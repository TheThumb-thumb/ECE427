`timescale 1ns/1ps
import le_types::*;
import params::*;
module drbg_wrapper_tb;

  // Clock / Reset
  logic clk, rst_n;
  localparam int CLK_PS = 10_000; // 100 MHz
  initial begin
    clk = 0;
    forever #(CLK_PS/2) clk = ~clk;
  end

  initial begin
    rst_n = 0;
    repeat (5) @(posedge clk);
    rst_n = 1;
  end

  // Conditioner 
  logic                 drbg_ready_o;     // from me -> conditioner
  logic                 drbg_valid_i;     // from conditioner -> me
  logic [255:0]         seed_i;           // conditoner to me

  // to buffer
  logic                 out_valid_o;
  logic                 out_ready_i;
  logic [127:0]         out_data_o;

  // Status
  logic                 busy_o;
  logic [15:0]          blocks_since_reseed_o;

  localparam int RESEED_INTERVAL_TB = 20;

  ctr_drbg_wrapper #(
    .KEY_BITS         (128),
    .SEED_BITS        (256),
    .RESEED_INTERVAL  (RESEED_INTERVAL_TB)
  ) dut (
    .clk                     (clk),
    .rst_n                   (rst_n),

    // conditioner handshake
    .drbg_ready_o            (drbg_ready_o),
    .drbg_valid_i            (drbg_valid_i),
    .seed_i                  (seed_i),

    // streaming out
    .out_valid_o             (out_valid_o),
    .out_ready_i             (out_ready_i),
    .out_data_o              (out_data_o),

    // status
    .busy_o                  (busy_o),
    .blocks_since_reseed_o   (blocks_since_reseed_o)
  );

  // Conditioner model
  // When the wrapper asserts drbg_ready_o, we respond after 2 cycles
  // with drbg_valid_i=1 for one cycle and present a seed on seed_i.
  //
  // We supply SEED0 at first instantiate, then SEED1 on next reseed request.
  typedef enum logic [1:0] {C_IDLE, C_WAIT_RDY, C_RESPOND} cstate_t;
  cstate_t cstate;

  logic [255:0] SEED0 = 256'h00010203_04050607_08090A0B_0C0D0E0F__10111213_14151617_18191A1B_1C1D1E1F;
  logic [255:0] SEED1 = 256'hA5A5A5A5_A5A5A5A5_5A5A5A5A_5A5A5A5A__01234567_89ABCDEF_FEDCBA98_76543210;
  int           seed_phase = 0; 

  // default
  initial begin
    drbg_valid_i = 1'b0;
    seed_i       = '0;
    cstate       = C_IDLE;
  end

  // simple responder
  task automatic send_seed(input logic [255:0] s);
    begin
      // two-cycle latency to mimic conditioner work
      @(posedge clk); @(posedge clk);
      seed_i       = s;
      drbg_valid_i = 1'b1;  // one-cycle valid
      @(posedge clk);
      drbg_valid_i = 1'b0;
    end
  endtask

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      cstate     <= C_IDLE;
      seed_phase <= 0;
    end else begin
      case (cstate)
        C_IDLE: begin
          // Wait until the wrapper asks for a seed at boot
          if (drbg_ready_o) cstate <= C_WAIT_RDY;
        end
        C_WAIT_RDY: begin
          // Keep watching ready; when asserted, deliver the next seed
          if (drbg_ready_o) begin
            cstate <= C_RESPOND;
            case (seed_phase % 2)
              0: fork send_seed(SEED0); join_none
              1: fork send_seed(SEED1); join_none
            endcase
            seed_phase <= seed_phase + 1;
          end else begin
            cstate <= C_IDLE;
          end
        end
        C_RESPOND: begin
          // After responding, go idle; wrapper will re-assert ready
          // when RESEED_INTERVAL blocks have been produced.
          if (!drbg_ready_o) cstate <= C_IDLE;
        end
        default: cstate <= C_IDLE;
      endcase
    end
  end

  // Simple pattern: 3 cycles ready, 1 cycle not ready.
  // Counts blocks and logs them to a file.
  int unsigned took_blocks = 0;
  int          fh;

  initial begin
    out_ready_i = 1'b0;
    fh = $fopen("wrapper_blocks.txt", "w");
    if (!fh) $error("Failed to open wrapper_blocks.txt");
    // start giving ready after reset settles
    @(posedge rst_n);
    repeat (5) @(posedge clk);
    forever begin
      out_ready_i = 1'b1; repeat (3) @(posedge clk);
      out_ready_i = 1'b0; repeat (1) @(posedge clk);
    end
  end

  always_ff @(posedge clk) begin
    if (out_valid_o && out_ready_i) begin
      took_blocks++;
      $display("%0t WRAP OUT[%0d] = %032h  (since_reseed=%0d)",
               $time, took_blocks, out_data_o, blocks_since_reseed_o);
      if (fh) $fdisplay(fh, "%032h", out_data_o);
    end
  end

  // Stop after N blocks so the run is finite and we see at least
  // one reseed (RESEED_INTERVAL_TB=16).
  localparam int MAX_BLOCKS = 48;

  // Watch that blocks_since_reseed_o resets to 0 shortly after a reseed.
  logic [15:0] last_bsr;
  always_ff @(posedge clk) last_bsr <= blocks_since_reseed_o;

  // A crude assertion: when the counter drops (reseed), it should drop to 0.
  always_ff @(posedge clk) begin
    if (rst_n && (blocks_since_reseed_o < last_bsr) && (blocks_since_reseed_o != 0)) begin
      $error("blocks_since_reseed_o dropped but not to 0 (value=%0d)", blocks_since_reseed_o);
    end
  end

  // Timeout (just in case)
  initial begin
    time start = 0;
    @(posedge rst_n); start = $time;
    forever begin
      @(posedge clk);
      if ($time - start > 5_000_000_000) begin // 5 ms at 100 MHz
        $error("Timeout. took_blocks=%0d busy=%0b", took_blocks, busy_o);
        $finish;
      end
      if (took_blocks >= MAX_BLOCKS) begin
        $display("[TB] Collected %0d blocks. Finishing.", took_blocks);
        $finish;
      end
    end
  end

  // FSDB for waves (optional)
  initial begin
    $fsdbDumpfile("ctr_drbg_wrapper_tb.fsdb");
    $fsdbDumpvars(0, "+all");
  end

endmodule


// add near state regs
logic [1:0] seed_stretch_cnt;

// W_INST_PULSE (similar change for W_RESEED_PULSE)
W_INST_PULSE: begin
  seed_material     = seed_latched;
  seed_valid_pulse  = 1'b1;        // keep high while in this state
  if (seed_stretch_cnt == 2'd0)    // first cycle only
    instantiate_pulse = 1'b1;

  if (seed_stretch_cnt == 2'd1) begin
    blocks_since_reseed_n = '0;
    state_n = W_RUN;
  end
end

// sequential
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) seed_stretch_cnt <= '0;
  else case (state)
    W_INST_PULSE:   seed_stretch_cnt <= seed_stretch_cnt + 2'd1;
    default:        seed_stretch_cnt <= '0;
  endcase
end

logic drbg_busy_q;
always_ff @(posedge clk or negedge rst_n)
  if (!rst_n) drbg_busy_q <= 1'b1; else drbg_busy_q <= drbg_busy;

wire core_just_idle = drbg_busy_q & ~drbg_busy;

W_RUN: begin
  if ((!hold_valid) || (hold_valid && out_ready_i)) begin
    if (blocks_since_reseed >= RESEED_INTERVAL)
      state_n = W_RESEED_REQ;
    else if (core_just_idle)
      generate_pulse = 1'b1;  // one-cycle
  end
  if (drbg_rand_v) blocks_since_reseed_n = blocks_since_reseed + 16'd1;
end
