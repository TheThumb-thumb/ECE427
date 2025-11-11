// debug shift reg
module drbg_debug_loader #(
  parameter int SEED_BITS = 256
)(
  input  logic              clk,
  input  logic              rst_n,

  // Enable serial loading
  input  logic              debug_mode_i,   // 1 = use this path
  input  logic              serial_in_i,    // from FPGA pin / TB
  input  logic              load_start_i,   // 1-cycle pulse: start capturing 256 bits

  // “Ready for a fresh seed” from wrapper (optional but nice)
  input  logic              drbg_ready_i,   // wrapper says it wants a seed

  // Outputs to DRBG wrapper
  output logic [SEED_BITS-1:0] seed_o,
  output logic                 seed_valid_o  // held high for 2 cycles
);

  typedef enum logic [1:0] { D_IDLE, D_SHIFT, D_WAIT_READY } dstate_t;
  dstate_t          dstate, dstate_n;

  logic [SEED_BITS-1:0] shift_reg;
  logic [7:0]           bit_cnt;       // 0..255
  logic                 valid_hold;    // to stretch seed_valid_o

  always_comb begin
    dstate_n = dstate;

    case (dstate)
      D_IDLE: begin
        if (debug_mode_i && load_start_i) begin
          dstate_n = D_SHIFT;
        end
      end

      D_SHIFT: begin
        if (bit_cnt == SEED_BITS-1) begin
          // captured full 256 bits; wait until wrapper is ready
          dstate_n = D_WAIT_READY;
        end
      end

      D_WAIT_READY: begin
        if (drbg_ready_i) begin
          // once wrapper shows “ready”, we’ll assert valid for 2 cycles
          dstate_n = D_IDLE;
        end
      end

      default: dstate_n = D_IDLE;
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      dstate      <= D_IDLE;
      shift_reg   <= '0;
      bit_cnt     <= '0;
      valid_hold  <= 1'b0;
      seed_o      <= '0;
      seed_valid_o<= 1'b0;
    end else begin
      dstate <= dstate_n;

      case (dstate)
        D_IDLE: begin
          seed_valid_o <= 1'b0;
          valid_hold   <= 1'b0;
          bit_cnt      <= '0;

          if (debug_mode_i && load_start_i) begin
            // first bit
            shift_reg <= { shift_reg[SEED_BITS-2:0], serial_in_i };
            bit_cnt   <= bit_cnt + 8'd1;
          end
        end

        D_SHIFT: begin
          // shift in one bit per clock
          shift_reg <= { shift_reg[SEED_BITS-2:0], serial_in_i };
          bit_cnt   <= bit_cnt + 8'd1;

          // when finished, capture final value as seed_o
          if (bit_cnt == SEED_BITS-1) begin
            seed_o <= { shift_reg[SEED_BITS-2:0], serial_in_i };
          end
        end

        D_WAIT_READY: begin
          // we now have a full 256b seed in seed_o
          if (drbg_ready_i && !valid_hold) begin
            seed_valid_o <= 1'b1;    // first valid cycle
            valid_hold   <= 1'b1;
          end else if (valid_hold) begin
            // second valid cycle, then drop
            seed_valid_o <= 1'b0;
            valid_hold   <= 1'b0;
          end
        end
      endcase
    end
  end

endmodule


// // hook into top
//   // Wires
//   logic [255:0] dbg_seed;
//   logic         dbg_seed_valid;

//   drbg_debug_loader #(
//     .SEED_BITS(256)
//   ) u_dbg_loader (
//     .clk          (clk),
//     .rst_n        (rst_n),

//     .debug_mode_i (debug),           // or from control.sv/debug_register
//     .serial_in_i  (serial_input),    // from FPGA
//     .load_start_i (dbg_load_start),  // pulse from control.sv or debug button

//     .drbg_ready_i (cond_drbg_ready), // same ready the conditioner sees

//     .seed_o       (dbg_seed),
//     .seed_valid_o (dbg_seed_valid)
//   );


// // hook into wrapper:
//   ctr_drbg_wrapper #(
//     .KEY_BITS        (128),
//     .SEED_BITS       (256),
//     .RESEED_INTERVAL (511)   // or 15 if you like for testing
//   ) u_drbg_wrap (
//     .clk          (clk),
//     .rst_n        (rst_n),

//     // normal conditioner handshake
//     .drbg_ready_o (cond_drbg_ready),
//     .drbg_valid_i (cond_drbg_valid),
//     .seed_i       (seed),

//     // streaming to output buffer
//     .out_valid_o  (drbg_random_valid),
//     .out_ready_i  (drbg_output_ready),
//     .out_data_o   (drbg_random_block),

//     .busy_o       (), // or hook if you use it
//     .blocks_since_reseed_o(),

//     // *** new debug connections ***
//     .dbg_mode_i       (debug),         // same debug signal used by conditioner
//     .dbg_seed_i       (dbg_seed),
//     .dbg_seed_valid_i (dbg_seed_valid)
//   );



// // Now, when debug=0, everything is exactly as before (conditioner normal).
// // When debug=1 and you drive dbg_load_start + serial_input, the DRBG will 
// // seed from your custom serial data instead.