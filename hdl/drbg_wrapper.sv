module ctr_drbg_wrapper #(
  parameter int KEY_BITS        = 128,
  parameter int SEED_BITS       = 256,
  parameter int RESEED_INTERVAL = 511   // blocks between reseeds
)(
  input  logic                 clk,
  input  logic                 rst_n,

  // Handshake to/from conditioner
  output logic                 drbg_ready_o, // -> conditioner.drbg_ready_i
  input  logic                 drbg_valid_i, // <- conditioner.drbg_valid_o
  input  logic [SEED_BITS-1:0] seed_i,       // <- conditioner.seed_o

  // debug serial seed load
    input  logic                 drbg_debug_mode_i,       // 1 = use debug loader
    input  logic                 drbg_serial_i,

  // Streaming output to buffer/consumer ready/valid
  output logic                 out_valid_o,
  input  logic                 out_ready_i,
  output logic [127:0]         out_data_o,

  // Status/telemetry
  output logic                 busy_o,        // high when not idle
  output logic [15:0]          blocks_since_reseed_o // remove blocks since reseed 
);

// DRBG Wires
logic                instantiate_pulse;
logic                reseed_pulse;
logic                generate_pulse;
logic [15:0]         num_blocks_1;
logic [SEED_BITS-1:0] seed_material;
logic                seed_valid_pulse;
logic [SEED_BITS-1:0] additional_input_zero;

logic out_ready_int;

logic                drbg_busy;
logic                drbg_done;
logic                drbg_rand_v;
logic [127:0]        drbg_rand;


logic [1:0]           seed_stretch;              
logic                 seed_stretch_ld_inst;      
logic                 seed_stretch_ld_reseed;    
logic                 inst_fired;                
logic                 reseed_fired;              

assign num_blocks_1         = 16'd1;       // Stream one block at a time
assign additional_input_zero = '0;

assign out_ready_int = drbg_debug_mode_i ? 1'b1: out_ready_i; 

// Seed latch (capture from conditioner once per (re)seed)
logic [SEED_BITS-1:0] seed_latched;

// Reseed interval counter
logic [15:0] blocks_since_reseed, blocks_since_reseed_n;
assign blocks_since_reseed_o = blocks_since_reseed;

// DRBG core
aes_ctr_drbg #(
    .KEY_BITS       (KEY_BITS),
    .BLOCK_BITS     (128),
    .SEED_BITS      (SEED_BITS),
    .RESEED_INTERVAL(RESEED_INTERVAL) // core may also enforce/track; we track here too
) u_drbg (
    .clk               (clk),
    .rst_n             (rst_n),

    .instantiate_i     (instantiate_pulse),
    .reseed_i          (reseed_pulse),
    .generate_i        (generate_pulse),
    .num_blocks_i      (num_blocks_1),

    .seed_material_i   (seed_latched),    // when cond doesnt assert xxxxx
    // .seed_material_i   ('0),  // check if drbg spits

    .seed_valid_i      (seed_valid_pulse),

    .additional_input_i(additional_input_zero),

    .busy_o            (drbg_busy),
    .done_o            (drbg_done),          // pulses after each 1 block generate (post-update)
    .random_valid_o    (drbg_rand_v),        // pulses when the 128b block is ready
    .random_block_o    (drbg_rand)
);

// Output buffer handshake
// Hold data when produced until buff accepts it (ready/valid).
logic        hold_valid;
logic [127:0] hold_data;

// Capture DRBG block when it arrives
always_ff @(posedge clk) begin
    if (!rst_n) begin
        hold_valid <= 1'b0;
        hold_data  <= '0;
    end else begin
        // Accept a new block from DRBG when it appears
        if (drbg_rand_v) begin
            hold_data  <= drbg_rand;
            hold_valid <= 1'b1;
        end

        // Downstream took the word
        if (hold_valid && out_ready_int) begin
            hold_valid <= 1'b0;
        end
    end
end

assign out_valid_o = hold_valid;
assign out_data_o  = hold_data;

// Conditioner handshake + DRBG drive FSM
typedef enum logic [3:0] {
    W_IDLE,
    W_SEED_REQ,     // assert drbg_ready_o
    W_SEED_WAIT,    // wait for drbg_valid_i; latch seed
    W_INST_PULSE,   // pulse instantiate + seed_valid
    W_WAIT_INIT,
    W_RUN,          // stream generates until backpressure or reseed interval hit
    W_RESEED_REQ,   // request new seed from conditioner
    W_RESEED_PULSE,  // pulse reseed + seed_valid
    W_WAIT_RESEED
} wstate_t;

wstate_t state, state_n;

// Simple debug shift register for 256-bit seed
logic [SEED_BITS-1:0] dbg_shift_reg;
logic [$clog2(SEED_BITS+1)-1:0 ] dbg_bit_cnt;
logic dbg_seed_ready;
logic dbg_flag;

always_ff @(posedge clk) begin
  if (!rst_n) begin
    dbg_shift_reg  <= '0;
    dbg_bit_cnt    <= '0;
    dbg_seed_ready <= 1'b0;
    dbg_flag <= '0;
  end else begin
    // default: clear "ready" unless we just finished loading
    dbg_seed_ready <= 1'b0;

    if (drbg_debug_mode_i) begin
      // Shift in LSB from serial line; choose MSB/LSB convention as you like
      dbg_shift_reg <= {dbg_shift_reg[SEED_BITS-2:0], drbg_serial_i};

      if (signed'(dbg_bit_cnt) == signed'(SEED_BITS-1)) begin
        dbg_bit_cnt    <= '0;
        dbg_seed_ready <= 1'b1;  // we now have a full 256-bit seed
        dbg_flag <= 1'b1;
      end else if (!dbg_flag)begin
        dbg_bit_cnt <= dbg_bit_cnt + 1'b1;
      end
    end else begin
      // Not in debug mode: reset counter and keep "not ready"
      dbg_bit_cnt    <= '0;
      dbg_seed_ready <= 1'b0;
    end
  end
end



// Defaults
always_comb begin
    // DRBG pulses default low
    instantiate_pulse = 1'b0;
    reseed_pulse      = 1'b0;
    generate_pulse    = 1'b0;
    seed_valid_pulse  = 1'b0;
    // seed_material     = seed_latched;

    seed_stretch_ld_inst   = 1'b0;
    seed_stretch_ld_reseed = 1'b0;

    // Conditioner handshake default
    drbg_ready_o      = 1'b0;

    // Busy
    busy_o            = (state != W_IDLE);

    // Counter default
    blocks_since_reseed_n = blocks_since_reseed;

    // mux seed in wrapper:
    // // Normal vs debug routing
    // valid_int = dbg_mode_i ? dbg_seed_valid_i : drbg_valid_i;
    // seed_int  = dbg_mode_i ? dbg_seed_i       : seed_i;

    // // In debug mode, do NOT request seeds from conditioner
    // drbg_ready_o = dbg_mode_i ? 1'b0 : ready_int;


    // state machine
    state_n = state;

    unique case (state)
        W_IDLE: begin
            // Immediately seek a seed on power-up/reset
            state_n = W_SEED_REQ;
        end

        W_SEED_REQ: begin
        if (!drbg_debug_mode_i) begin
            drbg_ready_o = 1'b1;       // only handshake with conditioner in normal mode
        end
        state_n = W_SEED_WAIT;
        end

        W_SEED_WAIT: begin
          if (!drbg_debug_mode_i) begin
              drbg_ready_o = 1'b1;
              if (drbg_valid_i) begin
              seed_stretch_ld_inst = 1'b1;
              state_n              = W_INST_PULSE;
              end
          end else begin
              // DEBUG MODE: no handshake; wait for 256 bits to load
              if (dbg_seed_ready) begin
              seed_stretch_ld_inst = 1'b1;
              state_n              = W_INST_PULSE;
              end
          end
        end

        W_INST_PULSE: begin
            // Stretch seed_valid while seed_stretch != 0
            // seed_material    = seed_latched;
            seed_valid_pulse = 1'b1;

            // 1c instantiate pulse (gated by inst_fired)
            if (!inst_fired) instantiate_pulse = 1'b1; 

            // When stretch is done, move on
            if (seed_stretch == 0) begin
                blocks_since_reseed_n = '0;
                state_n = W_WAIT_INIT;
            end
        end

        W_WAIT_INIT: begin
            if(drbg_done)begin
                state_n = W_RUN;
            end
        end

        W_RUN: begin
            // If downstream can accept (either empty or will consume next),
            if (!out_valid_o || (out_valid_o && out_ready_int)) begin
              if (dbg_seed_ready && drbg_debug_mode_i) begin
                state_n = W_RESEED_REQ;
              end else if (blocks_since_reseed >= RESEED_INTERVAL) begin
                  state_n = W_RESEED_REQ;   // go to reseed path, not fresh instantiate
                  // do NOT reset blocks_since_reseed here; wait until reseed completes
              end else if (!drbg_busy) begin
                  generate_pulse = 1'b1;
              end
            end
            // blocks_since_reseed go incr a block is actually produced
            if (drbg_rand_v) begin
                blocks_since_reseed_n = blocks_since_reseed + 16'd1;
            end
        end

        W_RESEED_REQ: begin
            if (!drbg_debug_mode_i) begin
                drbg_ready_o = 1'b1;
                if (drbg_valid_i) begin
                seed_stretch_ld_reseed = 1'b1;
                state_n                = W_RESEED_PULSE;
                end
            end else begin
                // DEBUG MODE: re-use debug stream to load a new seed
           
                seed_stretch_ld_reseed = 1'b1;
                state_n                = W_RESEED_PULSE;
            
            end
        end


        W_RESEED_PULSE: begin
          seed_valid_pulse = 1'b1;
          if (!reseed_fired)
            reseed_pulse = 1'b1;

          if (seed_stretch == 0) begin
            blocks_since_reseed_n = '0;
            state_n = W_WAIT_RESEED;
          end
        end


        // W_WAIT_RESEED: begin
        //   if (drbg_done)
        //     state_n = W_RUN;
        // end


        W_WAIT_RESEED: begin
          if (!drbg_debug_mode_i)begin
            if (drbg_done)begin
              state_n = W_RUN;
            end
          end
          else begin
            state_n = W_RUN;
          end
        end



        default: state_n = W_IDLE;
    endcase
end
logic drbg_valid_q;  // 1-cycle delayed copy of drbg_valid_i


always_ff @(posedge clk) begin
  if (!rst_n) begin
    seed_material <= '0;
  end else begin
    if (state == W_INST_PULSE || state == W_RESEED_PULSE)
      seed_material <= seed_latched;
    else if (drbg_done)
      seed_material <= '0;
  end
end



always_ff @(posedge clk) begin
  if (!rst_n) begin
    state               <= W_IDLE;
    seed_latched        <= '0;
    blocks_since_reseed <= '0;
    seed_stretch        <= '0;
    inst_fired          <= 1'b0;
    reseed_fired        <= 1'b0;
  end else begin
    state               <= state_n;
    blocks_since_reseed <= blocks_since_reseed_n;

    // >>> Latch on raw VALID (no state gating) <<<
    // if (valid_int)
    if (!drbg_debug_mode_i)begin
        if (drbg_valid_i)
            seed_latched <= seed_i;
    end else begin
        if (dbg_seed_ready)
            seed_latched <= dbg_shift_reg;
    end
    // Stretch counter
    if (seed_stretch_ld_inst)
      seed_stretch <= 2;
    else if (seed_stretch_ld_reseed)
      seed_stretch <= 2;
    else if ((state == W_INST_PULSE || state == W_RESEED_PULSE) && seed_stretch != 0)
      seed_stretch <= seed_stretch - 2'd1;

    // One-cycle pulse guards
    if (state == W_INST_PULSE && !inst_fired)  inst_fired  <= 1'b1;
    else if (state != W_INST_PULSE)            inst_fired  <= 1'b0;

    if (state == W_RESEED_PULSE && !reseed_fired) reseed_fired <= 1'b1;
    else if (state != W_RESEED_PULSE)             reseed_fired <= 1'b0;
  end
end


endmodule
