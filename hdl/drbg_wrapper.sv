module ctr_drbg_wrapper #(
  parameter int KEY_BITS        = 128,
  parameter int SEED_BITS       = 256,
  parameter int RESEED_INTERVAL = 511   // blocks between reseeds
)(
  input  logic                 clk,
  input  logic                 rst_n,

  // --- Handshake to/from conditioner (no changes to conditioner) ---
  output logic                 drbg_ready_o, // -> conditioner.drbg_ready_i
  input  logic                 drbg_valid_i, // <- conditioner.drbg_valid_o
  input  logic [SEED_BITS-1:0] seed_i,       // <- conditioner.seed_o

  // --- Streaming output to buffer/consumer (ready/valid) ---
  output logic                 out_valid_o,
  input  logic                 out_ready_i,
  output logic [127:0]         out_data_o,

  // --- Status/telemetry (optional) ---
  output logic                 busy_o,        // high when not idle
  output logic [15:0]          blocks_since_reseed_o
);

  // DRBG Wires
  logic                instantiate_pulse;
  logic                reseed_pulse;
  logic                generate_pulse;
  logic [15:0]         num_blocks_1;
  logic [SEED_BITS-1:0] seed_material;
  logic                seed_valid_pulse;
  logic [SEED_BITS-1:0] additional_input_zero;

  logic                drbg_busy;
  logic                drbg_done;
  logic                drbg_rand_v;
  logic [127:0]        drbg_rand;

  assign num_blocks_1         = 16'd1;       // Stream one block at a time
  assign additional_input_zero = '0;

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

    .seed_material_i   (seed_material),
    .seed_valid_i      (seed_valid_pulse),

    .additional_input_i(additional_input_zero),

    .busy_o            (drbg_busy),
    .done_o            (drbg_done),          // pulses after each 1-block generate (post-update)
    .random_valid_o    (drbg_rand_v),        // pulses when the 128b block is ready
    .random_block_o    (drbg_rand)
  );

  // ---------------------------
  // Output buffer handshake
  // ---------------------------
  // Hold data when produced until consumer accepts it (ready/valid).
  logic        hold_valid;
  logic [127:0] hold_data;

  // Capture DRBG block when it arrives
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      hold_valid <= 1'b0;
      hold_data  <= '0;
    end else begin
      // Accept a new block from DRBG when it appears
      if (drbg_rand_v) begin
        hold_data  <= drbg_rand;
        hold_valid <= 1'b1;
      end

      // Downstream consumed the word
      if (hold_valid && out_ready_i) begin
        hold_valid <= 1'b0;
      end
    end
  end

  assign out_valid_o = hold_valid;
  assign out_data_o  = hold_data;

  // ---------------------------
  // Conditioner handshake + DRBG drive FSM
  // ---------------------------
  typedef enum logic [2:0] {
    W_IDLE,
    W_SEED_REQ,     // assert drbg_ready_o
    W_SEED_WAIT,    // wait for drbg_valid_i; latch seed
    W_INST_PULSE,   // pulse instantiate + seed_valid
    W_RUN,          // stream generates until backpressure or reseed interval hit
    W_RESEED_REQ,   // request new seed from conditioner
    W_RESEED_PULSE  // pulse reseed + seed_valid
  } wstate_t;

  wstate_t state, state_n;

  // Defaults
  always_comb begin
    // DRBG pulses default low
    instantiate_pulse = 1'b0;
    reseed_pulse      = 1'b0;
    generate_pulse    = 1'b0;
    seed_valid_pulse  = 1'b0;
    seed_material     = seed_latched;

    // Conditioner handshake default
    drbg_ready_o      = 1'b0;

    // Busy
    busy_o            = (state != W_IDLE);

    // Counter default
    blocks_since_reseed_n = blocks_since_reseed;

    state_n = state;

    unique case (state)
      W_IDLE: begin
        // Immediately seek a seed on power-up/reset
        state_n = W_SEED_REQ;
      end

      W_SEED_REQ: begin
        drbg_ready_o = 1'b1;     // tell conditioner we're ready for a seed
        state_n      = W_SEED_WAIT;
      end

      W_SEED_WAIT: begin
        drbg_ready_o = 1'b1;
        if (drbg_valid_i) begin
          // latch happens in sequential block below
          state_n = W_INST_PULSE;
        end
      end

      W_INST_PULSE: begin
        // Push seed into core and instantiate
        seed_material    = seed_latched;
        seed_valid_pulse = 1'b1;
        instantiate_pulse= 1'b1;
        // reset interval counter
        blocks_since_reseed_n = '0;
        // next: start running
        state_n          = W_RUN;
      end

      W_RUN: begin
        // If downstream can accept (either empty or will consume next),
        // and the core is idle (done_o just completed the last block),
        // issue another 1-block generate.
        // We also allow overlapping: as soon as DRBG isn't busy and we don't
        // have backpressure, kick the next block.
        if (!hold_valid || (hold_valid && out_ready_i)) begin
          // check reseed interval
          if (blocks_since_reseed >= RESEED_INTERVAL) begin
            state_n = W_RESEED_REQ;
          end else begin
            // core should be idle between 1-block generates; use done_o as guard
            // Issue a new generate only when core is not busy
            if (!drbg_busy) begin
              generate_pulse = 1'b1;
            end
          end
        end
        // blocks_since_reseed increment when a block is actually produced
        if (drbg_rand_v) begin
          blocks_since_reseed_n = blocks_since_reseed + 16'd1;
        end
      end

      W_RESEED_REQ: begin
        drbg_ready_o = 1'b1;
        state_n      = W_RESEED_PULSE; // wait one cycle if you want strict valid check, or:
        if (!drbg_valid_i) state_n = W_RESEED_REQ; // more conservative: wait for valid
      end

      W_RESEED_PULSE: begin
        if (drbg_valid_i) begin
          seed_valid_pulse = 1'b1;
          reseed_pulse     = 1'b1;
          blocks_since_reseed_n = '0;
          state_n          = W_RUN;   // resume streaming
        end else begin
          // stay until conditioner gives a seed
          drbg_ready_o     = 1'b1;
          state_n          = W_RESEED_PULSE;
        end
      end

      default: state_n = W_IDLE;
    endcase
  end

  // Sequential: latch seed & state/counters
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state               <= W_IDLE;
      seed_latched        <= '0;
      blocks_since_reseed <= '0;
    end else begin
      state               <= state_n;
      blocks_since_reseed <= blocks_since_reseed_n;

      // Latch new seed when conditioner asserts valid in the wait states
      if ((state == W_SEED_WAIT && drbg_valid_i) ||
          (state == W_RESEED_REQ && drbg_valid_i) ||
          (state == W_RESEED_PULSE && drbg_valid_i)) begin
        seed_latched <= seed_i;
      end
    end
  end

endmodule



// module ctr_drbg_wrapper #(
//     parameter int KEY_BITS        = 128,  // AES
//     parameter int DATA_WIDTH      = 256,  // Seed width from conditioner
//     parameter int RESEED_INTERVAL = 511   // simple reseed guard (count of generate calls)

// )(
//     input  logic                      clk,
//     input  logic                      rst_n,

//     // Handshake to/from conditioner
//     output logic                   drbg_ready_o, // -> conditioner.drbg_ready_i
//     input  logic                   drbg_valid_i, // <- conditioner.drbg_valid_o
//     input  logic [DATA_WIDTH-1:0]  seed_i,       // <- conditioner.seed_o (256-bit)

//     // DRBG signals from control
//     input  logic                   instantiate_i, // 1-cycle (IDLE only)
//     input  logic                   reseed_i,      // 1-cycle (IDLE only)
//     input  logic                   generate_i,    // 1-cycle (IDLE only)
//     input  logic [15:0]            num_blocks_i,  // # of 128b encrypt blocks to output


//     // DRBG status & data outputs
//     output logic                   random_valid_o,      //  per 128b block
//     output logic [KEY_BITS-1:0]    random_block_o       // capture on random_valid_o
    
// );

// // seed handoff to DRBG:
// logic [DATA_WIDTH-1:0] seed_latched;
// logic seed_valid_pulse;
// logic core_done;

// // FSM: request seed, capture seed, chuck @ DRBG
// typedef enum logic [1:0] {W_IDLE, W_WAIT_SEED, W_PULSE_DRBG} wstate_t;
// wstate_t wstate, wstate_n;

// // Seq Logic
// always_ff @(posedge clk or negedge rst_n) begin
//     if (!rst_n) begin
//         wstate           <= W_IDLE;
//         seed_latched     <= '0;
//         seed_valid_pulse <= 1'b0;
//     end else begin
//         wstate           <= wstate_n;
//         // goes into DRBG
//         seed_valid_pulse <= (wstate_n == W_PULSE_DRBG);

//         // Latch the 256b seed exactly when conditioner asserts valid
//         if (drbg_valid_i && (wstate == W_WAIT_SEED)) begin
//             seed_latched <= seed_i;
//         end
//     end
// end

// // Comb Logic
// always_comb begin
//     wstate_n      = wstate;
//     drbg_ready_o  = 1'b0;

//     unique case (wstate)
//         W_IDLE: begin
//             // @ instan or reseed request, ask conditioner for a seed
//             if (instantiate_i || reseed_i) begin
//                 drbg_ready_o = 1'b1;
//                 wstate_n     = W_WAIT_SEED;
//             end
//         end

//         W_WAIT_SEED: begin
//             // stays ready asserted until conditioner sends valid
//             drbg_ready_o = 1'b1;
//             if (drbg_valid_i) begin
//                 wstate_n = W_PULSE_DRBG;  // next cycle: strobe seed into DRBG core
//             end
//         end

//         W_PULSE_DRBG: begin
//             // seed_valid is generated, return to idle
//             wstate_n = W_IDLE;
//         end

//         default: wstate_n = W_IDLE;
//     endcase
// end


// // drbg core
// aes_ctr_drbg #(
//     .KEY_BITS        (KEY_BITS),
//     .BLOCK_BITS      (128),
//     .SEED_BITS       (DATA_WIDTH),
//     .RESEED_INTERVAL (RESEED_INTERVAL)
// ) u_drbg (
//     .clk               (clk),
//     .rst_n             (rst_n),

//     // command pulses & size
//     .instantiate_i     (instantiate_i),
//     .reseed_i          (reseed_i),
//     .generate_i        (generate_i),
//     .num_blocks_i      (num_blocks_i),

//     // seed from wrapper (latched + 1-cycle strobe)
//     .seed_material_i   (seed_latched),
//     .seed_valid_i      (seed_valid_pulse),

//     // optional additional input (post-generate update)
//     .additional_input_i('0),

//     // status & data
//     //.busy_o            (busy_o),
//     .done_o            (core_done),
//     .random_valid_o    (random_valid_o),
//     .random_block_o    (random_block_o)
// );

// // assign buffer_ready = core_done;

// endmodule