/*
 Module: aes_ctr_drbg.sv  (decoupled core)
 Type  : CTR_DRBG (AES-128), per NIST SP 800-90A Rev.1 §10.2.1
 
 Summary
  - Internal state: Key (128), V (128), reseed_counter
  - Instantiate/Reseed: wait for external 256-bit seed_material_i (from conditioner),
    then run CTR_DRBG_Update(Key, V, seed_material_i)
  - Generate: for i in N blocks: V←V+1; out_i = AES-ECB(Key, V)
    then run CTR_DRBG_Update(Key, V, additional_input_i) after the batch
 Top-level should wire:  OHT → aes_cbc_mac (or other) → seed_material_i/seed_valid_i → DRBG
 */

module aes_ctr_drbg #(
  parameter int KEY_BITS        = 128,
  parameter int BLOCK_BITS      = 128,
  parameter int SEED_BITS       = 256,  // seedlen for AES-128
  parameter int RESEED_INTERVAL = 511   // simple reseed guard (count of generate calls)
)(
  input  logic                      clk,
  input  logic                      rst_n,

  // Commands (assert exactly one for 1 cycle in IDLE)
  input  logic                      instantiate_i,
  input  logic                      reseed_i,
  input  logic                      generate_i,
  input  logic [15:0]               num_blocks_i,     // number of 128b blocks to output

  // Conditioner interface (external)
  input  logic [SEED_BITS-1:0]      seed_material_i,  // 256-bit from conditioner
  input  logic                      seed_valid_i,     // pulse when seed_material_i is valid

  // Optional additional input (mixed in after Generate)
  input  logic [SEED_BITS-1:0]      additional_input_i,

  // Outputs
//   output logic                      busy_o,
  output logic                      done_o,           // pulses when op completes
  output logic                      random_valid_o,   // pulses with each 128b random block
  output logic [BLOCK_BITS-1:0]     random_block_o
);

  // State machine
typedef enum logic [3:0] {
    S_IDLE,
    // Instantiate/Reseed via external seed_material
    S_WAIT_SEED,
    S_UPD1_REQ, S_UPD1_WAIT,
    S_UPD2_REQ, S_UPD2_WAIT,
    S_UPD_MIX,
    // Generate path
    S_GEN_REQ, S_GEN_WAIT, S_GEN_OUT,
    // Post-generate Update
    S_PG_UPD1_REQ, S_PG_UPD1_WAIT,
    S_PG_UPD2_REQ, S_PG_UPD2_WAIT,
    S_PG_UPD_MIX
} state_t;

state_t state, state_n;

// DRBG registers
logic [KEY_BITS-1:0]   K_reg, K_n;
logic [BLOCK_BITS-1:0] V_reg, V_n;
logic [31:0]           reseed_counter_reg, reseed_counter_n;

// Generate bookkeeping
logic [15:0]           blocks_left_reg, blocks_left_n;
logic                  op_gen_reg, op_gen_n;

// Provided data for Update step
logic [SEED_BITS-1:0]  provided_data_reg, provided_data_n;
logic [BLOCK_BITS-1:0] temp0_reg, temp0_n;
logic [BLOCK_BITS-1:0] temp1_reg, temp1_n;

// AES core wires
logic                  aes_in_valid;
logic [BLOCK_BITS-1:0] aes_in_block;
logic                  aes_out_valid;
logic [BLOCK_BITS-1:0] aes_out_block;

// Outputs (pulse helpers)
logic                  done_set, rnd_set;

// Reseed guard
logic                  at_reseed_limit;
assign at_reseed_limit = (reseed_counter_reg >= RESEED_INTERVAL);

// Submodule: AES-128 ECB encrypt block
aes_core u_aes_core (
    .clk              (clk),
    .rst_n            (rst_n),
    .data_in_valid_i  (aes_in_valid),
    .key_in_i         (K_reg),
    .data_in_i        (aes_in_block),
    .data_out_valid_o (aes_out_valid),
    .data_out_o       (aes_out_block)
);

// Help
function automatic [BLOCK_BITS-1:0] inc_block (input [BLOCK_BITS-1:0] x);
inc_block = x + {{(BLOCK_BITS-1){1'b0}}, 1'b1};
endfunction

// Sequential
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        state              <= S_IDLE;
        K_reg              <= '0;
        V_reg              <= '0;
        reseed_counter_reg <= '0;
        blocks_left_reg    <= '0;
        op_gen_reg         <= 1'b0;
        provided_data_reg  <= '0;
        temp0_reg          <= '0;
        temp1_reg          <= '0;
        random_block_o     <= '0;
        random_valid_o     <= 1'b0;
        done_o             <= 1'b0;
    end else begin
        state              <= state_n;
        K_reg              <= K_n;
        V_reg              <= V_n;
        reseed_counter_reg <= reseed_counter_n;
        blocks_left_reg    <= blocks_left_n;
        op_gen_reg         <= op_gen_n;
        provided_data_reg  <= provided_data_n;
        temp0_reg          <= temp0_n;
        temp1_reg          <= temp1_n;

        // Pulse outputs
        random_valid_o     <= rnd_set;
        if (rnd_set) random_block_o <= aes_out_block;
        done_o             <= done_set;
    end
end

always_comb begin
    // Defaults
    state_n             = state;
    K_n                 = K_reg;
    V_n                 = V_reg;
    reseed_counter_n    = reseed_counter_reg;
    blocks_left_n       = blocks_left_reg;
    op_gen_n            = op_gen_reg;
    provided_data_n     = provided_data_reg;
    temp0_n             = temp0_reg;
    temp1_n             = temp1_reg;

    // busy_o              = (state != S_IDLE);

    // AES defaults
    aes_in_valid        = 1'b0;
    aes_in_block        = '0;

    // Output pulses
    done_set            = 1'b0;
    rnd_set             = 1'b0;

    unique case (state)
      // IDLE
        S_IDLE: begin
            if (instantiate_i || reseed_i) begin
                // Wait for external seed (seed_valid_i pulse)
                provided_data_n = '0;
                op_gen_n        = 1'b0;
                state_n         = S_WAIT_SEED;
            end else if (generate_i) begin
                if (!at_reseed_limit && num_blocks_i != 16'd0) begin
                    blocks_left_n = num_blocks_i;
                    op_gen_n      = 1'b1;
                    state_n       = S_GEN_REQ;
                end else begin
                    // ignore generate if reseed required or zero length
                    done_set      = 1'b1;
                    state_n       = S_IDLE;
                end
            end
        end

        // Instantiate/Reseed: wait for conditioner seed, then Update
        S_WAIT_SEED: begin
            if (seed_valid_i) begin
                provided_data_n = seed_material_i; // 256-bit seed_material
                state_n         = S_UPD1_REQ;
            end
        end

        // Update: temp0 = AES_K(V+1), temp1 = AES_K(V+2), mix with provided_data
        S_UPD1_REQ: begin
            aes_in_block = inc_block(V_reg);
            V_n          = aes_in_block;
            aes_in_valid = 1'b1;
            state_n      = S_UPD1_WAIT;
        end
        S_UPD1_WAIT: begin
            if (aes_out_valid) begin
                temp0_n = aes_out_block;
                state_n = S_UPD2_REQ;
            end
        end
        S_UPD2_REQ: begin
            aes_in_block = inc_block(V_reg);
            V_n          = aes_in_block;
            aes_in_valid = 1'b1;
            state_n      = S_UPD2_WAIT;
        end
        S_UPD2_WAIT: begin
            if (aes_out_valid) begin
            temp1_n = aes_out_block;
            state_n = S_UPD_MIX;
            end
        end
        S_UPD_MIX: begin
            // temp = leftmost( temp0||temp1 , seedlen ) XOR provided_data
            logic [SEED_BITS-1:0] temp_cat;
            temp_cat = {temp0_reg, temp1_reg} ^ provided_data_reg;
            // Key = leftmost(temp, keylen); V = rightmost(temp, blocklen)
            K_n      = temp_cat[SEED_BITS-1 -: KEY_BITS];
            V_n      = temp_cat[BLOCK_BITS-1:0];
            reseed_counter_n = 32'd1;
            done_set = 1'b1;
            state_n  = S_IDLE;
        end

        // Generate N blocks: V←V+1; out = AES_K(V)
        S_GEN_REQ: begin
            if (blocks_left_reg != 16'd0) begin
                aes_in_block = inc_block(V_reg);
                V_n          = aes_in_block;
                aes_in_valid = 1'b1;
                state_n      = S_GEN_WAIT;
            end else begin
                // no more blocks -> post-generate Update
                provided_data_n = additional_input_i;
                state_n         = S_PG_UPD1_REQ;
            end
        end
        S_GEN_WAIT: begin
            if (aes_out_valid) begin
                rnd_set        = 1'b1;                     // present random block
                blocks_left_n  = blocks_left_reg - 16'd1;
                state_n        = S_GEN_OUT;
            end
        end
        S_GEN_OUT: begin
            if (blocks_left_n != 16'd0) begin
                state_n = S_GEN_REQ;
            end else begin
                provided_data_n = additional_input_i;      // may be zeros
                state_n         = S_PG_UPD1_REQ;
            end
        end

        // Post-generate Update(Key,V, additional_input)
        S_PG_UPD1_REQ: begin
            aes_in_block = inc_block(V_reg);
            V_n          = aes_in_block;
            aes_in_valid = 1'b1;
            state_n      = S_PG_UPD1_WAIT;
        end
        S_PG_UPD1_WAIT: begin
            if (aes_out_valid) begin
                temp0_n = aes_out_block;
                state_n = S_PG_UPD2_REQ;
            end
        end
        S_PG_UPD2_REQ: begin
            aes_in_block = inc_block(V_reg);
            V_n          = aes_in_block;
            aes_in_valid = 1'b1;
            state_n      = S_PG_UPD2_WAIT;
        end
        S_PG_UPD2_WAIT: begin
            if (aes_out_valid) begin
            temp1_n = aes_out_block;
            state_n = S_PG_UPD_MIX;
            end
        end
        S_PG_UPD_MIX: begin
            logic [SEED_BITS-1:0] temp_cat;
            temp_cat      = {temp0_reg, temp1_reg} ^ provided_data_reg;
            K_n           = temp_cat[SEED_BITS-1 -: KEY_BITS];
            V_n           = temp_cat[BLOCK_BITS-1:0];
            reseed_counter_n = reseed_counter_reg + 32'd1;
            done_set      = 1'b1;
            op_gen_n      = 1'b0;
            state_n       = S_IDLE;
        end

        default: state_n = S_IDLE;
    endcase
end

endmodule