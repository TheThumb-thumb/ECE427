/*
Module: aes_ctr_drbg.sv

Purpose:  
    - CTR_DRBG(AES-128),  per NIST SP 800-90A 
    - State: K (128), V (128), reseed_counter
    - Instantiate/Reseed: seed_material (256) from DF -> Update(K,V, seed_material)
    - Generate: For i in N: V=V+1; out_i = E_K(V) 
        + Then Update(K,V, additional_input)

Interfaxes:
    - instantiate_i, reseed_i, generate_i are 1 cycle requests
    - done_o pulses high for one cycle when the requested op completes
    - random_valid_o pulses w/ each 128b random_block_o during generate


In Progress: 
    - for now this keeps the simplified DF (aes_df) by default, but can swap later 
      for aes_df 90A fully compliant w/ out changing this module
    - finish the rest of the combinational logic
*/


module aes_ctr_drbg #(
    parameter int DATA_WIDTH = 256,
    parameter int KEY_BITS = 128,
    // opt reseed window limit, generate is ignored until reseed if goes past this amount
    parameter int MAX_BTW_RESEEDS = 511 
)(
    input  logic         clk,
    input  logic         rst_n,

    // commands, assert only one of these for 1 cycle when IDLE
    input  logic         instantiate_i,
    input  logic         reseed_i,
    input  logic         generate_i,
    input  logic [15:0]  num_blocks_i,                // blocks to generate, 128b each


    // inputs for instantiate, reseed, & update after generate
    input  logic [DATA_WIDTH-1:0] entropy_i,
    input  logic [DATA_WIDTH-1:0] nonce_i,
    input  logic [DATA_WIDTH-1:0] personalization_i,
    input  logic [DATA_WIDTH-1:0] additional_input_i,          // optional, used in update after generate 

    input  logic [KEY_BITS-1:0] k_df_i,                      // can be 128 0' for simplicity

    // outputs
    output  logic         busy_o,
    output  logic         done_o,                      // pulses when op complete
    output  logic         random_valid_o,
    output  logic [KEY_BITS-1:0] random_block_o,                     

);

// states
typedef enum logic [3:0] {
    S_IDLE,
    // instantiate/reseed path via df
    S_DF_START, S_DF_WAIT, S_UPDATE_INIT_START1, S_UPDATE_INIT_WAIT1,
    S_UPDATE_INIT_START2, S_UPDATE_INIT_WAIT2, S_UPDATE_INIT_MIX,
    // gen path
    S_GEN_REQ, S_GEN_WAIT, S_GEN_OUT,
    S_UPDATE_AFTER_START1, S_UPDATE_AFTER_WAIT1,
    S_UPDATE_AFTER_START2, S_UPDATE_AFTER_WAIT2, S_UPDATE_AFTER_MIX
} state_t;

state_t state, state_n;

// DRBG registers
logic [KEY_BITS-1:0] K_reg, K_n;
logic [KEY_BITS-1:0]        V_reg, V_n;
logic [31:0]         reseed_counter_reg, reseed_counter_n;

// flags/ctrs
logic [15:0] blocks_left_reg, blocks_left_n;

logic op_is_instantiate_reg, op_is_instantiate_n;
logic op_is_reseed_reg, op_is_reseed_n;
logic op_is_generate_reg, op_is_generate_n;

// data for update
logic [DATA_WIDTH-1:0] provided_data_reg, provided_data_n;
logic [KEY_BITS-1:0] temp0_reg, temp0_n, temp1_reg, temp1_n;

// AES core wires?
logic [KEY_BITS-1:0] aes_in_block;
logic aes_in_valid, aes_out_block, aes_out_valid;

// deriv fucntion wires
logic [DATA_WIDTH-1:0] df_seed_material
logic df_start, df_done;

// reseed window
logic at_reseed_limit;

// output pulse help
logic done_set;
logic rnd_valid_set;

// submodule
// aes core
aes_core u_aes_core (
    .clk              (clk),
    .rst_n            (rst_n),
    .data_in_valid_i  (aes_in_valid),
    .key_in_i         (K_reg),
    .data_in_i        (aes_in_block),
    .data_out_valid_o (aes_out_valid),
    .data_out_o       (aes_out_block)
);
// deric function
aes_df u_df(
    .clk              (clk),
    .rst_n            (rst_n),
    .start_i(df_start),
    .entropy_i(entropy_i),
    .nonce_i(nonce_i),
    .personalization_i(),
    .k_df_i(),
    .done_o(),
    .seed_material_o()
);

// others(mainly helpers)
// thinking of using auto function for making big Indian incr for 128b vector
function automatic [KEY_BITS-1:0] inc128 (input [KEY_BITS-1:0] X);
    inc128 = x + 128'd1;
endfunction

// seq:
always_ff @(posedge clk) begin
    
    if(!rst_n)begin
        state                 <= S_IDLE;
        K_reg                 <= '0;
        V_reg                 <= '0;
        reseed_counter_reg    <= '0;
        blocks_left_reg       <= '0;
        op_is_instantiate_reg <= 1'b0;
        op_is_reseed_reg      <= 1'b0;
        op_is_generate_reg    <= 1'b0;
        provided_data_reg     <= '0;
        temp0_reg             <= '0;
        temp1_reg             <= '0;
        random_block_o        <= '0;
        random_valid_o        <= 1'b0;
        done_o                <= 1'b0;
    end
    
    else begin
        state <= state_n;
        K_reg <= K_n;
        V_reg <= V_n;
        reseed_counter_reg <= reseed_counter_n;
        blocks_left_reg <= blocks_left_n;
        op_is_instantiate_reg <= op_is_instantiate_n;
        op_is_reseed_reg <= op_is_reseed_n;
        op_is_generate_reg <= op_is_generate_n;
        provided_data_reg <= provided_data_n;
        temp0_reg <= temp0_n;
        temp1_reg <= temp1_n;

        //outputting pulses (registered)
        done_o <= done_set;
        random_valid_o <= rnd_valid_set;

        if (rnd_valid_set) random_block_o <= aes_out_block;
    end
end

// comb: 
always_comb begin
    // defaults
    state_n = state;
    K_n = K_reg;
    V_n = V_reg;
    reseed_counter_n = reseed_counter_reg;
    blocks_left_n = blocks_left_reg;
    op_is_instantiate_n = op_is_instantiate_reg;
    op_is_reseed_n = op_is_reseed_reg;
    op_is_generate_n = op_is_generate_reg;
    provided_data_n = provided_data_reg;
    temp0_n = temp0_reg;
    temp1_n = temp1_reg;

    busy_o = (state != S_IDLE);
    at_reseed_limit = (reseed_counter_reg >= MAX_BLOCKS_BETWEEN_RESEED);

    // AES defaults
    aes_in_valid = 1'b0;
    aes_in_block = '0;

    // DF defaults
    df_start = 1'b0;

    // Output pulse defaults
    done_set = 1'b0;
    rnd_valid_set = 1'b0;

    // FSM:
    unique case(state):
        // idle
        S_IDLE: begin
            // latch command: priority inst -> reseed -> generate
            if (instantiate_i) begin
                op_is_instantiate_n = 1'b1;
                op_is_reseed_n = 1'b0;
                op_is_generate_n = 1'b0;
                // start deriv funct to make seed_material
                state_n = S_DF_START;
            end 
            else if (reseed_i) begin
                op_is_instantiate_n = 1'b0;
                op_is_reseed_n = 1'b1;
                op_is_generate_n = 1'b0;
                state_n = S_DF_START;
            end 
            else if (generate_i) begin
                if (at_reseed_limit) begin
                    // @ reseed window limit: ignore generate request until reseed happens
                    state_n = S_IDLE;
                    end else begin
                    op_is_instantiate_n = 1'b0;
                    op_is_reseed_n = 1'b0;
                    op_is_generate_n = 1'b1;
                    blocks_left_n = num_blocks_i;
                    state_n = (num_blocks_i != 16'd0) ? S_GEN_REQ : S_IDLE;
                end
            end
        end

        // start
        // inst/reseed: run df -> Update(K,V, seed_material)  
        S_DF_START: begin
            df_start = 1'b1;         // 1 cycle start
            state_n = S_DF_WAIT;
        end
        S_DF_WAIT: begin
            if (df_done) begin
                provided_data_n = df_seed_material;
                state_n = S_UPDATE_INIT_START1;
            end
        end
        // wait

        // updating init

        // 2nd AES for update

        // update mixing


        // generating blocks: Need to finish
    endcase
end

endmodule