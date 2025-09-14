// ============================================================================
// Module: key_schedule
// Description: Generates all 11 round keys for AES-128 from the initial 128-bit key.
// This version uses a state machine to compute one round key per clock cycle.
//
// State Machine Operation:
// 1. IDLE: Waits for 'start_i' to go high.
// 2. INIT: Loads the input key as the first round key (Round 0).
// 3. COMPUTE: Spends 10 cycles calculating Round 1 through Round 10 keys.
// ============================================================================
module key_schedule (
    input  logic            clk,
    input  logic            rst_n,

    input  aes_core_state_t state_reg,
    input  logic [127:0]    key_in_i,
    output logic [127:0]    cur_round_key_o
);

    // Counter to track which round key is being computed (1 through 10)
    logic [3:0] round_cnt_reg;

    // Round constants
    logic [7:0] round_constants [10];
    initial begin
        round_constants[0] = 8'h01; round_constants[1] = 8'h02; round_constants[2] = 8'h04;
        round_constants[3] = 8'h08; round_constants[4] = 8'h10; round_constants[5] = 8'h20;
        round_constants[6] = 8'h40; round_constants[7] = 8'h80; round_constants[8] = 8'h1B;
        round_constants[9] = 8'h36;
    end

    // Combinatorial logic for the g-function (RotWord, SubWord, XOR Rcon)
    logic [31:0] g_func_in;
    logic [31:0] g_func_out;

    // 1. RotWord: One-byte circular left shift
    logic [31:0] rotated_word;
    assign rotated_word = {g_func_in[23:0], g_func_in[31:24]};


    // 2. SubWord: Substitute each byte using S-boxes
    logic [7:0] sub_bytes_in  [4];
    logic [7:0] sub_bytes_out [4];
    logic [31:0] subbed_word;

    generate for (genvar i = 0; i < 4; i++) begin : gen_sub_bytes
        // Connect inputs for SubWord
        assign sub_bytes_in[i] = rotated_word[31-8*i -: 8];
        // Re-assemble the word from S-box outputs
        assign subbed_word[31-8*i -: 8] = sub_bytes_out[i];

        sbox sbox_inst (
            .in_byte (sub_bytes_in[i]),
            .out_byte(sub_bytes_out[i])
        );
    end endgenerate

    // 3. XOR with Round Constant
    assign g_func_out = subbed_word ^ {round_constants[round_cnt_reg], 24'b0};

    // Combinatorial logic to calculate the next round key from the previous one
    logic [127:0] next_key_w;

    assign g_func_in = cur_round_key_o[31:0]; // The g-function operates on the last word (W3)

    // Calculate the four words (W0, W1, W2, W3) of the next round key
    assign next_key_w[127:96] = cur_round_key_o[127:96] ^ g_func_out;
    assign next_key_w[95:64]  = cur_round_key_o[95:64]  ^ next_key_w[127:96];
    assign next_key_w[63:32]  = cur_round_key_o[63:32]  ^ next_key_w[95:64];
    assign next_key_w[31:0]   = cur_round_key_o[31:0]   ^ next_key_w[63:32];

    // FSM Sequential Logic: Counter Registers
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            round_cnt_reg <= 4'd0;
        end else begin
            if(state_reg == S_PROCESS_ROUNDS || state_reg == S_INIT_ADD_KEY) round_cnt_reg <= round_cnt_reg + 1;
        end
    end

    // Output and Key Storage Register Logic
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            cur_round_key_o <= 128'bx;
        end else begin
            case(state_reg) 
                S_IDLE: begin
                    // Load the initial key as the Round 0 key
                    cur_round_key_o <= key_in_i;
                end
                S_INIT_ADD_KEY, S_PROCESS_ROUNDS, S_FINAL_ROUND: begin
                     // In each compute cycle, store the newly calculated key
                    cur_round_key_o <= next_key_w;
                end
                default: begin
                    // Hold values in IDLE state
                end
            endcase
        end
    end

endmodule : key_schedule