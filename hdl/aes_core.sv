/*
 * Module: aes_core.sv
 *
 * Description: Multi-Cycle, FSM-based AES-128 Encryption Core. This module
 * implements the same functionality as a pipelined core but reuses
 * a single round instance over multiple clock cycles to save area.
 * A pipelined design was found to be useless in a AES-CBC-MAC implementation,
 * which this project uses. 
 * 
 * Behavior: Encrypts a single 128-bit block using a 128-bit key. The encryption
 * process is controlled by a state machine and takes 13 clock cycles
 * from a valid data input to a valid data output.
 *
 */
module aes_core(
    // System Signals
    input  logic         clk,
    input  logic         rst_n,

    // Data Input Interface
    input  logic           data_in_valid_i,    // Indicates data_in is valid
    input  logic [127:0]   key_in_i,           // The 128-bit secret key
    input  logic [127:0]   data_in_i,          // 128-bit data block to encrypt

    // Data Output Interface
    output logic           data_out_valid_o,   // Indicates data_out is valid
    output logic [127:0]   data_out_o          // 128-bit encrypted data block
);

    aes_core_state_t state_reg, state_next;

    //--------------------------------------------------------------------------
    // Datapath Registers
    //--------------------------------------------------------------------------
    logic [127:0] key_reg, key_reg_i;  // Registers the key for the duration of the encryption
    logic [127:0] aes_state_reg;       // Holds the intermediate state between rounds
    logic [3:0]   round_counter_reg;   // Counts the 9 main rounds (from 1 to 9)
    logic [127:0] data_out_reg;        // Registers the final output
    logic         data_out_valid_reg;  // Registers the output valid signal

    //--------------------------------------------------------------------------
    // Wires and Sub-Module Connections
    //--------------------------------------------------------------------------
    logic [127:0] current_round_key;   // Storage for the 11 round keys
    logic         round_key_ready;     // Each index of this vector determines if a round key is ready
    logic [127:0] round_output;        // Combinational output of the standard round module
    logic [127:0] final_round_output;  // Combinational output of the final round module

    //--------------------------------------------------------------------------
    // Sub-Module Instantiations
    //--------------------------------------------------------------------------

    // Key schedule calculates all round keys based on the registered input key
    key_schedule key_schedule_inst (
        .clk            (clk),
        .rst_n          (rst_n),
        .state_reg      (state_reg),
        .key_in_i       (key_reg),
        .cur_round_key_o(current_round_key)
    );

    assign key_reg = (state_reg == S_PROCESS_ROUNDS) ? key_reg : key_in_i; 

    // A single standard round instance, reused for rounds 1 through 9
    aes_round aes_round_inst (
        .state_in_i         (aes_state_reg),
        .round_key_in_i     (current_round_key),
        .state_out_o        (round_output)
    );

    // A single final round instance, used for the 10th and final round
    aes_round_final aes_round_final_inst (
        .state_in_i     (aes_state_reg),
        .round_key_in_i (current_round_key),
        .state_out_o    (final_round_output)
    );

    //--------------------------------------------------------------------------
    // State Transition Logic (Combinational)
    //--------------------------------------------------------------------------
    always_comb begin
        state_next = state_reg; // Default to staying in the current state
        case (state_reg)
            S_IDLE: begin
                if (data_in_valid_i) begin
                    state_next = S_INIT_ADD_KEY;
                end
            end
            
            S_INIT_ADD_KEY: begin
                state_next = S_PROCESS_ROUNDS;
            end
            
            S_PROCESS_ROUNDS: begin
                // Rounds 1 through 9 are processed here.
                // After the 9th round is processed, move to the final round.
                if (round_counter_reg == 9) begin
                    state_next = S_FINAL_ROUND;
                end
            end
            
            S_FINAL_ROUND: begin
                state_next = S_DONE;
            end
            
            S_DONE: begin
                state_next = S_IDLE;
            end
        endcase
    end

    //--------------------------------------------------------------------------
    // State and Datapath Update Logic (Sequential)
    //--------------------------------------------------------------------------
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            state_reg         <= S_IDLE;
            aes_state_reg     <= 128'b0;
            key_reg_i         <= 128'b0;
            round_counter_reg <= 4'd1;
            data_out_reg      <= 128'b0;
            data_out_valid_reg<= 1'b0;
        end else begin
            // Default assignments
            state_reg <= state_next;
            data_out_valid_reg <= 1'b0; // Output valid is a single-cycle pulse

            case (state_reg)
                S_IDLE: begin
                    if (data_in_valid_i) begin
                        // Latch inputs and start the process
                        key_reg_i <= key_in_i;
                        aes_state_reg <= data_in_i;
                        round_counter_reg <= 4'd1; // Initialize for the first round
                    end
                end
                
                S_INIT_ADD_KEY: begin
                    // Perform the initial AddRoundKey operation
                    aes_state_reg <= key_reg_i ^ aes_state_reg;
                end
                
                S_PROCESS_ROUNDS: begin
                    // Process a standard round and increment the counter
                    aes_state_reg <= round_output;
                    round_counter_reg <= round_counter_reg + 1;
                end
                
                S_FINAL_ROUND: begin
                    // Process the final round (no MixColumns)
                    aes_state_reg <= final_round_output;
                end
                
                S_DONE: begin
                    // Set output valid and store final result
                    data_out_valid_reg <= 1'b1;
                    data_out_reg <= aes_state_reg;
                end
            endcase
        end
    end

    //--------------------------------------------------------------------------
    // Output Assignments
    //--------------------------------------------------------------------------
    assign data_out_o = data_out_reg;
    assign data_out_valid_o = data_out_valid_reg;

endmodule : aes_core
