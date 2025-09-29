/**
 * AES-CBC-MAC Conditioner Top-Level Module
 *
 * Generates a 256-bit Message Authentication Code (MAC) for a given
 * message and key using the AES-CBC-MAC algorithm. Will be used for
 * entropy conditioning as per NIST 800-90B whitepaper
 *
 */
import le_types::*;
module aes_cbc_mac #(
    parameter DATA_WIDTH = 256
)(
    // System Signals
    input  logic        clk,
    input  logic        rst_n,

    // Control Signals
    input  logic        start_i,                // Start the MAC calculation
    output logic        done_o,                 // MAC calculation is complete

    // Data Ports
    input  logic [(DATA_WIDTH/2)-1:0]   key_i,          // The 128-bit secret key
    input  logic [DATA_WIDTH-1:0]       message_i,      // 256-bit message
    output logic [DATA_WIDTH-1:0]   mac_o           // The resulting MAC
);

logic data_in_valid, data_out_valid;
logic [(DATA_WIDTH/2)-1:0] key, key_reg, message, data_out;
logic [DATA_WIDTH-1:0] message_reg;

aes_cbc_mac_state_t current_state, next_state;

always_ff @ (posedge clk) begin : cbc_mac_states
   if(!rst_n) begin
    current_state <= IDLE;
   end else begin
    current_state <= next_state;
   end 
end

always_ff @ (posedge clk) begin : cbc_mac_bookkeeping
    if(!rst_n) begin
        key_reg <= '0;
        message_reg <= '0;
    end else begin
        if(start_i && current_state == IDLE) begin
            key_reg <= key_i;
            message_reg <= message_i;
        end

        if(current_state == FIRST_HALF && data_out_valid) begin
            message_reg[(DATA_WIDTH/2)-1:0] <= data_out;
        end
    end
end

always_comb begin : cbc_mac_transitions
    next_state = current_state;
    key = 'x;
    message = 'x;
    data_in_valid = 1'b0;
    done_o = 1'b0;

   unique case (current_state) 

    IDLE: begin    
        if(start_i) begin
            next_state = FIRST_HALF;
        end
        key = 'x;
        message = 'x;
        data_in_valid = 1'b0;
        done_o = 1'b0;
    end

    FIRST_HALF: begin
        key = key_reg;
        message = message_reg[127:0];
        data_in_valid = 1'b1;
        if(data_out_valid) begin 
            next_state = SECOND_HALF;
            data_in_valid = 1'b0;
        end else begin
            data_in_valid = 1'b1;
        end
    end


    SECOND_HALF: begin
        key = key_reg;
        message = message_reg[255:128] ^ message_reg[127:0];
        data_in_valid = 1'b1;
        if(data_out_valid) begin 
            next_state = DONE;
            data_in_valid = 1'b0;
        end
    end

    DONE: begin
        done_o = 1'b1;
        next_state = IDLE;
        data_in_valid = 1'b0;
    end

    default: begin

    end

   endcase
end

assign mac_o = {data_out, message_reg[127:0]};

aes_core aes (
    .clk(clk),
    .rst_n(rst_n),

    .data_in_valid_i(data_in_valid),
    .key_in_i(key),
    .data_in_i(message),

    .data_out_valid_o(data_out_valid),
    .data_out_o(data_out)
);

endmodule