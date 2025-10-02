/**
 * Conditioner Module
 *
 * Mixes and distills the entropy within a 384 bit input down to a 
 * 256 output. 
 */
import le_types::*;
module conditioner #(
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
    output logic [DATA_WIDTH-1:0]       mac_o,          // The resulting MAC


    // Debug Control signals
    input logic debug,
    input logic serial_input,           //Input from the FPGA
    input logic [7:0] debug_register    //SPI register that holds relevant settings to the conditioner's debug mode

);

logic [(DATA_WIDTH/2)-1:0] debug_key_buffer;
logic [DATA_WIDTH-1:0] debug_message_buffer;
logic [8:0] debug_ctr;

//Normal operation signals
logic start;
logic [DATA_WIDTH-1:0] message;
logic [(DATA_WIDTH-1)-1:0] key;

always_ff @ (posedge clk) begin
    if (debug) begin
        // if we are in debug mode and the input pin is driving us, serially shift
        // that pins data into the debug registers, starting with the key
        if(debug_register == 8'b1010_0000) begin 
            if(debug_ctr < 128) debug_key_buffer[debug_ctr] <= serial_input;
            else debug_key_buffer[debug_ctr - 128] <= serial_input;

            if(debug_ctr == 9'd384) debug_ctr <= '0;
            else debug_ctr <= debug_ctr + 1'b1;
        end
    end else begin
        debug_key_buffer <= '0;
        debug_message_buffer <= '0;
        debug_ctr <= '0;
    end
end

//Drive inputs
always_comb begin
    start = start_i;
    key = key_i;
    message = message_i;
    //We are in debug mode, use the debug buffer and serial input
    if(debug && debug_register == 8'b1010_0000) begin
        if(debug_ctr == 9'd384) begin
            start = 1'b1;
            key = debug_key_buffer;
            message = debug_message_buffer;
        end else begin
            start = 1'b0;
            key = '0;
            message = '0;
        end

    end

end

aes_cbc_mac #(
    .DATA_WIDTH(DATA_WIDTH)
) aes_cbc_mac_inst (
    .clk(clk),
    .rst_n(rst_n),

    .start_i(start),
    .done_o(done_o),    //pass output as normal regardless of debug

    .key_i(key),
    .message_i(message),
    .mac_o(mac_o)       //pass output as normal regardless of debug
);


endmodule