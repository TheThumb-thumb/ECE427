/**
 * Conditioner Module
 *
 * Mixes and distills the entropy within a 384 bit input down to a 
 * 256 output. Wraps aes_cbc_mac with handshake signals.
 */
import le_types::*;
module conditioner #(
    parameter DATA_WIDTH = 256
)(
    // System Signals
    input  logic        clk,
    input  logic        rst_n,

    // Control Signals (valid/ready handshakes)
    input  logic        oht_valid_i,            // OHT indicating that a raw number is valid
    output logic        oht_ready_o,            // Indicate to OHT that we ready for a raw number

    input  logic        drbg_ready_i,           // DRBG indicating it is ready for a seed
    output logic        drbg_valid_o,           // Indicate to DRBG that a seed is valid

    input  logic        rdseed_ready_i,         // Output buffer indicating it is ready for a seed
    output logic        rdseed_valid_o,         // Indicate to output buffer that a seed is valid

    // Data Ports
    input  logic [(DATA_WIDTH/2)-1:0]   key_i,          // The 128-bit secret key
    input  logic [DATA_WIDTH-1:0]       message_i,      // 256-bit message
    output logic [DATA_WIDTH-1:0]       seed_o,         // 256-bit seed

    // Debug Control signals
    input logic debug,                          // Debug pin
    input logic serial_input,                   // Input from the FPGA
    input logic [7:0] debug_register            // SPI register that holds relevant settings to the conditioner's debug mode

);

logic [(DATA_WIDTH/2)-1:0] debug_key_buffer;
logic [DATA_WIDTH-1:0] debug_message_buffer;
logic [8:0] debug_ctr;

//Normal operation signals
logic start, done, busy, seed_staged;
logic [DATA_WIDTH-1:0] message;
logic [(DATA_WIDTH/2)-1:0] key;

always_ff @ (posedge clk) begin
    if(!rst_n) begin
        busy <= 1'b0;
        seed_staged <= 1'b0;
    end else begin
        if(start) busy <= 1'b1;
        else if(busy && (drbg_ready_i || rdseed_ready_i)) busy <= 1'b0;

        if(done) seed_staged <= 1'b1;
        else if(seed_staged && (drbg_ready_i || rdseed_ready_i)) seed_staged <= 1'b0;
    end
end

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

//Drive I/O
always_comb begin
    //Core control signals
    start = 1'b0;
    key = key_i;
    message = message_i;

    //Control outputs
    oht_ready_o = ~busy;
    drbg_valid_o = 1'b0;
    rdseed_valid_o = 1'b0;

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

    if(oht_ready_o && oht_valid_i && !busy) begin
        start = 1'b1;
    end

    if(seed_staged) begin
        drbg_valid_o = 1'b1;
        if(!drbg_ready_i) rdseed_valid_o = 1'b1;
    end

end

aes_cbc_mac #(
    .DATA_WIDTH(DATA_WIDTH)
) aes_cbc_mac_inst (
    .clk(clk),
    .rst_n(rst_n),

    .start_i(start),
    .done_o(done),

    .key_i(key),
    .message_i(message),
    .mac_o(seed_o)
);


endmodule