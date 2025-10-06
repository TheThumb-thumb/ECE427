import le_types::*;
import params::*;
module conditioner_basic_tb;

	logic top_clk;
	logic top_reset;

	initial top_clk = 1'b0;
	always #1ns top_clk = ~top_clk;
	initial top_reset = 1'b1;

    localparam DATA_WIDTH = 256;

    logic oht_valid_i, 
    oht_ready_o,
    drbg_ready_i,
    drbg_valid_o,
    rdseed_ready_i,
    rdseed_valid_o;

    logic [(DATA_WIDTH/2)-1:0] key_i;
    logic [DATA_WIDTH-1:0] message_i, seed_o;

    logic debug, serial_input;
    logic [7:0] debug_register;

    conditioner #(
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
		.clk(top_clk),
		.rst_n(top_reset),

		.*
	);

	//extremely basic test

	initial begin
        debug = '0;
        serial_input = 'x;
        debug_register = 'x;

        oht_valid_i = 1'b0;
        drbg_ready_i = 1'b0;
        rdseed_ready_i = 1'b0;
        key_i = 'x;
        message_i = 'x;
		#10ns
        @(posedge top_clk);
        key_i =  128'h000102030405060708090a0b0c0d0e0f;
		message_i = {128'h00112233445566778899aabbccddeeff,
		128'h6A9EE8941F318681A3727155CE20CB9A};
        oht_valid_i = 1'b1;
        @(posedge top_clk);
        #1
        oht_valid_i = 1'b0;
		#100ns
        rdseed_ready_i = 1'b1;
        @(posedge top_clk);
        #1
        rdseed_ready_i = 1'b0;
        #100ns
    	$finish();
	end

	//result should be
	// MS: b79cf61ae1c5799b57bef5f3455bc8e2
	// LS: f9ad5cac96745a50a4f0a2a730325491

	initial begin
		$fsdbDumpfile("aes_dump.fsdb");
		$fsdbDumpvars(0, "+all");
		top_reset = 1'b0;
        #10ns
		top_reset = 1'b1;
	end

endmodule