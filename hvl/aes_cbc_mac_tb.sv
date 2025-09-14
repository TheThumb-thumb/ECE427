import le_types::*;
import params::*;
module aes_cbc_mac_tb;

	logic top_clk;
	logic top_reset;

	initial top_clk = 1'b0;
	always #1ns top_clk = ~top_clk;
	initial top_reset = 1'b1;

    localparam DATA_WIDTH = 256;

    logic        start_i;
	initial start_i = 1'b0;
    logic        done_o;
    logic [(DATA_WIDTH/2)-1:0] key_i;
    logic [DATA_WIDTH-1:0] message_i;
    logic [DATA_WIDTH-1:0] mac_o ;


    aes_cbc_mac #(
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
		.clk(top_clk),
		.rst_n(top_reset),

		.*
	);

	initial begin 
		#10ns
		@(posedge top_clk);
		key_i =  128'h000102030405060708090a0b0c0d0e0f;
		//key_i =  128'h0;
		message_i = {128'h00112233445566778899aabbccddeeff,
		128'h6A9EE8941F318681A3727155CE20CB9A};
		start_i = 1'b1;
		@(posedge top_clk);
		start_i = 1'b0;
		key_i = '0;
		message_i = '0;
	end

	//result should be
	// MS: 7d7786be32d059a60ca8021a65dd9f09
	// LS: f9ad5cac96745a50a4f0a2a730325491

	initial begin
		$fsdbDumpfile("aes_dump.fsdb");
		$fsdbDumpvars(0, "+all");
		top_reset = 1'b0;
        #10ns
		top_reset = 1'b1;
		#1000ns
		$finish();
	end

endmodule : aes_cbc_mac_tb
