import le_types::*;
import params::*;
module top_tb;

	logic top_clk;
	logic top_reset;

	initial top_clk = 1'b0;
	always #2ns top_clk = ~top_clk;
	initial top_reset = 1'b0;

	//CPU IO 
	logic rand_req, rand_valid;
	logic [7:0] rand_byte;
	logic [2:0] rand_req_type;

	//SPI
	logic ss_n, mosi, miso;

	//DEBUG IO
	logic input_pin_1, output_pin_1, output_pin_2, debug;

	top dut(
		.ic_clk(top_clk),
		.rst_n(top_reset),
	
		.rand_req(rand_req),
		.rand_req_type(rand_req_type),
		.rand_byte(rand_byte),
		.rand_valid(rand_valid),

		.ss_n(ss_n),
		.debug_clk(top_clk),
		.mosi(mosi),
		.miso(miso),

		.debug(debug),

		.output_pin_2(input_pin_1),
		.output_pin_1(output_pin_1),
		.input_pin_1(output_pin_2)
		
	);

	//Drive reset and log signals
	initial begin
		$fsdbDumpfile("dump.fsdb");
		$fsdbDumpvars(0, "+all");
		#10ns
		top_reset = 1'b1;
		#1000ns
		$finish();
	end

endmodule
