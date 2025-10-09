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
	rand_req_t rand_req_type;

	//SPI
	logic ss_n, mosi, miso;

	//DEBUG IO
	logic input_pin_1, output_pin_1, output_pin_2, debug;

	//TEMP IO (before buffer/entropy is made)
	logic [es_sources-1:0] entropy_source_array;
	logic [256:0] temp_seed_out;
	logic [127:0] temp_drbg_out;
	logic temp_out_valid;

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
		.spi_data_ready(),

		.debug(debug),
		.output_to_input_direct(1'b0),

		.output_pin_2(output_pin_2),
		.output_pin_1(output_pin_1),
		.input_pin_1(input_pin_1),

		.entropy_source_array(entropy_source_array),
		.arr_n(),
		.arr_p(),
		.jitter_disable_arr()
		
	);

	initial begin
		debug = 1'b0;
		rand_req = 1'b1;
		rand_req_type = RDSEED_64;
		forever begin 
			@(posedge top_clk);
			entropy_source_array = { $urandom, $urandom };
		end
	end

	//Drive reset and log signals
	initial begin
		$fsdbDumpfile("dump.fsdb");
		$fsdbDumpvars(0, "+all");
		#10ns
		top_reset = 1'b1;
		#100000ns
		$finish();
	end

endmodule
