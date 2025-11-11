import le_types::*;
import params::*;
module top_tb;

	logic top_clk;
	logic top_reset;

	initial top_clk = 1'b0;
	always #2ns top_clk = ~top_clk;
	initial top_reset = 1'b1;

	//CPU IO 
	logic rand_req, rand_valid;
	logic [OUTPUT_WIDTH-1:0] rand_byte;
	rand_req_t rand_req_type;
	logic slow_clk;

	//SPI
	logic ss_n, mosi, miso;

	//DEBUG IO
	logic input_pin_1, output_pin_1, output_pin_2, debug;

	//TEMP IO (before buffer/entropy is made)
	logic [es_sources-1:0] entropy_source_array;
	logic [256:0] temp_seed_out;
	logic [127:0] temp_drbg_out;
	logic temp_out_valid;
	logic [latch_sources-1:0][calib_bits-1:0] arr_n, arr_p;
	logic [latch_sources-1:0] jitter_disable_arr;
	logic spi_data_ready;

	top dut(
		.ic_clk(top_clk),
		.rst_n(top_reset),
	
		.rand_req(rand_req),
		.rand_req_type(rand_req_type),
		.rand_byte(rand_byte),
		.rand_valid(rand_valid),
		.slow_clk(slow_clk),

		.ss_n(ss_n),
		.debug_clk(top_clk),
		.mosi(mosi),
		.miso(miso),
		.spi_data_ready(spi_data_ready),

		.debug(debug),
		.output_to_input_direct(1'b0),

		.output_pin_2(output_pin_2),
		.output_pin_1(output_pin_1),
		.input_pin_1(input_pin_1),

		.temp_sens_in(4'b0000),
		.io_temp_debug(1'b0),

		.entropy_source_array(entropy_source_array),
		.arr_n(arr_n),
		.arr_p(arr_p),
		.jitter_disable_arr(jitter_disable_arr)
		
	);

	//Drive entropy pins (pretend to be entropy)
	initial begin
		forever begin 
			@(posedge top_clk);
			entropy_source_array = { $urandom, $urandom };
			//entropy_source_array = '1;
		end
	end

	int shorts_received, shorts_received_max; 

	initial begin
		debug = 1'b0;
		rand_req = 1'b1;
		
		rand_req_type = RDRAND_64;
		forever begin
			@(posedge slow_clk);
		end

		// forever begin 
		// 	@(posedge slow_clk) begin
		// 		if(shorts_received == shorts_received_max) begin
		// 			case ($urandom_range(5, 0))
		// 				0: rand_req_type = RDSEED_16;
		// 				1: rand_req_type = RDRAND_16;
		// 				2: rand_req_type = RDSEED_32;
		// 				3: rand_req_type = RDRAND_32;
		// 				4: rand_req_type = RDSEED_64;
		// 				5: rand_req_type = RDRAND_64;
		// 				default: rand_req_type = RDRAND_16;
		// 			endcase
		// 		end
		// 	end
		// end
	end

	//Monitor output pins, verify that no extra bytes are being served
	initial begin 

		forever @(posedge slow_clk) begin 
			case (rand_req_type)
				RDSEED_16, RDRAND_16: begin
					shorts_received_max = 1;
				end
				RDSEED_32, RDRAND_32: begin
					shorts_received_max = 2;
				end 
				RDSEED_64, RDRAND_64: begin
					shorts_received_max = 4;
				end
			endcase
		end

		forever begin
			@(posedge slow_clk) begin
				#1;
				if(rand_valid) shorts_received = shorts_received + 1;
				else if(shorts_received == shorts_received_max) shorts_received = 0;
			end
		end 
	end

	// property rand_byte_stability_on_valid;
	// 	@(posedge slow_clk)
	// endproperty

	//Drive reset and log signals
	initial begin
		$fsdbDumpfile("dump.fsdb");
		$fsdbDumpvars(0, "+all");
		#5ns
		top_reset = 1'b0;
		#5ns
		top_reset = 1'b1;
		#100000ns
		$finish();
	end

endmodule
