import le_types::*;
import params::*;
module top_tb_debug;

	logic top_clk;
	logic top_reset;

	initial top_clk = 1'b0;
	always #2ns top_clk = ~top_clk;
	initial top_reset = 1'b1;

	//CPU IO 
	logic rand_req, rand_valid;
	logic [OUTPUT_WIDTH-1:0] rand_byte;
	rand_req_t rand_req_type;

	//SPI
	logic ss_n, mosi, miso, spi_data_ready;
	

	//DEBUG IO
	logic input_pin_1, output_pin_1, output_pin_2, debug;

	//TEMP IO (before buffer/entropy is made)
	logic [es_sources-1:0] entropy_source_array;
	logic [256:0] temp_seed_out;
	logic [127:0] temp_drbg_out;
	logic temp_out_valid;
	logic [latch_sources-1:0][7:0] arr_n, arr_p;
	logic [latch_sources-1:0] jitter_disable_arr;

	logic [383:0] conditioner_serial_input;
	logic [21:0] test_word;

	localparam word_width = 5'd22;

	top dut(
		.ic_clk(top_clk),
		.rst_n(top_reset),
	
		.rand_req(rand_req),
		.rand_req_type(rand_req_type),
		.rand_byte(rand_byte),
		.rand_valid(rand_valid),
		.slow_clk(),

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

		.entropy_source_array(entropy_source_array),
		.arr_n(arr_n),
		.arr_p(arr_p),
		.jitter_disable_arr(jitter_disable_arr)
		
	);

	initial begin
		debug = 1'b1;
		rand_req = 1'b1;
		rand_req_type = RDSEED_64;
		input_pin_1 = 1'b0;

		ss_n = 1'b1;
		#4ns;

		// ---------------- Set input 1 to conditioner

        // output 1 =vcc, output2 = clk, input 1 -> conditioner
        assign test_word = 22'b0_00_00000_00_00001_11_00000; // input to conditioner
        
        // input to be on pin 1
        assign conditioner_serial_input = 384'h7b3a9f0e5c6d2814b7f8d0a3e5b6f7a8c9d0e1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c1d2e3f4a5b6c7d8e9f;

        // Test passed: 9/29/25
        // Initial states

        // Select the slave
        @(posedge top.u_control.clk);
        ss_n = 0;
        #6ns;

        @(negedge top.u_control.clk);
        for (int i=word_width-1; i>=0; i--) begin
            mosi = test_word[i]; // MSB first
            #4ns;
        end

        // Check results
        if (spi_data_ready) begin
            @(posedge top.u_control.clk)
            @(posedge top.u_control.clk)
            @(posedge top.u_control.clk)

            $display("Curr state: %h", top.u_control.curr_state);
            if (top.u_control.curr_state == test_word) begin
                $display("Curr state Test PASSED!");
            end else begin
                $display("Curr state FAILED: Expected %h", test_word);
            end
        end else begin
            $display("Curr state FAILED: data_ready not high");
        end

        ss_n = 1;
        mosi = 0;

        @(posedge top.u_control.clk)
        for (int i=383; i>=0; i--) begin
            input_pin_1 = conditioner_serial_input[i]; // MSB first
            #4ns;
        end

        #12ns;	
	end

	//Drive reset and log signals
	initial begin
		$fsdbDumpfile("conditioner_debug_tb.fsdb");
		$fsdbDumpvars(0, "+all");
		#5ns
		top_reset = 1'b0;
		#5ns
		top_reset = 1'b1;
		#100000ns
		$finish();
	end

endmodule
