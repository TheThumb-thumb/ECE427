`timescale 1ns/1ps

import le_types::*;
import params::*;

module top_io_tb;

	//Paramters
	localparam WORD_WIDTH = 5'd22;

	//Debug Test names
	typedef enum logic [WORD_WIDTH-1:0] { 
		READ_DEFAULT_STATE,
		READ_HALT_STATE,
		READ_LATCH_LS,
		READ_LATCH_MS,
		READ_JITTER_LS,
		READ_JITTER_MS
	} read_cmd_name_e;

	typedef struct {
		logic [WORD_WIDTH-1:0] cmd;
		logic [WORD_WIDTH-1:0] exp_rsp;
	} read_cmd_data_t;

	const read_cmd_data_t READ_CMD_MAP[read_cmd_name_e] = '{
		READ_DEFAULT_STATE: '{cmd: 22'b1100000000000000000000, exp_rsp: '0},
		READ_HALT_STATE: 	'{cmd: 22'b1100010000000000000000, exp_rsp: 22'hED_BEF},
		READ_LATCH_LS: 		'{cmd: 22'b1100110000000000000000, exp_rsp: '0},
		READ_LATCH_MS: 		'{cmd: 22'b1101000000000000000000, exp_rsp: '0},
		READ_JITTER_LS: 	'{cmd: 22'b1101010000000000000000, exp_rsp: '0},
		READ_JITTER_MS: 	'{cmd: 22'b1101100000000000000000, exp_rsp: '0}
	};

	// Clock generation
    logic ic_clk;

	//Reset pin
	logic top_reset;
	initial top_reset = 1'b1;

	//CPU IO 
	logic rand_req, rand_valid;
	logic [OUTPUT_WIDTH-1:0] rand_byte;
	rand_req_t rand_req_type;
	logic slow_clk;

	//SPI
	logic ss_n, mosi, miso;

	//DEBUG IO
	logic input_pin_1, output_pin_1, output_pin_2, debug, output_to_input_direct;

	//TEMP/ENTROP
    logic io_temp_debug;
    logic [TEMP_WIDTH-1:0] temp_threshold_array_0;
    logic [TEMP_WIDTH-1:0] temp_threshold_array_1;
    logic [TEMP_WIDTH-1:0] temp_threshold_array_2;
    logic [TEMP_WIDTH-1:0] temp_threshold_array_3;
    logic [TEMP_WIDTH-1:0] temp_counter_0;
    logic [TEMP_WIDTH-1:0] temp_counter_1;
    logic [TEMP_WIDTH-1:0] temp_counter_2;
    logic [TEMP_WIDTH-1:0] temp_counter_3;
    logic [es_sources-1:0] entropy_source_array, entropy_debug, entropy;
    logic [latch_sources-1:0][calib_bits-1:0] arr_n;
    logic [latch_sources-1:0][calib_bits-1:0] arr_p;
    logic [jitter_sources-1:0] jitter_disable_arr;
    logic [(latch_sources/2)-1:0] lower_latch_entropy_good;
    logic [(latch_sources/2)-1:0] upper_latch_entropy_good;
    logic [(latch_sources/2)-1:0] lower_jitter_entropy_good;
    logic [(latch_sources/2)-1:0] upper_jitter_entropy_good;

	//Debug testing variables
	logic [21:0] test_word;
    logic [21:0] fake_input;
    logic [21:0] master_received;
    logic [383:0] conditioner_serial_input;
    logic [383:0] entropy_sim_serial_input;
    logic [11:0] entropy_sim_serial_input_short;
    logic [3:0] EN_out1, EN_out2;
    logic [63:0] analog_clk;

	//Drive clocks
	initial begin
        ic_clk = 0;
        forever #10 ic_clk = ~ic_clk;
    end

	top_io dut(
		// CLK+RST
		.ic_clk_io(ic_clk),
		.rst_n_io(top_reset),
	
		// CPU I/O
		.rand_req_io(rand_req),
		.rand_req_type_io(rand_req_type),
		.rand_byte_io(rand_byte),
		.rand_valid_io(rand_valid),
		.slow_clk_io(slow_clk),

		// SPI Pins
		.ss_n_io(ss_n),
		.mosi_io(mosi),
		.miso_io(miso),
		.spi_data_ready_io(spi_data_ready),

		// Debug
		.debug_io(debug),
		.output_to_input_direct_io(output_to_input_direct),

		// Serial I/O for debug
		.output_pin_2_io(output_pin_2),
		.output_pin_1_io(output_pin_1),
		.input_pin_1_io(input_pin_1),

		// Temperature sensor I/O
        .temp_debug_io(io_temp_debug),
        .EN_out1(EN_out1),
        .EN_out2(EN_out2),
        .temp_counter_0(temp_counter_0),
        .temp_counter_1(temp_counter_1),
        .temp_counter_2(temp_counter_2),
        .temp_counter_3(temp_counter_3),
        
        .entropy_source_array(entropy),
        .arr_n(arr_n),
        .arr_p(),
        .jitter_disable_arr(),
        .analog_clk()
		
	);

	logic [63:0] permanent_entropy_mask;
    initial begin
        permanent_entropy_mask = {$urandom(), $urandom()};
        //permanent_entropy_mask = '1;
        //permanent_entropy_mask = 64'hF77D_FAD5;
    end
	//Drive entropy pins (pretend to be entropy)
    always_ff @(posedge ic_clk) begin
        entropy_source_array <= {$urandom(), $urandom()} & permanent_entropy_mask;
    end

    always_comb begin
        if(debug) entropy = entropy_debug;
        else entropy = entropy_source_array;
    end
 
	int shorts_received, shorts_received_max; 

	initial begin
		debug = 1'b0;
        temp_counter_0 = {1'b0, 12'hECE};
        temp_counter_1 = {1'b0, 12'hECE};
        temp_counter_2 = {1'b0, 12'hECE};
        temp_counter_3 = {1'b0, 12'hECE};
	end

    logic request_outstanding;
    int instr_select;
    rand_req_t rand_req_type_reg;

	always_ff @(posedge slow_clk or negedge top_reset) begin
        if(!top_reset) begin
            rand_req <= 1'b0;
            request_outstanding <= 1'b0;
            shorts_received <= 0;
        end else begin
            if(!request_outstanding || shorts_received == shorts_received_max) begin 
                rand_req <= 1'b1;
                request_outstanding <= 1'b1;
                shorts_received <= 0;
                instr_select <= $urandom_range(5, 0);
            end else begin
                rand_req <= '0;
                instr_select <= 6;
            end

            if(rand_valid) begin 
                shorts_received <= shorts_received + 1;
            end
            
        end
    end

    always_comb begin
        case (instr_select)
            0: rand_req_type = RDSEED_16;
            1: rand_req_type = RDRAND_16;
            2: rand_req_type = RDSEED_32;
            3: rand_req_type = RDRAND_32;
            4: rand_req_type = RDSEED_64;
            5: rand_req_type = RDRAND_64;
            default: rand_req_type = 'x;
        endcase

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

	//Below are assertions that ensure no bad behavior at the host I/O pins

	// --- Assertion 1 ---
    // Ensures that while rand_valid is high, rand_byte can only change on the 
    // rising edge of slow_clk.

    property p_rand_byte_stable;
		@(posedge ic_clk)
		disable iff ($rose(slow_clk))
        rand_valid |-> $stable(rand_byte);
    endproperty
    a_rand_byte_stable: assert property (p_rand_byte_stable) 
		else $fatal("rand_byte changed when not at posedge slow_clk");

    // --- Assertion 2 ---
    // Asserts that while rand_valid is high, rand_byte can never be all 0.
    // This could happen organically however if you are really unlucky
    property p_rand_byte_not_zero;
		@(posedge ic_clk)
		disable iff ($rose(slow_clk) || $rose(rand_valid))
        rand_valid |-> (rand_byte !== '0);
    endproperty
    a_rand_byte_not_zero: assert property (p_rand_byte_not_zero) 
        else $warning("rand_byte was all zeros while rand_valid was high");

	// --- Assertion 3 ---
    // Asserts that while rand_valid is high, rand_byte can never be an unknown value.

    property p_rand_byte_not_unknown;
		@(posedge ic_clk)
		disable iff ($rose(slow_clk) || $rose(rand_valid))
        rand_valid |-> (!$isunknown(rand_byte));
    endproperty
    a_rand_byte_not_unknown: assert property (p_rand_byte_not_unknown) 
        else $fatal("rand_byte was unknown ('x or 'z) while rand_valid was high");

    // Assertion 4
    // Asserts that an outstanding request takes no longer than 5000 ns to serve (otherwise it's a timeout)

    initial begin : timeout_check_block // Use a named block for clarity
        // Loop continuously until the 'debug' signal is set
        forever begin
            // 1. Check the disable condition *before* proceeding
            if (debug) begin
                $display("--- Assertion 4 Permanently Disabled: Debug mode active at time %t ---", $realtime);
                break; // Exit the forever loop permanently
            end
            // 2. Wait for the starting condition
            @(posedge rand_req);
            // 3. Immediately check the disable condition again (in case 'debug' went high at the same time)
            if (debug) begin
                break; // Exit loop
            end
            // 4. Start the timeout detection
            fork
                #10000ns;     
                @(negedge rand_req);  
            join_any
            assert (rand_req == 1'b0)
            else $fatal(1, "ASIC TIMEOUT: 'rand_req' was held high for 10000ns at time %t", $realtime);
            disable fork;
        end
    end : timeout_check_block
	
	//Below are Tasks
	task reset_dut();
        $display("Applying reset...");
        top_reset = 1'b1;
        #500ns
        top_reset = 1'b0;
        #500ns
		top_reset = 1'b1;
    endtask

    task init();
        entropy_debug = '0;
        io_temp_debug = '0;
        input_pin_1 = '0;
        output_to_input_direct = '0;
        mosi = '0;
        ss_n = '0;
    endtask

    task assert_debug();
        $display("Asserting Debug Pin...");
        debug = 1'b1;
    endtask

    task de_assert_debug();
        $display("De-Asserting Debug Pin...");
        debug = 1'b0;
    endtask


	//Main loop -> drive reset, drive normal behavior, and also randomly test DFT tasks intermittently.
	initial begin
		$fsdbDumpfile("post_synth_dump.fsdb");
		$fsdbDumpvars(0, "+all");
        init();
		reset_dut();

        // assert_debug();
        // repeat (50) begin
        //     run_random_debug_test(); 
        //     #50ns
        //     reset_dut();
        // end
        // de_assert_debug();

        #200000ns
		$finish();
	end

endmodule

