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
    logic debug_clk;
    logic ic_clk;
	logic top_clk;

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
	logic input_pin_1, output_pin_1, output_pin_2, debug;

	//TEMP/ENTROP
	logic[3:0] temp_sens_in;
    assign temp_sens_in = '0;
    logic io_temp_debug;
    logic [TEMP_WIDTH-1:0] temp_threshold_array_0;
    logic [TEMP_WIDTH-1:0] temp_threshold_array_1;
    logic [TEMP_WIDTH-1:0] temp_threshold_array_2;
    logic [TEMP_WIDTH-1:0] temp_threshold_array_3;
    logic [TEMP_WIDTH-1:0] temp_counter_0;
    logic [TEMP_WIDTH-1:0] temp_counter_1;
    logic [TEMP_WIDTH-1:0] temp_counter_2;
    logic [TEMP_WIDTH-1:0] temp_counter_3;
    logic [es_sources-1:0] entropy_source_array;
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
        debug_clk = 0;
        forever #5 debug_clk = ~debug_clk; // 100 MHz clock
    end

	initial begin
        ic_clk = 0;
        forever #2 ic_clk = ~ic_clk; // 500 MHz clock
    end

	always_comb begin
		if(debug) top_clk = debug_clk;
		else top_clk = ic_clk;
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
		.debug_clk_io(debug_clk),
		.mosi_io(mosi),
		.miso_io(miso),
		.spi_data_ready_io(spi_data_ready),

		// Debug
		.debug_io(debug),
		.output_to_input_direct_io(1'b0),

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
        
        .entropy_source_array(entropy_source_array),
        .arr_n(arr_n),
        .arr_p(),
        .jitter_disable_arr(),
        .analog_clk(),
        .vdd_A(),
        .vdd_B(),
        .jitter_vdd_A(),
        .jitter_vdd_B()
		
	);

	//Drive entropy pins (pretend to be entropy)
    always_ff @(posedge top_clk) begin
        entropy_source_array <= {$urandom(), $urandom()};
    end
 
	int shorts_received, shorts_received_max; 

	initial begin
		debug = 1'b0;
        temp_counter_0 = {1'b0, 12'hECE};
        temp_counter_1 = {1'b0, 12'hECE};
        temp_counter_2 = {1'b0, 12'hECE};
        temp_counter_3 = {1'b0, 12'hECE};
	end

	always_ff @(posedge slow_clk) begin
		if(shorts_received == shorts_received_max) begin
			case ($urandom_range(5, 0))
				0: rand_req_type <= RDSEED_16;
				1: rand_req_type <= RDRAND_16;
				2: rand_req_type <= RDSEED_32;
				3: rand_req_type <= RDRAND_32;
				4: rand_req_type <= RDSEED_64;
				5: rand_req_type <= RDRAND_64;
				default: rand_req_type <= RDRAND_16;
			endcase
		end

	end

	//Monitor output pins, verify that no true_rand_validextra bytes are being served
	always_comb begin
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

        if(shorts_received == shorts_received_max) rand_req = 1'b0;
        else rand_req = 1'b1;
	end

	always_ff @(posedge slow_clk) begin
        if(shorts_received == shorts_received_max) shorts_received <= 0;
		else if(rand_valid) shorts_received <= shorts_received + 1;
	end 

	//Below are assertions that ensure no bad behavior at the host I/O pins

	// --- Assertion 1 ---
    // Ensures that while rand_valid is high, rand_byte can only change on the 
    // rising edge of slow_clk.

    property p_rand_byte_stable;
		@(posedge top_clk)
		disable iff ($rose(slow_clk))
        rand_valid |-> $stable(rand_byte);
    endproperty
    a_rand_byte_stable: assert property (p_rand_byte_stable) 
		else $fatal("rand_byte changed when not at posedge slow_clk");

    // --- Assertion 2 ---
    // Asserts that while rand_valid is high, rand_byte can never be all 0.
    // This could happen organically however
    property p_rand_byte_not_zero;
		@(posedge top_clk)
		disable iff ($rose(slow_clk) || $rose(rand_valid))
        rand_valid |-> (rand_byte !== '0);
    endproperty
    a_rand_byte_not_zero: assert property (p_rand_byte_not_zero) 
        else $warning("rand_byte was all zeros while rand_valid was high");

	// --- Assertion 3 ---
    // Asserts that while rand_valid is high, rand_byte can never be an unknown value.

    property p_rand_byte_not_unknown;
		@(posedge top_clk)
		disable iff ($rose(slow_clk) || $rose(rand_valid))
        rand_valid |-> (!$isunknown(rand_byte));
    endproperty
    a_rand_byte_not_unknown: assert property (p_rand_byte_not_unknown) 
        else $fatal("rand_byte was unknown ('x or 'z) while rand_valid was high");

    // Assertion 4
    // Asserts that an outstanding request takes no longer than 5000 ns to serve (otherwise it's a timeout)

    always begin
        @(posedge rand_req);
        fork
            #10000ns;
            @(negedge rand_req);
        join_any
        assert (rand_req == 1'b0 || debug == 1'b1)
        else $fatal(1, "ASIC TIMEOUT: 'rand_req' was held high for 5000ns at time without being in debug mode %t", $realtime);
        disable fork;
    end
	
	//Below are Tasks
	task reset_dut();
        $display("Applying reset...");
        top_reset = 1'b0;
        #5ns
		top_reset = 1'b1;
    endtask

    task assert_debug();
        $display("Asserting Debug Pin...");
        debug = 1'b1;
    endtask

    task de_assert_debug();
        $display("De-Asserting Debug Pin...");
        debug = 1'b0;
    endtask

	task spi_write_only(input logic [WORD_WIDTH-1:0] data_to_send);
        // Select the slave
        @(posedge debug_clk);
        ss_n = 0;
        #15;

        // Send data
        @(negedge debug_clk);
        for (int i=WORD_WIDTH-1; i>=0; i--) begin
            mosi = data_to_send[i]; // MSB first
            #10;
        end

        // Deselect the slave
        ss_n = 1;
        mosi = 0;
    endtask

    //------------------------------------------------------------------
    // Performs an SPI write-then-read transaction
    // Fills the 'master_received' variable in the testbench.
    //------------------------------------------------------------------
    task spi_write_read(input logic [WORD_WIDTH-1:0] data_to_send,
                        output logic [WORD_WIDTH-1:0] data_received);
        
        data_received = '0; // Clear old data

        // Select the slave
        @(posedge debug_clk);
        ss_n = 0;
        #15;

        // Send command
        @(negedge debug_clk);
        for (int i=WORD_WIDTH-1; i>=0; i--) begin
            mosi = data_to_send[i]; // MSB first
            #10;
        end

        #20; // Wait one cycle

        // Read data
        for (int i=WORD_WIDTH-1; i>=0; i--) begin
            data_received[i] = miso;
            #10;
        end

        // Deselect the slave
        ss_n = 1;
        mosi = 0;
    endtask

	// ------------------- Test reading from somewhere ----------------------
	task read_test
	(
		input read_cmd_name_e test_word
	);
		read_cmd_data_t current_struct;
        $display("\n --- Test: %s ---", test_word.name());

        // Call the task to perform the transaction
        spi_write_read(test_word, master_received);
		current_struct = READ_CMD_MAP[test_word.name()];

        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received == current_struct.exp_rsp) begin 
                $display("%s read test PASSED ✓!", test_word.name());
            end else begin
                $error("%s read test FAILED ✘: Expected %h", test_word.name(), current_struct.exp_rsp);
            end
        end else begin
            $display("%s read test FAILED ✘: data_ready not high at %t", test_word.name(), $realtime);
        end
        #20;

	endtask

	// ------------------- Try calibration bit write then read (Write then read reg 0x07) ----------------------
	task rw_calibration_bits ();
        $display("\n --- Test: Write Calibration Bits ---");
        test_word = 22'b1_0_0111_1100_0011_1100_0001; // Write 0xC3C1
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check result wait(spi_data_ready)
        wait (spi_data_ready); if (spi_data_ready) begin
            @(negedge spi_data_ready) // Wait for signal to go low
            $display("Internal Entropy Calibration Bits: %h", dut.mixed_IC.u_control.internal_entropy_calibration);
            if (dut.mixed_IC.u_control.internal_entropy_calibration == 16'hC3C1) begin 
                $display("Calibration bits write test PASSED ✓!");
            end else begin
                $error("Calibration bits write test FAILED ✘: Expected %h", 16'hC3C1);
            end
        end else begin
            $display("Calibration bits write test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #80;

		$display("\n --- Test: Read Calibration Bits ---");
        test_word = 22'b1_1_0111_0000_0000_0000_0000; // Read debug calibration bits

        spi_write_read(test_word, master_received);
        
        // Check results
        #1;

        if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.mixed_IC.u_control.internal_entropy_calibration) begin
                $display("Calibration bits read test PASSED ✓!");
            end else begin
                $error("Calibration bits read test FAILED ✘: Expected %h, Got %h", 
                         dut.mixed_IC.u_control.internal_entropy_calibration, master_received);
            end
        end else begin
            $display("Calibration bits read test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #20;
	endtask

	// ------------------- Try temp sensor 0 threshold write then read (Write then read reg 0x08) ----------------------
	task tempsensor0_rw ();
		$display("\n --- Test: Write temp sensor threshold 0 Bits ---");
        test_word = 22'b1010000000000000010001 ; // Write 0x280011
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            @(negedge spi_data_ready) // Wait for signal to go low
            $display("Internal temp sensor threshold 0 Bits: %h", dut.mixed_IC.u_control.internal_temp_threshold_0);
            if (dut.mixed_IC.u_control.internal_temp_threshold_0 == 16'h0011) begin
                $display("Internal temp sensor threshold 0 bits write test PASSED ✓!");
            end else begin
                $error("Internal temp sensor threshold 0 bits write test FAILED ✘: Expected %h", 16'h0011);
            end
        end else begin
            $display("Internal temp sensor threshold 0 bits write test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #80;

        
        $display("\n --- Test: Read temp sensor threshold 0 Bits ---");
        test_word = 22'b1110000000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.mixed_IC.u_control.internal_temp_threshold_0) begin
                $display("Internal temp sensor threshold 0 bits read test PASSED ✓!");
            end else begin
                $error("Internal temp sensor threshold 0 bits read FAILED ✘: Expected %h, Got %h", 
                         dut.mixed_IC.u_control.internal_temp_threshold_0, master_received);
            end
        end else begin
            $display("Internal temp sensor threshold 0 bits read test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #20;
	endtask

	// ------------------- Try temp sensor 1 threshold write then read (Write then read reg 0x09) ----------------------
	task tempsensor1_rw ();
		$display("\n --- Test: Write temp sensor threshold 1 Bits ---");
        test_word = 22'b1010010000000000000111 ; 
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            @(negedge spi_data_ready) // Wait for signal to go low
            $display("Internal temp sensor threshold 1 Bits: %h", dut.mixed_IC.u_control.internal_temp_threshold_1);
            if (dut.mixed_IC.u_control.internal_temp_threshold_1 == 16'h0007) begin
                $display("Internal temp sensor threshold 1 bits write test PASSED ✓!");
            end else begin
                $error("Internal temp sensor threshold 1 bits write test FAILED ✘: Expected %h", 16'h0007);
            end
        end else begin
            $display("Internal temp sensor threshold 1 bits write test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #80;

        
        $display("\n --- Test: Read temp sensor threshold 1 Bits ---");
        test_word = 22'b1110010000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.mixed_IC.u_control.internal_temp_threshold_1) begin
                $display("Internal temp sensor threshold 1 bits read test PASSED ✓!");
            end else begin
                $error("Internal temp sensor threshold 1 bits read FAILED ✘: Expected %h, Got %h", 
                         dut.mixed_IC.u_control.internal_temp_threshold_1, master_received);
            end
        end else begin
            $display("Internal temp sensor threshold 1 bits read test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #20;
	endtask

	// ------------------- Try temp sensor 2 threshold write then read (Write then read reg 0x0A) ----------------------
	task tempsensor2_rw ();
		$display("\n --- Test: Write temp sensor threshold 2 Bits ---");
        test_word = 22'b1010100000000000000011 ; // Write 0x2A0003
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            @(negedge spi_data_ready) // Wait for signal to go low
            $display("Internal temp sensor threshold 2 Bits: %h", dut.mixed_IC.u_control.internal_temp_threshold_2);
            if (dut.mixed_IC.u_control.internal_temp_threshold_2 == 16'h0003) begin
                $display("Internal temp sensor threshold 2 bits write test PASSED ✓!");
            end else begin
                $error("Internal temp sensor threshold 2 bits write test FAILED ✘: Expected %h", 16'h0003);
            end
        end else begin
            $display("Internal temp sensor threshold 2 bits write test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #80;

        
        $display("\n --- Test: Read temp sensor threshold 2 Bits ---");
        test_word = 22'b1010100000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.mixed_IC.u_control.internal_temp_threshold_2) begin
                $display("Internal temp sensor threshold 2 bits write test PASSED ✓!");
            end else begin
                $error("Internal temp sensor threshold 2 bits write FAILED ✘: Expected %h, Got %h", 
                         dut.mixed_IC.u_control.internal_temp_threshold_2, master_received);
            end
        end else begin
            $display("Internal temp sensor threshold 2 bits write test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #20;
	endtask

	// ------------------- Try temp sensor 3 threshold write then read (Write then read reg 0x0B) ----------------------
	task tempsensor3_rw ();
		$display("\n --- Test: Write temp sensor threshold 3 Bits ---");
        test_word = 22'b1010110000000000000101; // Write 0x2B0005
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            @(negedge spi_data_ready) // Wait for signal to go low
            $display("Internal temp sensor threshold 3 Bits: %h", dut.mixed_IC.u_control.internal_temp_threshold_3);
            if (dut.mixed_IC.u_control.internal_temp_threshold_3 == 16'h0005) begin
                $display("Internal temp sensor threshold 3 bits write test PASSED ✓!");
            end else begin
                $error("Internal temp sensor threshold 3 bits write test FAILED ✘: Expected %h", 16'h0005);
            end
        end else begin
            $display("Internal temp sensor threshold 3 bits write test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #80;

        
        $display("\n --- Test: Read temp sensor threshold 3 Bits ---");
        test_word = 22'b1110110000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.mixed_IC.u_control.internal_temp_threshold_3) begin
                $display("Internal temp sensor threshold 3 bits write test PASSED ✓!");
            end else begin
                $error("Internal temp sensor threshold 3 bits write FAILED ✘: Expected %h, Got %h", 
                         dut.mixed_IC.u_control.internal_temp_threshold_3, master_received);
            end
        end else begin
            $display("Internal temp sensor threshold 3 bits write test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #20;

	endtask

	// ------------------- Test reading from temp counter 0  (Write then read reg 0x0C) ----------------------
	task tempctr0_rw ();
		$display("\n --- Test: Read Temp Counter 0 ---");
        test_word = 22'b1_1_1100_0000_0000_0000_0000;
        
        // Call the task to perform the transaction
        spi_write_read(test_word, master_received);

        // Check results
        wait (spi_data_ready);if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $error("TX Test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #20;
	endtask

	// ------------------- Test reading from temp counter 1 (Write then read reg 0x0D) ----------------------
	task tempctr1_rw ();
		$display("\n --- Test: Read Temp Counter 1 ---");
        test_word = 22'b1_1_1101_0000_0000_0000_0000;
        
        spi_write_read(test_word, master_received);

        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #20;
	endtask

	// ------------------- Test reading from temp counter 2 (Write then read reg 0x0E) ----------------------
	task tempctr2_rw();
		$display("\n --- Test: Read Temp Counter 2 ---");
        test_word = 22'b1_1_1110_0000_0000_0000_0000;
        
        spi_write_read(test_word, master_received);

        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #20;
	endtask

	task tempctr3_rw();
		$display("\n --- Test: Read Temp Counter 3 ---");
        test_word = 22'b1_1_1111_0000_0000_0000_0000;
        
        spi_write_read(test_word, master_received);

        // Check results
        wait (spi_data_ready); if (spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high at %t", $realtime);
        end
        #20;
	endtask

    task conditioner_debug_test();
        $display("\n --- Test: Isolate and Drive Conditioner ---");

        test_word = 22'b0100101000000011100000;
        conditioner_serial_input = 384'h7b3a9f0e5c6d2814b7f8c9d0a3e5b6f7a8c9d0e1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c2e3f4a5b6c7d8e9f;
        spi_write_only(test_word);

        wait(spi_data_ready);

        if(
            dut.mixed_IC.conditioner_0.debug_register == 7'b110_0000
            && dut.mixed_IC.conditioner_0.debug_cond == 1'b1
            && dut.mixed_IC.conditioner_0.debug_ctr != '0
        ) begin
            $display("Isolate Conditioner Passed ✓");
        end else begin
            $error("Isolate Conditioner Failed ✘");
        end

        for (int i=0; i <= 383; i++) begin
            entropy_source_array[42] = conditioner_serial_input[i];
            @(posedge top_clk);
        end

    endtask

    task run_random_debug_test();   
        
        int rand_choice;

        rand_choice = $urandom_range(8, 0);

        
        case(rand_choice)
            0: rw_calibration_bits();
            1: tempsensor0_rw();
            2: tempsensor1_rw();
            3: tempsensor2_rw();
            4: tempsensor3_rw();
            5: tempctr0_rw();
            6: tempctr1_rw();
            7: tempctr2_rw();
            8: tempctr3_rw();
            9: conditioner_debug_test();
        endcase

    endtask



	//Main loop -> drive reset, drive normal behavior, and also randomly test DFT tasks intermittently.
	initial begin
		$fsdbDumpfile("top_io_dump.fsdb");
		$fsdbDumpvars(0, "+all");
		reset_dut();
		#5000ns
        assert_debug();
        conditioner_debug_test();
        // repeat (50) begin
        //     reset_dut();
        //     #500;
        //     run_random_debug_test(); 
        // end
        de_assert_debug();
        #5000ns
		$finish();
	end

endmodule
