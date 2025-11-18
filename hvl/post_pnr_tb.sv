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
		READ_LATCH_LS: 		'{cmd: 22'b1100110000000000000000, exp_rsp: '0},
		READ_LATCH_MS: 		'{cmd: 22'b1101000000000000000000, exp_rsp: '0},
		READ_JITTER_LS: 	'{cmd: 22'b1101010000000000000000, exp_rsp: '0},
		READ_JITTER_MS: 	'{cmd: 22'b1101100000000000000000, exp_rsp: '0}
	};

	// Clock generation
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
    logic [255:0] drbg_serial_input;

	//Drive clocks
	initial begin
        top_clk = 0;
        forever #20 top_clk = ~top_clk; 
    end

	top_io dut(
		// CLK+RST
		.ic_clk_io(top_clk),
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
    end
	//Drive entropy pins (pretend to be entropy)
    always_ff @(posedge top_clk) begin
        entropy_source_array <= {$urandom(), $urandom()} & permanent_entropy_mask;
    end

    always_comb begin
        if(debug) entropy = entropy_debug;
        else entropy = entropy_source_array;
        entropy = entropy_source_array;
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
    int ctr;

	always_ff @(posedge slow_clk or negedge top_reset) begin
        if(!top_reset) begin
            rand_req <= 1'b0;
            request_outstanding <= 1'b0;
            shorts_received <= 0;
            ctr <= 0;
        end else begin
            if(!request_outstanding || shorts_received == shorts_received_max || ctr > 500) begin 
                rand_req <= 1'b1;
                request_outstanding <= 1'b1;
                shorts_received <= 0;
                instr_select <= $urandom_range(5, 0);
                ctr <= 0;
            end else begin
                rand_req <= '0;
                instr_select <= 6;
                if(debug) ctr <= ctr + 1;
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
		@(posedge top_clk)
		disable iff ($rose(slow_clk))
        rand_valid |-> $stable(rand_byte);
    endproperty
    a_rand_byte_stable: assert property (p_rand_byte_stable) 
		else $fatal("rand_byte changed when not at posedge slow_clk");

    // --- Assertion 2 ---
    // Asserts that while rand_valid is high, rand_byte can never be all 0.
    // This could happen organically however if you are really unlucky (or just de-asserted debug) so it's a warning
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

    // initial begin : timeout_check_block // Use a named block for clarity
    //     // Loop continuously until the 'debug' signal is set
    //     forever begin
    //         // 1. Check the disable condition *before* proceeding
    //         if (debug) begin
    //             $display("--- Assertion 4 Permanently Disabled: Debug mode active at time %t ---", $realtime);
    //             break; // Exit the forever loop permanently
    //         end
    //         // 2. Wait for the starting condition
    //         @(posedge rand_req);
    //         // 3. Immediately check the disable condition again (in case 'debug' went high at the same time)
    //         if (debug) begin
    //             break; // Exit loop
    //         end
    //         // 4. Start the timeout detection
    //         fork
    //             #10000ns;     
    //             @(negedge rand_req);  
    //         join_any
    //         assert (rand_req == 1'b0)
    //         else $fatal(1, "ASIC TIMEOUT: 'rand_req' was held high for 10000ns at time %t", $realtime);
            
    //         disable fork;
    //     end
    // end : timeout_check_block
	
	//Below are Tasks
	task reset_dut();
        $display("Applying reset...");
        top_reset = 1'b1;
        repeat(2) @(posedge top_clk);
        top_reset = 1'b0;
        repeat(10) @(posedge top_clk);
		top_reset = 1'b1;
    endtask

    logic test;

    task init();
        entropy_debug = '0;
        io_temp_debug = '0;
        input_pin_1 = '0;
        output_to_input_direct = '0;
        mosi = '0;
        ss_n = '1;
        test = '0;
    endtask

    task assert_debug();
        $display("Asserting Debug Pin...");
        debug = 1'b1;
    endtask

    task de_assert_debug();
        $display("De-Asserting Debug Pin...");
        debug = 1'b0;
    endtask

    int timeout_count = 0;

    task wait_spi_ready_delay();

        // Reset counter before starting the wait
        timeout_count = 0;

        repeat(10) begin
            if (spi_data_ready) begin
                // Success: spi_data_ready asserted. Exit the loop.
                $display("SPI data ready detected after %0d cycles.", timeout_count);
                break; 
            end
            
            // Wait for the next clock edge and increment the counter
            @(posedge top_clk); 
            timeout_count = timeout_count + 1;

            // Check if the loop completed due to timeout (i.e., spi_data_ready never asserted)
            if (timeout_count == 10) begin
                // Failure: Timeout reached without seeing spi_data_ready
                $error(1, "TIMEOUT ERROR: spi_data_ready did not assert within the 10-cycle limit.");
            end
        end
    
    endtask

	task spi_write_only(input logic [WORD_WIDTH-1:0] data_to_send);
        // Select the slave
        ss_n = 0;
        @(posedge top_clk);

        // Send data
        for (int i=WORD_WIDTH-1; i>=0; i--) begin
            mosi = data_to_send[i]; // MSB first
            @(posedge top_clk);
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

        // Select the slave
        data_received = '0; // Clear old data
        ss_n = 0;
        @(posedge top_clk);

        // Send command
        for (int i=WORD_WIDTH-1; i>=0; i--) begin
            mosi = data_to_send[i]; // MSB first
            @(posedge top_clk);
        end

        repeat(4) @(posedge top_clk);

        // Read data
        for (int i=WORD_WIDTH-1; i>=0; i--) begin
            test = 1'b1;
            data_received[i] = miso;
            if(i == 1) ss_n = 1;
            @(posedge top_clk);
        end

        test = 1'b0;

        // Deselect the slave
        $display("spi_read_write done  ", $realtime);

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
        wait_spi_ready_delay();

        $display("Data received by master: %h", master_received);
        if (master_received == current_struct.exp_rsp) begin 
            $display("%s read test PASSED ✓!", test_word.name());
        end else begin
            $error("%s read test FAILED ✘: Expected %h", test_word.name(), current_struct.exp_rsp);
        end

	endtask

	// ------------------- Try calibration bit write then read (Write then read reg 0x07) ----------------------
	task rw_calibration_bits ();
        $display("\n --- Test: Write Calibration Bits ---");
        test_word = 22'b1_0_0111_0000_1000_0010_0001; // Write 0x821
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check result
        wait_spi_ready_delay();

        // $display("Internal Entropy Calibration Bits: %h", dut.mixed_IC.u_control.internal_entropy_calibration);
        // if (dut.mixed_IC.u_control.internal_entropy_calibration == 12'h821) begin 
        //     $display("Calibration bits write test PASSED ✓!");
        // end else begin
        //     $error("Calibration bits write test FAILED ✘: Expected %h ", 12'h821, $realtime);
        // end

		$display("\n --- Test: Read Calibration Bits ---");
        test_word = 22'b1_1_0111_0000_0000_0000_0000; // Read debug calibration bits

        spi_write_read(test_word, master_received);
        
        // Check results
        wait_spi_ready_delay();

        $display("Data received by master: %h", master_received);
        // if (master_received[15:0] == dut.mixed_IC.u_control.internal_entropy_calibration) begin
        //     $display("Calibration bits read test PASSED ✓!");
        // end else begin
        //     $error("Calibration bits read test FAILED ✘: Expected %h, Got %h", 
        //                 dut.mixed_IC.u_control.internal_entropy_calibration, master_received, $realtime);
        // end

	endtask

	// ------------------- Try temp sensor 0 threshold write then read (Write then read reg 0x08) ----------------------
	task tempsensor0_rw ();
		$display("\n --- Test: Write temp sensor threshold 0 Bits ---");
        test_word = 22'b1010000000000000010001 ; // Write 0x280011
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        wait_spi_ready_delay();

        // $display("Internal temp sensor threshold 0 Bits: %h", dut.mixed_IC.u_control.internal_temp_threshold_0);
        // if (dut.mixed_IC.u_control.internal_temp_threshold_0 == 16'h0011) begin
        //     $display("Internal temp sensor threshold 0 bits write test PASSED ✓!");
        // end else begin
        //     $error("Internal temp sensor threshold 0 bits write test FAILED ✘: Expected %h", 16'h0011);
        // end

        
        $display("\n --- Test: Read temp sensor threshold 0 Bits ---");
        test_word = 22'b1110000000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        wait_spi_ready_delay();

        $display("Data received by master: %h", master_received);
        // if (master_received[15:0] == dut.mixed_IC.u_control.internal_temp_threshold_0) begin
        //     $display("Internal temp sensor threshold 0 bits read test PASSED ✓!");
        // end else begin
        //     $error("Internal temp sensor threshold 0 bits read FAILED ✘: Expected %h, Got %h", 
        //                 dut.mixed_IC.u_control.internal_temp_threshold_0, master_received);
        // end

	endtask

	// ------------------- Try temp sensor 1 threshold write then read (Write then read reg 0x09) ----------------------
	task tempsensor1_rw ();
		$display("\n --- Test: Write temp sensor threshold 1 Bits ---");
        test_word = 22'b1010010000000000000111 ; 
        
        // Call the write-only task
        spi_write_only(test_word);
        
        wait_spi_ready_delay();

        // $display("Internal temp sensor threshold 1 Bits: %h", dut.mixed_IC.u_control.internal_temp_threshold_1);
        // if (dut.mixed_IC.u_control.internal_temp_threshold_1 == 16'h0007) begin
        //     $display("Internal temp sensor threshold 1 bits write test PASSED ✓!");
        // end else begin
        //     $error("Internal temp sensor threshold 1 bits write test FAILED ✘: Expected %h", 16'h0007);
        // end


        $display("\n --- Test: Read temp sensor threshold 1 Bits ---");
        test_word = 22'b1110010000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        wait_spi_ready_delay();

        // Check results
        // $display("Data received by master: %h", master_received);
        // if (master_received[15:0] == dut.mixed_IC.u_control.internal_temp_threshold_1) begin
        //     $display("Internal temp sensor threshold 1 bits read test PASSED ✓!");
        // end else begin
        //     $error("Internal temp sensor threshold 1 bits read FAILED ✘: Expected %h, Got %h", 
        //                 dut.mixed_IC.u_control.internal_temp_threshold_1, master_received);
        // end

	endtask

	// ------------------- Try temp sensor 2 threshold write then read (Write then read reg 0x0A) ----------------------
	task tempsensor2_rw ();
		$display("\n --- Test: Write temp sensor threshold 2 Bits ---");
        test_word = 22'b1010100000000000000011 ; // Write 0x2A0003
        
        // Call the write-only task
        spi_write_only(test_word);

        wait_spi_ready_delay();
        
        // Check results
        // $display("Internal temp sensor threshold 2 Bits: %h", dut.mixed_IC.u_control.internal_temp_threshold_2);
        // if (dut.mixed_IC.u_control.internal_temp_threshold_2 == 16'h0003) begin
        //     $display("Internal temp sensor threshold 2 bits write test PASSED ✓!");
        // end else begin
        //     $error("Internal temp sensor threshold 2 bits write test FAILED ✘: Expected %h", 16'h0003);
        // end

        
        $display("\n --- Test: Read temp sensor threshold 2 Bits ---");
        test_word = 22'b1010100000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        wait_spi_ready_delay();

        // Check results
        $display("Data received by master: %h", master_received);
        // if (master_received[15:0] == dut.mixed_IC.u_control.internal_temp_threshold_2) begin
        //     $display("Internal temp sensor threshold 2 bits write test PASSED ✓!");
        // end else begin
        //     $error("Internal temp sensor threshold 2 bits write FAILED ✘: Expected %h, Got %h", 
        //                 dut.mixed_IC.u_control.internal_temp_threshold_2, master_received);
        // end

	endtask

	// ------------------- Try temp sensor 3 threshold write then read (Write then read reg 0x0B) ----------------------
	task tempsensor3_rw ();
		$display("\n --- Test: Write temp sensor threshold 3 Bits ---");
        test_word = 22'b1010110000000000000101; // Write 0x2B0005
        
        // Call the write-only task
        spi_write_only(test_word);

        wait_spi_ready_delay();
        
        // Check results
        // $display("Internal temp sensor threshold 3 Bits: %h", dut.mixed_IC.u_control.internal_temp_threshold_3);
        // if (dut.mixed_IC.u_control.internal_temp_threshold_3 == 16'h0005) begin
        //     $display("Internal temp sensor threshold 3 bits write test PASSED ✓!");
        // end else begin
        //     $error("Internal temp sensor threshold 3 bits write test FAILED ✘: Expected %h", 16'h0005);
        // end


        
        $display("\n --- Test: Read temp sensor threshold 3 Bits ---");
        test_word = 22'b1110110000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        // Check results
        wait_spi_ready_delay();
        $display("Data received by master: %h", master_received);
        // if (master_received[15:0] == dut.mixed_IC.u_control.internal_temp_threshold_3) begin
        //     $display("Internal temp sensor threshold 3 bits write test PASSED ✓!");
        // end else begin
        //     $error("Internal temp sensor threshold 3 bits write FAILED ✘: Expected %h, Got %h", 
        //                 dut.mixed_IC.u_control.internal_temp_threshold_3, master_received);
        // end

	endtask

	// ------------------- Test reading from temp counter 0  (Write then read reg 0x0C) ----------------------
	task tempctr0_rw ();
		$display("\n --- Test: Read Temp Counter 0 ---");
        test_word = 22'b1_1_1100_0000_0000_0000_0000;
        
        // Call the task to perform the transaction
        spi_write_read(test_word, master_received);

        wait_spi_ready_delay();
        
        $display("Data received by master: %h", master_received);

	endtask

	// ------------------- Test reading from temp counter 1 (Write then read reg 0x0D) ----------------------
	task tempctr1_rw ();
		$display("\n --- Test: Read Temp Counter 1 ---");
        test_word = 22'b1_1_1101_0000_0000_0000_0000;
        
        spi_write_read(test_word, master_received);

        wait_spi_ready_delay();

        $display("Data received by master: %h", master_received);

	endtask

	// ------------------- Test reading from temp counter 2 (Write then read reg 0x0E) ----------------------
	task tempctr2_rw();
		$display("\n --- Test: Read Temp Counter 2 ---");
        test_word = 22'b1_1_1110_0000_0000_0000_0000;
        
        spi_write_read(test_word, master_received);
        wait_spi_ready_delay();
        
        $display("Data received by master: %h", master_received);

	endtask

	task tempctr3_rw();
		$display("\n --- Test: Read Temp Counter 3 ---");
        test_word = 22'b1_1_1111_0000_0000_0000_0000;
        
        spi_write_read(test_word, master_received);

        wait_spi_ready_delay();

        $display("Data received by master: %h", master_received);

	endtask

    //asserts that within ten cycles, serial_input does something
    // property serial_input_goes_high;
    //     @(posedge top_clk) (dut.mixed_IC.conditioner_0.serial_input [=0:9]);
    // endproperty

    task conditioner_debug_test();
        $display("\n --- Test: Isolate and Drive Conditioner ---");

        test_word = 22'b0100101000000011100000;
        conditioner_serial_input = 384'h7b3a9f0e5c6d2814b7f8c9d0a3e5b6f7a8c9d0e1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c2e3f4a5b6c7d8e9f;
        spi_write_only(test_word);

        wait_spi_ready_delay();
        repeat(2) @(posedge top_clk);

        // if(
        //     dut.mixed_IC.conditioner_0.debug_register == 7'b110_0000
        //     && dut.mixed_IC.conditioner_0.debug_cond == 1'b1
        //     && dut.mixed_IC.conditioner_0.debug_ctr != '0
        // ) begin
        //     $display("Isolate Conditioner Passed ✓");
        // end else begin
        //     $error("Isolate Conditioner Failed ✘");
        // end

        for (int i=0; i <= 383; i++) begin
            input_pin_1 = conditioner_serial_input[i];
            @(posedge top_clk);
        end
    endtask

    task output_buffer_debug_test();
        $display("\n --- Test: Write Output Buffer Control Bits ---");

        test_word = 22'b1000100000000000100001;

        spi_write_only(test_word);

        wait_spi_ready_delay();
        @(posedge top_clk);

        // if(     dut.mixed_IC.output_buffer_inst.debug == 1'b1
        //     &&  dut.mixed_IC.output_buffer_inst.output_buffer_control == test_word[5:0]
        //     &&  dut.mixed_IC.output_buffer_inst.triv_mode_true == 1'b1
        // ) begin
        //     $display("Output Buffer Debug Mode Active ✓");
        // end else begin
        //     $error("Output Buffer Debug Mode Inactive ✘");
        // end

        @(posedge top_clk);

        $display("\n --- Test: Read Output Buffer Control Bits ---");
        test_word = 22'b1100100000000000000000; // Read output buffer control bits

        spi_write_read(test_word, master_received);

        wait_spi_ready_delay();

        // $display("Data received by master: %h", master_received);
        // if (master_received[15:0] == dut.mixed_IC.u_control.output_buffer_control_reg) begin
        //     $display("Output buffer control bits read test PASSED ✓!");
        // end else begin
        //     $display("Output buffer control read test FAILED ✘: Expected %h, Got %h",
        //                 dut.mixed_IC.u_control.output_buffer_control_reg, master_received);
        // end
        
    endtask

    task bypass_oht();
        // // ---------------- Set output 2 to jitter entropy source 10, output 1 to clk, output to input into conditioner
        $display("\n --- Test: jitter entropy source 10, directly into conditioner ---");
        output_to_input_direct = 1'b1;

        // Set up the command and the serial data
        test_word = 22'b0100101000000011100000;
        conditioner_serial_input = 384'h7b3a9f0e5c6d2814b7f8c9d0a3e5b6f7a8c9d0e1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c2e3f4a5b6c7d8e9f;
        spi_write_only(test_word);

        // Check results
        wait_spi_ready_delay();
        @(posedge top_clk);

        // $display("Next state: %h", dut.mixed_IC.u_control.curr_state); 
        
        // if (dut.mixed_IC.u_control.next_state == test_word) begin
        //     $display("Next state Test PASSED ✓!");
        // end else begin
        //     $error("Next state FAILED ✘: Expected %h", test_word);
        // end
        

        // Now, send the serial data on input_pin_1, driven by the main clock
        for (int i=0; i<=383; i++) begin
            entropy_debug[42] = conditioner_serial_input[i]; // MSB first
            @(posedge top_clk);
        end

        output_to_input_direct = 1'b0;
    endtask


    task drbg_debug_test();
        $display("\n --- Test: AES_DRBG Debug Mode via input_pin_1 ---");

        test_word = 22'b0_00_00000_00_00001_11_00010;
        drbg_serial_input = 256'hf3c8e4b1d72a9c0f54ab19de8837f4c2bb10e9df4372a6cc91ef02d7a54bc810;

        spi_write_only(test_word);

        wait_spi_ready_delay();
        @(posedge top_clk);

        // $display("Next state: %h", dut.mixed_IC.u_control.curr_state); 

        // if (dut.mixed_IC.u_control.next_state == test_word) begin
        //     $display("Next state Test PASSED ✓!");
        // end else begin
        //     $error("Next state FAILED ✘: Expected %h", test_word);
        // end

        // if(     dut.mixed_IC.u_drbg_rappin.drbg_debug_mode_i == 1'b1
        // ) begin
        //     $display("DBRG Debug Mode Active ✓");
        // end else begin
        //     $error("DRBG Debug Mode Inactive ✘");
        // end
        
        for (int i=0; i<=255; i++) begin
            input_pin_1 = drbg_serial_input[i];
            @(posedge top_clk);
        end
    endtask

    task run_random_debug_test();   
        
        int rand_choice;

        rand_choice = $urandom_range(12, 0);

        
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
            10: bypass_oht();
            11: output_buffer_debug_test();
            12: drbg_debug_test();
        endcase

    endtask



	//Main loop -> drive reset, drive normal behavior, and also randomly test DFT tasks intermittently.
	initial begin
		$fsdbDumpfile("post_pnr_dump.fsdb");
		$fsdbDumpvars(0, "+all");
        init();
		reset_dut();
        repeat(100) @(posedge top_clk);

        assert_debug();
        output_buffer_debug_test();
        repeat(1000) @(posedge top_clk);
        drbg_debug_test();
        repeat(50_000) @(posedge top_clk);
        de_assert_debug();

        // assert_debug();
        // repeat(100) @(posedge top_clk);
        // repeat (100) begin
        //     run_random_debug_test(); 
        //     @(posedge top_clk);
        // end
        // de_assert_debug();

        //repeat(1_000_000) @(posedge top_clk);

		$finish();
	end

endmodule
