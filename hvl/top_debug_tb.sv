`timescale 1ns/1ps
// This is your testbench module
import params::*;
import le_types::*;

typedef struct packed {
    logic [4:0] input_pin_mux_cell_sel;     // curr_state[4:0]
    logic [1:0] input_pin_mux_mod_sel;      // curr_state[6:5]
    logic [4:0] out_pin_mux1_cell_sel;      // curr_state[11:7]
    logic [1:0] out_pin_mux1_mod_sel;       // curr_state[13:12]
    logic [4:0] out_pin_mux2_cell_sel;      // curr_state[18:14]
    logic [1:0] out_pin_mux2_mod_sel;       // curr_state[20:19]
    logic       mux_sel_reg_op;             // curr_state[21]
} cmd_state_t;


module top_debug_tb;

    // Parameters
    localparam word_width = 5'd22; // This param is in your TB, but not used by 'top'
    
    // NOTE: You must define the parameters and types used by the 'top' module's
    // port list. They are likely in a file like "types.sv".
    // For this example, I will assume some definitions.
    // Make sure to `include the file that defines them, e.g.:
    // `include "types.sv" 

    

    // --- 1. Define Testbench Signals ---
    
    // Signals to drive DUT inputs
    logic tb_ic_clk;
    logic tb_rst_n;
    logic tb_rand_req;
    rand_req_t tb_rand_req_type;
    logic tb_ss_n;
    logic tb_debug_clk;
    logic tb_mosi;
    logic tb_debug;
    logic tb_output_to_input_direct;
    logic tb_input_pin_1;
    logic [3:0] tb_temp_sens_in;
    logic tb_io_temp_debug;
    logic [es_sources-1:0] tb_entropy_source_array;

    // Signals to monitor DUT outputs
    logic [OUTPUT_WIDTH-1:0] tb_rand_byte;
    logic tb_rand_valid;
    logic tb_slow_clk;
    logic tb_miso;
    logic tb_spi_data_ready;
    logic tb_output_pin_2;
    logic tb_output_pin_1;
    logic [latch_sources-1:0][calib_bits-1:0] tb_arr_n;
    logic [latch_sources-1:0][calib_bits-1:0] tb_arr_p;
    logic [jitter_sources-1:0] tb_jitter_disable_arr;


    // --- 2. Instantiate the Device Under Test (DUT) ---
    // We use named port connections (.port_name(signal_name))
    // for clarity and to avoid mistakes.
    top dut (
        // CLK+RST
        .ic_clk(tb_ic_clk),
        .rst_n(tb_rst_n),

        // CPU I/O
        .rand_req(tb_rand_req),
        .rand_req_type(tb_rand_req_type),
        .rand_byte(tb_rand_byte),
        .rand_valid(tb_rand_valid),
        .slow_clk(tb_slow_clk),
        
        // SPI Pins
        .ss_n(tb_ss_n),
        .debug_clk(tb_debug_clk),
        .mosi(tb_mosi),
        .miso(tb_miso),
        .spi_data_ready(tb_spi_data_ready),

        // Debug
        .debug(tb_debug),
        .output_to_input_direct(tb_output_to_input_direct),

        // Serial I/O for debug
        .output_pin_2(tb_output_pin_2),
        .output_pin_1(tb_output_pin_1),
        .input_pin_1(tb_input_pin_1),

        // Temperature sensor I/O
        .temp_sens_in(tb_temp_sens_in),
        .io_temp_debug(tb_io_temp_debug),

        // Temp pins for verification
        .entropy_source_array(tb_entropy_source_array),
        .arr_n(tb_arr_n),
        .arr_p(tb_arr_p),
        .jitter_disable_arr(tb_jitter_disable_arr)
    );


    // Clock generation (SPI clock)
    logic debug_clk;
    logic ic_clk;
    initial begin
        
        tb_debug_clk = 0;
        forever #5 tb_debug_clk = ~tb_debug_clk; // 100 MHz clock
    end

    initial begin
        tb_ic_clk = 0;
        forever #5 tb_ic_clk = ~tb_ic_clk; // 100 MHz clock
    end

    initial begin
        tb_rst_n = 0;
        #100ns;
        tb_rst_n = 1;
    end

    logic [21:0] test_word;
    logic [21:0] fake_input;
    logic [21:0] master_received;

    logic [383:0] conditioner_serial_input;

    // --- 0. Functions
    task reset_dut();
        $display("Applying reset...");
        tb_input_pin_1 = 0;
        // tb_rst_n = 0;
        tb_ss_n = 1; // Not selected
        tb_mosi = 0;
        tb_debug = 0;

        #20;
        // tb_rst_n = 1;
        tb_debug = 1'b1;
        #10;
    endtask
    
    task spi_write_only(input logic [word_width-1:0] data_to_send);
        // Select the slave
        @(posedge tb_debug_clk);
        tb_ss_n = 0;
        #15;

        // Send data
        @(negedge tb_debug_clk);
        for (int i=word_width-1; i>=0; i--) begin
            tb_mosi = data_to_send[i]; // MSB first
            #10;
        end

        // Deselect the slave
        tb_ss_n = 1;
        tb_mosi = 0;
    endtask

    //------------------------------------------------------------------
    // Performs an SPI write-then-read transaction
    // Fills the 'master_received' variable in the testbench.
    //------------------------------------------------------------------
    task spi_write_read(input logic [word_width-1:0] data_to_send,
                        output logic [word_width-1:0] data_received);
        
        data_received = '0; // Clear old data

        // Select the slave
        @(posedge tb_debug_clk);
        tb_ss_n = 0;
        #15;

        // Send command
        @(negedge tb_debug_clk);
        for (int i=word_width-1; i>=0; i--) begin
            tb_mosi = data_to_send[i]; // MSB first
            #10;
        end

        #20; // Wait one cycle

        // Read data
        for (int i=word_width-1; i>=0; i--) begin
            data_received[i] = tb_miso;
            #10;
        end

        // Deselect the slave
        tb_ss_n = 1;
        tb_mosi = 0;
    endtask
    
    // Test sequence
    initial begin

        $fsdbDumpfile("top_debug_tb.fsdb");
        $fsdbDumpvars(0, "+all");

        // Apply initial reset
        reset_dut();
        master_received = 1'b0;
        tb_io_temp_debug = 1'b0;
        #80;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Test reading DEFAULT STATE (Read reg 0x00) ----------------------
        $display("\n --- Test: Read DEFAULT STATE ---");
        test_word = 22'b1100000000000000000000 ;
        
        // Call the task to perform the transaction
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received == 22'b0000000000000000000000) begin 
                $display("DEFAULT STATE read test PASSED ✓!");
            end else begin
                $display("DEFAULT STATE read test FAILED ✘: Expected %h", 22'h000000);
            end
        end else begin
            $display("DEFAULT STATE read test FAILED ✘: data_ready not high");
        end
        #20;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

// ------------------- Test reading HALT STATE (Read reg 0x01)----------------------
        $display("\n --- Test: Read HALT STATE ---");
        test_word = 22'b1100010000000000000000;
        
        // Call the task to perform the transaction
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received == 22'hED_BEF) begin 
                $display("HALT STATE read test PASSED ✓!");
            end else begin
                $display("HALT STATE read test FAILED ✘: Expected %h", 22'hED_BEF);
            end
        end else begin
            $display("HALT STATE read test FAILED ✘: data_ready not high");
        end
        #20;



///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////



        // ------------------- Test reading from Entropy Latch Status [0-15] (Read reg 0x03) ----------------------
 
        $display("\n --- Test: Read Entropy Latch Status [0-15] ---");
        test_word = 22'b1100110000000000000000;
        
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high");
        end
        #20;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Test reading from Entropy Latch Status [16-31] (Read reg 0x04) ----------------------
 
        $display("\n --- Test: Read Entropy Latch Status [16-31] ---");
        test_word = 22'b1101000000000000000000;
        
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high");
        end
        #20;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Test reading from Entropy Jitter Status [0-15] (Read reg 0x05) ----------------------
 
        $display("\n --- Test: Read Entropy Jitter Status [0-15] ---");
        test_word = 22'b1101010000000000000000;
        
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high");
        end
        #20;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////


        // ------------------- Test reading from Entropy Jitter Status [16-31] (Read reg 0x06)----------------------
 
        $display("\n --- Test: Read Entropy Jitter Status [16-31] ---");
        test_word = 22'b1101100000000000000000;
        
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high");
        end
        #20;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Try calibration bit write then read (Write then read reg 0x07) ----------------------
        $display("\n --- Test: Write Calibration Bits ---");
        test_word = 22'b1_0_0111_1100_0011_1100_0001; // Write 0xC3C1
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        if (tb_spi_data_ready) begin
            @(negedge tb_spi_data_ready) // Wait for signal to go low
            $display("Internal Entropy Calibration Bits: %h", dut.u_control.internal_entropy_calibration);
            if (dut.u_control.internal_entropy_calibration == 16'hC3C1) begin 
                $display("Calibration bits write test PASSED ✓!");
            end else begin
                $display("Calibration bits write test FAILED ✘: Expected %h", 16'hC3C1);
            end
        end else begin
            $display("Calibration bits write test FAILED ✘: data_ready not high");
        end
        #80;

        
        $display("\n --- Test: Read Calibration Bits ---");
        test_word = 22'b1_1_0111_0000_0000_0000_0000; // Read debug calibration bits

        spi_write_read(test_word, master_received);
        
        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.u_control.internal_entropy_calibration) begin
                $display("Calibration bits read test PASSED ✓!");
            end else begin
                $display("Calibration bits read test FAILED ✘: Expected %h, Got %h", 
                         dut.u_control.internal_entropy_calibration, master_received);
            end
        end else begin
            $display("Calibration bits read test FAILED ✘: data_ready not high");
        end
        #20;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Try temp sensor 0 threshold write then read (Write then read reg 0x08) ----------------------
        $display("\n --- Test: Write temp sensor threshold 0 Bits ---");
        test_word = 22'b1010000000000000010001 ; // Write 0x280011
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        if (tb_spi_data_ready) begin
            @(negedge tb_spi_data_ready) // Wait for signal to go low
            $display("Internal temp sensor threshold 0 Bits: %h", dut.u_control.internal_temp_threshold_0);
            if (dut.u_control.internal_temp_threshold_0 == 16'h0011) begin
                $display("Internal temp sensor threshold 0 bits write test PASSED ✓!");
            end else begin
                $display("Internal temp sensor threshold 0 bits write test FAILED ✘: Expected %h", 16'h0011);
            end
        end else begin
            $display("Internal temp sensor threshold 0 bits write test FAILED ✘: data_ready not high");
        end
        #80;

        
        $display("\n --- Test: Read temp sensor threshold 0 Bits ---");
        test_word = 22'b1110000000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.u_control.internal_temp_threshold_0) begin
                $display("Internal temp sensor threshold 0 bits read test PASSED ✓!");
            end else begin
                $display("Internal temp sensor threshold 0 bits read FAILED ✘: Expected %h, Got %h", 
                         dut.u_control.internal_temp_threshold_0, master_received);
            end
        end else begin
            $display("Internal temp sensor threshold 0 bits read test FAILED ✘: data_ready not high");
        end
        #20;
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Try temp sensor 1 threshold write then read (Write then read reg 0x09) ----------------------
        $display("\n --- Test: Write temp sensor threshold 1 Bits ---");
        test_word = 22'b1010010000000000000111 ; 
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        if (tb_spi_data_ready) begin
            @(negedge tb_spi_data_ready) // Wait for signal to go low
            $display("Internal temp sensor threshold 1 Bits: %h", dut.u_control.internal_temp_threshold_1);
            if (dut.u_control.internal_temp_threshold_1 == 16'h0007) begin
                $display("Internal temp sensor threshold 1 bits write test PASSED ✓!");
            end else begin
                $display("Internal temp sensor threshold 1 bits write test FAILED ✘: Expected %h", 16'h0007);
            end
        end else begin
            $display("Internal temp sensor threshold 1 bits write test FAILED ✘: data_ready not high");
        end
        #80;

        
        $display("\n --- Test: Read temp sensor threshold 1 Bits ---");
        test_word = 22'b1110010000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.u_control.internal_temp_threshold_1) begin
                $display("Internal temp sensor threshold 1 bits read test PASSED ✓!");
            end else begin
                $display("Internal temp sensor threshold 1 bits read FAILED ✘: Expected %h, Got %h", 
                         dut.u_control.internal_temp_threshold_1, master_received);
            end
        end else begin
            $display("Internal temp sensor threshold 1 bits read test FAILED ✘: data_ready not high");
        end
        #20;

        
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Try temp sensor 2 threshold write then read (Write then read reg 0x0A) ----------------------
        $display("\n --- Test: Write temp sensor threshold 2 Bits ---");
        test_word = 22'b1010100000000000000011 ; // Write 0x2A0003
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        if (tb_spi_data_ready) begin
            @(negedge tb_spi_data_ready) // Wait for signal to go low
            $display("Internal temp sensor threshold 2 Bits: %h", dut.u_control.internal_temp_threshold_2);
            if (dut.u_control.internal_temp_threshold_2 == 16'h0003) begin
                $display("Internal temp sensor threshold 2 bits write test PASSED ✓!");
            end else begin
                $display("Internal temp sensor threshold 2 bits write test FAILED ✘: Expected %h", 16'h0003);
            end
        end else begin
            $display("Internal temp sensor threshold 2 bits write test FAILED ✘: data_ready not high");
        end
        #80;

        
        $display("\n --- Test: Read temp sensor threshold 2 Bits ---");
        test_word = 22'b1010100000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.u_control.internal_temp_threshold_2) begin
                $display("Internal temp sensor threshold 2 bits write test PASSED ✓!");
            end else begin
                $display("Internal temp sensor threshold 2 bits write FAILED ✘: Expected %h, Got %h", 
                         dut.u_control.internal_temp_threshold_2, master_received);
            end
        end else begin
            $display("Internal temp sensor threshold 2 bits write test FAILED ✘: data_ready not high");
        end
        #20;


///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Try temp sensor 3 threshold write then read (Write then read reg 0x0B) ----------------------
        $display("\n --- Test: Write temp sensor threshold 3 Bits ---");
        test_word = 22'b1010110000000000000101; // Write 0x2B0005
        
        // Call the write-only task
        spi_write_only(test_word);
        
        // Check results
        if (tb_spi_data_ready) begin
            @(negedge tb_spi_data_ready) // Wait for signal to go low
            $display("Internal temp sensor threshold 3 Bits: %h", dut.u_control.internal_temp_threshold_3);
            if (dut.u_control.internal_temp_threshold_3 == 16'h0005) begin
                $display("Internal temp sensor threshold 3 bits write test PASSED ✓!");
            end else begin
                $display("Internal temp sensor threshold 3 bits write test FAILED ✘: Expected %h", 16'h0005);
            end
        end else begin
            $display("Internal temp sensor threshold 3 bits write test FAILED ✘: data_ready not high");
        end
        #80;

        
        $display("\n --- Test: Read temp sensor threshold 3 Bits ---");
        test_word = 22'b1110110000000000000000; // Read threshold bits

        spi_write_read(test_word, master_received);
        
        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            if (master_received[15:0] == dut.u_control.internal_temp_threshold_3) begin
                $display("Internal temp sensor threshold 3 bits write test PASSED ✓!");
            end else begin
                $display("Internal temp sensor threshold 3 bits write FAILED ✘: Expected %h, Got %h", 
                         dut.u_control.internal_temp_threshold_3, master_received);
            end
        end else begin
            $display("Internal temp sensor threshold 3 bits write test FAILED ✘: data_ready not high");
        end
        #20;
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Test reading from temp counter 0  (Write then read reg 0x0C) ----------------------
        $display("\n --- Test: Read Temp Counter 0 ---");
        test_word = 22'b1_1_1100_0000_0000_0000_0000;
        
        // Call the task to perform the transaction
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high");
        end
        #20;
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Test reading from temp counter 1 (Write then read reg 0x0D) ----------------------

        $display("\n --- Test: Read Temp Counter 1 ---");
        test_word = 22'b1_1_1101_0000_0000_0000_0000;
        
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high");
        end
        #20;
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Test reading from temp counter 2 (Write then read reg 0x0E) ----------------------
 
        $display("\n --- Test: Read Temp Counter 2 ---");
        test_word = 22'b1_1_1110_0000_0000_0000_0000;
        
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high");
        end
        #20;
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ------------------- Test reading from temp counter 3 (Write then read reg 0x0F)----------------------
 
        $display("\n --- Test: Read Temp Counter 3 ---");
        test_word = 22'b1_1_1111_0000_0000_0000_0000;
        
        spi_write_read(test_word, master_received);

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data received by master: %h", master_received);
            // Add your check here
        end else begin
            $display("TX Test FAILED ✘: data_ready not high");
        end
        #20;


///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////// ASSORTED MUX CONFIGURATIONS ///////////////////////////////////////
////////////////////////////////////// TESTS READ AND WRITE REG 0X03 //////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // ---------------- Set output 2 to temp sensor good 1, output 1 to clk, no input
        $display("\n --- Test: Mux Output Pins ---");

        // Assign testbench-side variable for checking
        // You might need to drive this into an input if the DUT uses it
        // e.g., tb_temp_sens_in[3] = 1'b1; or similar. 
        // The snippet isn't clear, so I'm assuming it's for a local check.

        test_word = 22'b0_00111_000_00001_000_00000;

        // Call the task to send the SPI command
        spi_write_only(test_word);

        // Wait for the command to be processed
        // You may need a small delay or wait for spi_data_ready

        // Check results
        if (tb_spi_data_ready) begin
            $display("Data seen on pin 2: %b", tb_output_pin_2);

            
        end else begin
            $display("Output pin mux test FAILED ✘: data_ready not high");
        end

        #20; // Delay before next test


///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////


        // // ---------------- Set input 1 to conditioner
        $display("\n --- Test: Set Input 1 to Conditioner ---");

        // Set up the command and the serial data
        test_word = 22'b0_00_00000_00_00001_11_00000; // input to conditioner
        conditioner_serial_input = 384'h7b3a9f0e5c6d2814b7f8c9d0a3e5b6f7a8c9d0e1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c2e3f4a5b6c7d8e9f;
        tb_debug = 1'b1;
        // Send the SPI command
        spi_write_only(test_word);
        tb_rand_req_type = RDSEED_64;



        // Check results
        if (tb_spi_data_ready) begin
            // Wait for the command to propagate internally
            @(posedge tb_ic_clk);
            @(posedge tb_ic_clk);
            @(posedge tb_ic_clk);

            // NOTE: Check your internal signal path. 
            // 'curr_state' is probably not a TB signal.
            $display("Curr state: %h", dut.u_control.curr_state); 
            
            // This check seems to compare an internal state with the command word.
            // Adjust this if logic is different.
            if (dut.u_control.curr_state == test_word) begin
                $display("Curr state Test PASSED ✓!");
            end else begin
                $display("Curr state FAILED ✘: Expected %h", test_word);
            end
            
        end else begin
            $display("Curr state FAILED ✘: data_ready not high");
        end

        // Now, send the serial data on input_pin_1, driven by the main clock
        for (int i=383; i>=0; i--) begin
            tb_input_pin_1 = conditioner_serial_input[i]; // MSB first
            #10; // This delay should align with your main clock period
                // If tb_ic_clk period is 10ns, use `@(posedge tb_ic_clk);` instead of #10
        end

        tb_input_pin_1 = 1'b0; // Set pin low after transmission

        #10000;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        // // ---------------- Set input 1 to Trivium (also setting debug state)
        $display("\n --- Test: Set Input 1 to Trivium ---");

        // Set up the command and the serial data
        test_word = 22'b0_00_00000_00_00001_11_00001; // input to conditioner
        conditioner_serial_input = 384'h7b3a9f0e5c6d2814b7f8c9d0a3e5b6f7a8c9d0e1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c2e3f4a5b6c7d8e9f;
        tb_debug = 1'b1;
        // Send the SPI command
        spi_write_only(test_word);
        tb_rand_req_type = RDRAND_16;


        // Check results
        if (tb_spi_data_ready) begin
            // Wait for the command to propagate internally
            @(posedge tb_ic_clk);
            @(posedge tb_ic_clk);
            @(posedge tb_ic_clk);

            // NOTE: Check your internal signal path. 
            // 'curr_state' is probably not a TB signal.
            $display("Curr state: %h", dut.u_control.curr_state); 
            
            // This check seems to compare an internal state with the command word.
            // Adjust this if logic is different.
            if (dut.u_control.curr_state == test_word) begin
                $display("Curr state Test PASSED ✓!");
            end else begin
                $display("Curr state FAILED ✘: Expected %h", test_word);
            end
            
        end else begin
            $display("Curr state FAILED ✘: data_ready not high");
        end

        // Now, send the serial data on input_pin_1, driven by the main clock
        for (int i=159; i>=0; i--) begin
            tb_input_pin_1 = conditioner_serial_input[i]; // MSB first
            #10; // This delay should align with your main clock period

        end

        tb_input_pin_1 = 1'b0; // Set pin low after transmission

        #1000000;

///////////////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////////////

        $finish;
    end

endmodule
