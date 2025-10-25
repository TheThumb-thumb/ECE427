`timescale 1ns/1ps

module control_tb;

    // Parameters
    localparam word_width = 5'd22;

    // DUT Interface Signals
    logic        clk;
    logic        latch_entropy_mux_out; // Serial debug output from selected latch entropy source
    logic        jitter_entropy_mux_out; // Serial debug output from selected latch entropy source
    logic [15:0] entropy_calibration; // Entropy calibration value for debug

    logic        latch_oht_mux_in; // Serial debug input to selected latch OHT
    logic        jitter_oht_mux_in; // Serial debug input to selected jitter OHT
    
    logic        CTD_debug_input; // Serial debug input to conditioner, trivium, or DRBG

    logic [13:0] temp_counter_0, temp_counter_1, temp_counter_2, temp_counter_3; // Counters for temp sensors, verify w Anthony
    logic [13:0] temp_threshold_0, temp_threshold_1, temp_threshold_2, temp_threshold_3; // Thresholds for temp sensors
    logic        temp_sense_0_good, temp_sense_1_good, temp_sense_2_good, temp_sense_3_good; // Single bit boolean good/bad for temp sensor
    logic [21:0] curr_state; // Contains all the info for muxes

    logic [15:0] lower_latch_entropy_good;
    logic [15:0] upper_latch_entropy_good;
    logic [15:0] lower_jitter_entropy_good;
    logic [15:0] upper_jitter_entropy_good;

    logic debug;
    logic debug_clk;
    logic ic_clk;
    logic rst_n;
    logic mosi;
    logic ss_n;
    logic output_to_input_direct; // Pin to connect output 2 directly to input
    logic spi_data_ready;
    logic [21:0] master_received;

    logic input_pin_1;

    logic [383:0] conditioner_serial_input;


    // Instantiate the control module
    control dut_control (
        .ic_clk(ic_clk),
        .debug_clk(debug_clk),
        .rst_n(rst_n),
        .mosi(mosi),
        .ss_n(ss_n),
        .debug(debug),
        
        .input_pin_1(input_pin_1),
        .miso(miso),
        .output_pin_2(output_pin_2),
        .output_pin_1(output_pin_1),
        .output_to_input_direct(output_to_input_direct),
        .clk(clk), // This is the new system clock (muxed between ic_clk and debug_clk pins)

        .latch_entropy_mux_out(latch_entropy_mux_out), // Serial output from selected latch entropy source
        .jitter_entropy_mux_out(jitter_entropy_mux_out), // Serial debug output from selected latch entropy source

        .entropy_calibration(entropy_calibration), // Entropy calibration value for debug

        .latch_oht_mux_in(latch_oht_mux_in),  // Serial debug input to selected latch OHT
        .jitter_oht_mux_in(jitter_oht_mux_in),  // Serial debug input to selected jitter OHT
        
        .CTD_debug_input(CTD_debug_input), // Serial debug input to conditioner, trivium, or DRBG
        .temp_counter_0(temp_counter_0),  // Counters for temp sensors
        .temp_counter_1(temp_counter_1),
        .temp_counter_2(temp_counter_2),
        .temp_counter_3(temp_counter_3),
        .temp_threshold_0(temp_threshold_0),  // Thresholds for temp sensors
        .temp_threshold_1(temp_threshold_1),
        .temp_threshold_2(temp_threshold_2),
        .temp_threshold_3(temp_threshold_3),
        .temp_sense_0_good(temp_sense_0_good), // Single bit boolean good/bad for temp sensor
        .temp_sense_1_good(temp_sense_1_good),
        .temp_sense_2_good(temp_sense_2_good),
        .temp_sense_3_good(temp_sense_3_good),

        .lower_latch_entropy_good(lower_latch_entropy_good),
        .upper_latch_entropy_good(upper_latch_entropy_good),
        .lower_jitter_entropy_good(lower_jitter_entropy_good),
        .upper_jitter_entropy_good(upper_jitter_entropy_good),

        .curr_state(curr_state),
        .spi_data_ready(spi_data_ready)
    );
    
    // Clock generation (SPI clock)
    initial begin
        
        debug_clk = 0;
        forever #5 debug_clk = ~debug_clk; // 100 MHz clock
    end

    initial begin
        ic_clk = 0;
        forever #5 ic_clk = ~ic_clk; // 100 MHz clock
    end



    logic [21:0] test_word;
    logic [21:0] fake_input;
    
    // Test sequence
    initial begin

        $fsdbDumpfile("control.fsdb");
        $fsdbDumpvars(0, "+all");

        // ------------------- Test reading from temp counter 0 ----------------------
        assign temp_counter_0 = 14'b11_0000_1111_0000;
        assign test_word = 22'b1_1_1100_0000_0000_0000_0000;
        // Test passed 9/29/25
        // Initial states
        input_pin_1 = 0;
        rst_n = 0;
        ss_n = 1; // Not selected
        mosi = 0;
        master_received = 22'd0;

        // Apply reset
        #20;
        rst_n = 1;
        debug =1'b1;
        #10;


        // Select the slave
        @(posedge clk);
        ss_n = 0;
        #15;

        @(negedge clk);
        for (int i=word_width-1; i>=0; i--) begin
            mosi = test_word[i]; // MSB first
            #10;
        end
        #20;
        for (int i=word_width-1; i>=0; i--) begin
            master_received[i] = miso;
            #10;
        end

        // Check results
        if (spi_data_ready) begin
            // Deselect the slave
            $display("Data received by master: %h", master_received);
            if (master_received ==temp_counter_0) begin
                $display("TX Test PASSED!");
            end else begin
                $display("TX Test FAILED: Expected %h", temp_counter_0);
            end
        end else begin
            $display("TX Test FAILED: data_ready not high");
        end
        ss_n = 1;
        mosi = 0;

        #20

        // ------------------- Test reading from temp counter 1 ----------------------
        assign temp_counter_1 = 14'b11_0110_0110_0001;
        assign test_word = 22'b1_1_1101_0000_0000_0000_0000;
        // Test passed: 9/29/25
        // Initial states

        // Select the slave
        @(posedge clk);
        ss_n = 0;
        #15;

        @(negedge clk);
        for (int i=word_width-1; i>=0; i--) begin
            mosi = test_word[i]; // MSB first
            #10;
        end
        #20;
        for (int i=word_width-1; i>=0; i--) begin
            master_received[i] = miso;
            #10;
        end

        // Check results
        if (spi_data_ready) begin
            // Deselect the slave
            $display("Data received by master: %h", master_received);
            if (master_received ==temp_counter_1) begin
                $display("TX Test PASSED!");
            end else begin
                $display("TX Test FAILED: Expected %h", temp_counter_1);
            end
        end else begin
            $display("TX Test FAILED: data_ready not high");
        end
        ss_n = 1;
        mosi = 0;

        #20

        // ------------------- Test if debug pin low that curr state is default ----------------------
        // Test passed: 9/29/25
        // Initial states

        debug = 1'b0;
        #20;
        

        // Check results
        
        // Deselect the slave
        $display("Current state: %h", curr_state);
        
            if (curr_state ==22'b00_0000_0000_0000_0000_0000) begin
                $display("Default State Test PASSED!");
            end else begin
                $display("Default State Test FAILED: Expected %h", 22'b00_0000_0000_0000_0000_0000);
            end

        #20;


        #20
        debug = 1'b1;
        #20

        // ------------------- Try calibration bit write then read ----------------------
        assign test_word = 22'b1_0_0111_1100_0011_1100_0001; // Register operation write_address 0x07 
        // Test passed 10/2/25

        // Select the slave
        @(posedge clk);
        ss_n = 0;
        #15;

        @(negedge clk);
        for (int i=word_width-1; i>=0; i--) begin
            mosi = test_word[i]; // MSB first
            #10;
        end

        // Check results
        if (spi_data_ready) begin
            @(negedge spi_data_ready)
            $display("Entropy Calibration Bits: %h", dut_control.internal_entropy_calibration);
            if (dut_control.internal_entropy_calibration == test_word[15:0]) begin
                $display("Calibration bits Test PASSED!");
            end else begin
                $display("Calibration bits Test FAILED: Expected %h", test_word[15:0]);
            end
        end else begin
            $display("Calibration bits Test FAILED: data_ready not high");
        end
        ss_n = 1;
        mosi = 0;
    
        #80;

        
        assign test_word = 22'b1_1_0111_0000_0000_0000_0000; // Read debug calibration bits

        @(posedge clk);
        ss_n = 0;
        #15;

        @(negedge clk);
        // Send command
        for (int i=word_width-1; i>=0; i--) begin
            mosi = test_word[i]; // MSB first
            #10;
        end

        #20; // Wait one cycle

        // Read command
        for (int i=word_width-1; i>=0; i--) begin
            master_received[i] = miso;
            #10;
        end
        
        // Check results
        if (spi_data_ready) begin
            // Deselect the slave
            $display("Data received by master: %h", master_received);
            if (master_received == dut_control.internal_entropy_calibration) begin
                $display("Calibration bits read Test PASSED!");
            end else begin
                $display("Calibration bits read Test FAILED: Expected %h", dut_control.internal_entropy_calibration);
            end
        end else begin
            $display("Calibration bits read Test FAILED: data_ready not high");
        end
        ss_n = 1;
        mosi = 0;      

        #20;



        // ---------------- Set output 2 to temp sensor good 1, output 1 to clk, no input
        assign temp_sense_3_good = 1'b1;
        assign test_word = 22'b0_00111_000_00001_000_00000;
        // Test passed: 9/29/25
        // Initial states

        // Select the slave
        @(posedge clk);
        ss_n = 0;
        #15;

        @(negedge clk);
        for (int i=word_width-1; i>=0; i--) begin
            mosi = test_word[i]; // MSB first
            #10;
        end

        ss_n = 1;
        // Check results
        if (spi_data_ready) begin
            // Deselect the slave
            $display("Data seen on pin 2: %h", output_pin_2);
            if (output_pin_2 ==temp_sense_3_good) begin
                $display("Output pin mux test PASSED!");
            end else begin
                $display("Output pin mux test FAILED: Expected %h", temp_sense_3_good);
            end
        end else begin
            $display("Output pin mux test FAILED: data_ready not high");
        end
        ss_n = 1;
        mosi = 0;


        // ---------------- Set input 1 to conditioner

        // output 1 =vcc, output2 = clk, input 1 -> conditioner
        assign test_word = 22'b0_00_00000_00_00001_11_00000; // input to conditioner
        
        // input to be on pin 1
        assign conditioner_serial_input = 384'h7b3a9f0e5c6d2814b7f8c9d0a3e5b6f7a8c9d0e1b2c3d4e5f6a7b8c9d0e1f2a3b4c5d6e7f8a9b0c2e3f4a5b6c7d8e9f;

        // Test passed: 9/29/25
        // Initial states

        // Select the slave
        @(posedge clk);
        ss_n = 0;
        #15;

        @(negedge clk);
        for (int i=word_width-1; i>=0; i--) begin
            mosi = test_word[i]; // MSB first
            #10;
        end

        // Check results
        if (spi_data_ready) begin
            @(posedge clk)
            @(posedge clk)
            @(posedge clk)

            $display("Curr state: %h", curr_state);
            if (curr_state == test_word) begin
                $display("Curr state Test PASSED!");
            end else begin
                $display("Curr state FAILED: Expected %h", test_word);
            end
        end else begin
            $display("Curr state FAILED: data_ready not high");
        end

        ss_n = 1;
        mosi = 0;

        @(posedge clk)
        for (int i=383; i>=0; i--) begin
            input_pin_1 = conditioner_serial_input[i]; // MSB first
            #10;
        end

        #30
        $finish;
    end

endmodule
