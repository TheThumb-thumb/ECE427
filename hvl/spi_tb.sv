`timescale 1ns/1ps

module spi_tb;


    // DUT Interface Signals
    logic sclk;
    logic rst_n;
    logic [21:0] data_to_send;
    logic [21:0] master_received;
    logic send_trigger;
    logic mosi;
    logic ss_n;
    logic miso;
    logic [21:0] data;
    logic data_ready;

    logic [21:0] test_word;
    assign test_word = 22'b10_1010_1010_1010_1010_1010;

    // Instantiate the DUT
    spi  dut (
        .sclk(sclk),
        .rst_n(rst_n),
        .data_to_send(data_to_send),
        .send_trigger(send_trigger),
        .mosi(mosi),
        .ss_n(ss_n),
        .miso(miso),
        .data(data),
        .data_ready(data_ready)
    );

    // Clock generation (SPI clock)
    initial begin
        sclk = 0;
        forever #5 sclk = ~sclk; // 100 MHz SPI clock (period = 10 ns)
    end


    // Test sequence
    initial begin

        // ------------------- Test RX -----------------------
        $fsdbDumpfile("spi_tb.fsdb");
        $fsdbDumpvars(0, "+all");
        // Initial states
        rst_n = 0;
        ss_n = 1; // Not selected
        mosi = 0;
        data_to_send = 4'b0000;
        send_trigger = 0;

        // Apply reset
        #20;
        rst_n = 1;
        #20;

        // Select the slave
        ss_n = 0;
        #15;

        for (int i=21; i>=0; i--) begin
            mosi = test_word[i]; // MSB first
            #10;
        end
        
        // Check results
        if (data_ready) begin
            // Deselect the slave

            ss_n = 1;

            $display("Data received by slave: %h", data);
            if (data ==test_word) begin
                $display("RX Test PASSED!");
            end else begin
                $display("RX Test FAILED: Expected %h", test_word);
            end
        end else begin
            $display("RX Test FAILED: data_ready not high");
        end

        #20;

        // ------------------- Test TX -----------------------
        // Initial states
        rst_n = 0;
        ss_n = 1; // Not selected
        mosi = 0;
        data_to_send = 4'b1101;
        send_trigger = 0;
        master_received = 4'b0000;

        // Apply reset
        #20;
        rst_n = 1;
        #15;

        // Select the slave
        ss_n = 0;
        #5;
        send_trigger = 1;
        #10;
        send_trigger = 0;

        
        for (int i=21; i>=0; i--) begin
            master_received[i] = miso;
            #10;
        end
        ss_n = 1;

        // Check results
        if (data_ready) begin
            // Deselect the slave

            
            $display("Data received by master: %h", master_received);
            if (master_received ==data_to_send) begin
                $display("TX Test PASSED!");
            end else begin
                $display("TX Test FAILED: Expected %h", data_to_send);
            end
        end else begin
            $display("TX Test FAILED: data_ready not high");
        end
        #20;
        // ------------------- Test Simulatenous -----------------------

        // Initial states
        rst_n = 0;
        ss_n = 1; // Not selected
        mosi = 0;
        data_to_send = 22'b10_1010_1010_1010_1010_1010;
        send_trigger = 0;

        // Apply reset
        #20;
        rst_n = 1;
        #20;

        // // Select the slave
        ss_n = 0;
        send_trigger = 1;
        #10;
        send_trigger = 0;

        for (int i=21; i>=0; i--) begin
            mosi = test_word[i]; // MSB first
            master_received[i] = miso;
            #10;
        end

        ss_n = 1;

        // Check results
        if (data_ready) begin
            // Deselect the slave


            $display("Data received by slave: %h. Data received by master: %h", data, master_received);
            if (data ==test_word && master_received==data_to_send) begin
                $display("Simulataneous Test PASSED!");
            end else begin
                $display("Simulataneous Test FAILED: Expected RX %h and TX %h", test_word, data_to_send);
            end
        end else begin
            $display("RX Test FAILED: data_ready not high");
        end


        #20;
        $finish;
    end

endmodule
