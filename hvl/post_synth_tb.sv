`timescale 1ns/1ps

import le_types::*;
import params::*;

module top_io_synth_tb;

    // clocks
    logic ic_clk;
    logic rst_n;
    logic debug_clk;

    initial begin
        ic_clk = 1'b0;
        forever #1ns ic_clk = ~ic_clk;
    end

    initial begin
        debug_clk = 1'b0;
        forever #5ns debug_clk = ~debug_clk;
    end

    // CPU 
    logic        rand_req;
    rand_req_t   rand_req_type;
    logic [15:0] rand_byte;
    logic        rand_valid;
    logic        slow_clk;

    // SPI
    logic ss_n, mosi, miso, spi_data_ready;

    // debug
    logic debug, output_to_input_direct, input_pin_1, output_pin_1, output_pin_2;

    // temp / analog
    logic        temp_debug;
    logic [3:0]  EN_out1, EN_out2;
    logic [13:0] temp_counter_0, temp_counter_1, temp_counter_2, temp_counter_3;

    // entropy / jitter
    logic [63:0]  entropy_source_array;
    logic [191:0] arr_n, arr_p;
    logic [31:0]  jitter_disable_arr;
    logic         analog_clk;
    logic         jitter_vdd_A, jitter_vdd_B;

    // DUT from top_io.gate.v
    top_io dut (
        .ic_clk_io                 (ic_clk),
        .rst_n_io                  (rst_n),

        .rand_req_io               (rand_req),
        .rand_req_type_io          (rand_req_type),
        .rand_byte_io              (rand_byte),
        .rand_valid_io             (rand_valid),
        .slow_clk_io               (slow_clk),

        .ss_n_io                   (ss_n),
        .debug_clk_io              (debug_clk),
        .mosi_io                   (mosi),
        .miso_io                   (miso),
        .spi_data_ready_io         (spi_data_ready),

        .debug_io                  (debug),
        .output_to_input_direct_io (output_to_input_direct),
        .input_pin_1_io            (input_pin_1),
        .output_pin_2_io           (output_pin_2),
        .output_pin_1_io           (output_pin_1),

        .temp_debug_io             (temp_debug),
        .EN_out1                   (EN_out1),
        .EN_out2                   (EN_out2),
        .temp_counter_0            (temp_counter_0),
        .temp_counter_1            (temp_counter_1),
        .temp_counter_2            (temp_counter_2),
        .temp_counter_3            (temp_counter_3),

        .entropy_source_array      (entropy_source_array),
        .arr_n                     (arr_n),
        .arr_p                     (arr_p),
        .jitter_disable_arr        (jitter_disable_arr),
        .analog_clk                (analog_clk),

        .jitter_vdd_A              (),
        .jitter_vdd_B              ()
    );

    // fake entropy
    always_ff @(posedge ic_clk) begin
        entropy_source_array <= {$urandom(), $urandom()};
    end

    // reset + defaults
    task automatic reset_dut();
        rst_n                 = 1'b0;
        rand_req              = 1'b0;
        rand_req_type         = '0;
        ss_n                  = 1'b1;
        mosi                  = 1'b0;
        debug                 = 1'b0;
        output_to_input_direct= 1'b0;
        input_pin_1           = 1'b0;
        temp_debug            = 1'b0;
        temp_counter_0        = '0;
        temp_counter_1        = '0;
        temp_counter_2        = '0;
        temp_counter_3        = '0;
        jitter_vdd_A          = 1'b1;
        jitter_vdd_B          = 1'b1;
        // entropy_source_array  = '0;

        repeat (10) @(posedge ic_clk);
        rst_n = 1'b1;
        repeat (20) @(posedge ic_clk);
    endtask

    task automatic drive_random_request();
        rand_req_type = RDSEED_64;
        rand_req      = 1'b1;
        @(posedge ic_clk);
        rand_req      = 1'b0;
        wait (rand_valid === 1'b1);
        $display("[%0t] SYNTH RDSEED_64: %h", $realtime, rand_byte);
    endtask

    task automatic normal_behavior_loop();
        forever begin
            repeat (50) @(posedge ic_clk);
            drive_random_request();
        end
    endtask

    initial begin
        $fsdbDumpfile("top_io_synth.fsdb");
        $fsdbDumpvars(0, top_io_synth_tb);

        reset_dut();

        fork
            normal_behavior_loop();
        join_none

        #20000ns;
        $finish;
    end

    // sanity assertion
    property p_rand_byte_known;
        @(posedge ic_clk) rand_valid |-> !$isunknown(rand_byte);
    endproperty

    a_rand_byte_known: assert property (p_rand_byte_known)
        else $fatal(1, "rand_byte X/Z when rand_valid=1 at %0t", $realtime);

endmodule
