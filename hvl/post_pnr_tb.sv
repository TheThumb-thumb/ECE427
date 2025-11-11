`timescale 1ns/1ps

import le_types::*;
import params::*;
module post_pnr_tb;

    logic ic_clk;
    logic rst_n; // active low reset for rst_n_io
    logic debug_clk;

    initial begin
        ic_clk = 1'b0;
        forever #1ns ic_clk = ~ic_clk; // 500 MHz core clock
    end

    initial begin
        debug_clk = 1'b0;
        forever #5ns debug_clk = ~debug_clk; // debug/SPI clock
    end

    // cpu
    logic        rand_req;
    rand_req_t   rand_req_type; // [2:0] in netlist
    logic [15:0] rand_byte; // rand_byte_io[15:0]
    logic        rand_valid;
    logic        slow_clk;

    // spi
    logic ss_n;
    logic mosi;
    logic miso;
    logic spi_data_ready;

    // debug
    logic debug;
    logic output_to_input_direct;
    logic input_pin_1;
    logic output_pin_1;
    logic output_pin_2;

    // temp & analog stuff
    logic        temp_debug;
    logic [3:0]  EN_out1, EN_out2;
    logic [13:0] temp_counter_0, temp_counter_1, temp_counter_2, temp_counter_3;

    // entropy & jitter 
    logic [63:0]  entropy_source_array; // fake entropy
    logic [191:0] arr_n; // DUT outputs
    logic [191:0] arr_p;
    logic [31:0]  jitter_disable_arr;
    logic         analog_clk;

    // itter rails inputs
    logic jitter_vdd_A, jitter_vdd_B;

    // ----------------- DUT instantiation (from top_io.pnr.v) -----------------
    top_io dut (
        // Clk/Reset
        .ic_clk_io                 (ic_clk),
        .rst_n_io                  (rst_n),

        // CPU interface
        .rand_req_io               (rand_req),
        .rand_req_type_io          (rand_req_type),
        .rand_byte_io              (rand_byte),
        .rand_valid_io             (rand_valid),
        .slow_clk_io               (slow_clk),

        // SPI
        .ss_n_io                   (ss_n),
        .debug_clk_io              (debug_clk),
        .mosi_io                   (mosi),
        .miso_io                   (miso),
        .spi_data_ready_io         (spi_data_ready),

        // Debug
        .debug_io                  (debug),
        .output_to_input_direct_io(output_to_input_direct),
        .input_pin_1_io            (input_pin_1),
        .output_pin_2_io           (output_pin_2),
        .output_pin_1_io           (output_pin_1),

        // Temp / analog
        .temp_debug_io             (temp_debug),
        .EN_out1                   (EN_out1),
        .EN_out2                   (EN_out2),
        .temp_counter_0            (temp_counter_0),
        .temp_counter_1            (temp_counter_1),
        .temp_counter_2            (temp_counter_2),
        .temp_counter_3            (temp_counter_3),

        // Entropy & jitter
        .entropy_source_array      (entropy_source_array),
        .arr_n                     (arr_n),
        .arr_p                     (arr_p),
        .jitter_disable_arr        (jitter_disable_arr),
        .analog_clk                (analog_clk),

        // Jitter rails
        .jitter_vdd_A              (jitter_vdd_A),
        .jitter_vdd_B              (jitter_vdd_B)
    );

    // sdf ignore this for now
    // initial begin
    // `ifdef SDF_ANNOTATE
    //     string sdf = "post_pnr_tb.sdf";
    //     void'($value$plusargs("SDF=%s", sdf)); // allow +SDF=yourfile.sdf
    //     $sdf_annotate(sdf, dut,,, "MAXIMUM");
    // `endif
    // end

    // default reset
    task automatic reset_dut();
        begin
            // reset asserted low
            rst_n                 = 1'b0;

            // CPU / SPI defaults
            rand_req              = 1'b0;
            rand_req_type         = '0;
            ss_n                  = 1'b1;
            mosi                  = 1'b0;

            // Debug
            debug                 = 1'b0;
            output_to_input_direct= 1'b0;
            input_pin_1           = 1'b0;

            // Temp
            temp_debug            = 1'b0;
            temp_counter_0        = '0;
            temp_counter_1        = '0;
            temp_counter_2        = '0;
            temp_counter_3        = '0;

            // Jitter rails
            jitter_vdd_A          = 1'b1;
            jitter_vdd_B          = 1'b1;

            // Start with zero entropy; we’ll drive it below
            entropy_source_array  = '0;

            // Hold reset for a bit
            repeat (10) @(posedge ic_clk);
            rst_n = 1'b1;

            repeat(20) @(posedge ic_clk);
        end
    endtask

    // Fake entropy
    always_ff @(posedge ic_clk) begin
        // random 64 bit val sent to entropy source array to feed oht/conditioner/drbg
        entropy_source_array <= {$urandom(), $urandom()};
    end

// SDF Timing Assertions: Entropy Path
    // entropy only changes on posedge:
    property p_entropy_changes_only_on_clk;
    @(negedge ic_clk) $stable(entropy_source_array);
    endproperty

    a_entropy_changes_only_on_clk: assert property (p_entropy_changes_only_on_clk)
    else $error("[%0t] entropy_source_array changed between clock edges", $realtime);


    // after a request, entropy_source_array must stay stable for a few cycles
    localparam int ENTROPY_STABLE_CYCLES = 2;
    property p_entropy_stable_after_req;
    @(posedge ic_clk)
        rand_req && rst_n |-> $stable(entropy_source_array)[*ENTROPY_STABLE_CYCLES];
    endproperty

    a_entropy_stable_after_req: assert property (p_entropy_stable_after_req)
    else $error("[%0t] entropy_source_array changed too soon after rand_req", $realtime);


    // rand_valid must come after rand_req, not same cycle, not set to late indef
    localparam int RAND_MIN_LATENCY = 5; // change after measuring
    localparam int RAND_MAX_LATENCY = 200; // upper bound to catch stalls

    property p_rand_latency_from_req;
    @(posedge ic_clk)
        rand_req && rst |-> ##[RAND_MIN_LATENCY:RAND_MAX_LATENCY] rand_valid;
    endproperty

    a_rand_latency_from_req: assert property (p_rand_latency_from_req)
    else $error("[%0t] rand_valid did not arrive in the expected latency window after rand_req", $realtime);

// still keep some rtl assertions even though it will get jacked by parasitic capacitance
    // data valid from top_io
    // When rand_valid is high, entropy is not X/Z
    property p_entropy_path_clean_when_valid;
    @(posedge ic_clk)
        rand_valid && rst_n |-> (!$isunknown(rand_byte) && !$isunknown(entropy_source_array));
    endproperty

    a_entropy_path_clean_when_valid: assert property (p_entropy_path_clean_when_valid)
    else $fatal(1, "[%0t] X/Z detected on entropy path while rand_valid=1", $realtime);


    // initial test 
    task automatic random_request();
        begin
            // request one 64b seed 
            rand_req_type = RDSEED_64;    
            
            // pulse rand req
            rand_req = 1'b1;
            @(posedge ic_clk);
            rand_req = 1'b0;

            // wait for rand_valid
            wait (rand_valid === 1'b1);
            $display("[%0t] Post-PNR random data: %h", $realtime, rand_byte);
        end
    endtask

    task automatic dft_check();
        begin
            // call your DFT tasks here
            // trigger scan, BIST, debug SPI sequences ...
            $display("[%0t]  DFT check ...", $realtime);
        end
    endtask

    task automatic work_loop();
        begin
            forever begin
                // some idle time
                repeat (50) @(posedge ic_clk);

                // do a random request
                random_request();

                // randomly run a DFT check
                if ($urandom_range(0,7) == 0) begin
                    dft_check();
                end
            end
        end
    endtask
    
    initial begin
        // FSDB dump
        $fsdbDumpfile("post_pnr_dump.fsdb");
		$fsdbDumpvars(0, "+all");

        // DUT out of reset
        reset_dut();

        // Main requests + DFT in background
        fork
            work_loop();
            // you could add more background tasks here if needed
        join_none

        // Let it run
        #20000ns;
        $finish();
    end

endmodule
