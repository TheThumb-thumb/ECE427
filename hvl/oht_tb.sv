import le_types::*;
import params::*;
module oht_tb;

logic clk, rst;

initial clk= 1'b0;
always #1ns clk= ~clk;
initial rst= 1'b0;

    // input logic adc_in, // data value from entropy source
    // input logic adc_en, // read data from entropy source when high -> apparently will be a multiple of the clock freq so base it on clock divider
    // input logic clk,
    // input logic rst,
    // input logic deque,

    // output logic inter_fail,
    // output logic perm_fail,
    // output logic [SAMPLE_SIZE-1:0] checked_noise,
    // output logic good_entropy_out,
    // output logic full,
    // output logic empty,

    // // outputs for controlling entropy source calibration
    // output logic [7:0] calibration_arr_n,   // controls the number of 1s
    // output logic [7:0] calibration_arr_p    // controls the number of 0s
    logic adc_en;
    logic adc_in, deque;
    logic inter_fail, perm_fail, good_entropy_out, full, empty;
    logic [7:0] calibration_arr_n, calibration_arr_p;
    logic [SAMPLE_SIZE-1:0] checked_noise;
    logic clk_div;
    logic [1023:0] input_val, input_val_next;

    always_ff @(posedge clk) begin
        if (rst) begin
            adc_in <= '0;
            adc_en <= '0;
            // input_val <= 1024'h3b827e8a159955d7f1d5d36e896489816e87b7a637d77b8b76c8c4943f25c7e9;
            input_val <= '1;
            deque <= '0;
            clk_div <= '0;
        end else begin

            // adc_in <= $urandom();
            input_val_next = {input_val[1023:1], 1'b0};
            adc_in <= input_val[1023];
            // deque <= empty ? '0 : $urandom();
            deque <= '0;
            clk_div <= clk_div + 1;
            if (clk_div) begin
            adc_en <= '1;
            end else begin
                adc_en <= '0;
            end

        end
    end

    OHT dut (
        .adc_in(adc_in),
        .adc_en(adc_en),
        .clk(clk),
        .rst(rst),
        .deque(deque),

        .inter_fail(inter_fail),
        .perm_fail(perm_fail),
        .checked_noise(checked_noise),
        .good_entropy_out(good_entropy_out),
        .full(full),
        .empty(empty),

        // calibration output
        .calibration_arr_n(calibration_arr_n),
        .calibration_arr_p(calibration_arr_p)
    );

    initial begin
		$fsdbDumpfile("dump.fsdb");
		$fsdbDumpvars(0, "+all");
		rst = 1'b1;
        #10ns
		rst = 1'b0;
		#10000ns
		$finish();
	end


endmodule