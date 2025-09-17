import le_types::*;
import params::*;
module oht_tb;

logic clk, rst, adc_en;

initial clk= 1'b0;
always #1ns clk= ~clk;
initial rst= 1'b0;

initial adc_en = 1'b0;
always #2ns adc_en = ~adc_en;

    logic adc_in, deque;
    logic inter_fail, perm_fail, good_entropy_out, full, empty;
    logic [7:0] calibration_arr_n, calibration_arr_p;
    logic [SAMPLE_SIZE-1:0] checked_noise;
    // logic clk_div;
    logic [1023:0] input_val;
    logic [9:0] counter;

    always_ff @(posedge adc_en) begin
        if (rst) begin
            adc_in <= '0;
            input_val <= 1024'b0000000000000000000100000010011000000000000001000000010000000100010000000000000000000000000110100000001100000100000000000000000000000000000001001000000000000000000001010000000000000000000000000000000000001100010000000000100000001000000000000000000000010000000000000100000000001000000000000010000000000010000000000000000000000000100000100000000010001000000000000000000000000000000001000000001100010001000001100000001000000000000001000100000000000000000100000000000000000000000000000000010010000000000000000100000000000000100000100000000101000000000000001000000000000010000000100110000000000010010000100000101000000000000010000000000001000010001000000000000000000110000000000001001000001000000000000000000000001000000000000100001100000100010001000000000000100000000000000010000000000000100000000000010000000000001100000000000010000010000000000000000000000001000100000010000100000000000000100000010000100000000000000001000000000001000000001000000000000000000000001000000010010000000000000000100001000000000000000000000000101010;
            counter <= '0;
        end else begin
            adc_in <= input_val[counter];
            counter <= counter + 1;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            deque <= 0;
        end else begin
            deque <= $urandom()%2;
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
		$fsdbDumpfile("oht_dump.fsdb");
		$fsdbDumpvars(0, "+all");
		rst = 1'b1;
        #10ns
		rst = 1'b0;
		#100000ns
		$finish();
	end


endmodule