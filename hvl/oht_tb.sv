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
            input_val <= 1024'b1011101010110000110001000101011000100100011111011111000100010110000111001010101110011000010000001011011110000010111111111000010111011111010010111111001101101100000110010010011110001100011010000110111010000111111000001111011001010011110010000110011101100000110111010000101000101111100100000101001100101101010111110001001111101010000000000001111100111100111110010111001101100011010010010100110101001110010101101111010111010000001111011100101011100001100000100001101100110000000110110010011010010001110001010101011110001110110111000101100110101110111100000110010000101101110001111110100010110100100010110011100010100010011010011111100110011101101101000001111111111000010100101001111111100101111001101010011010110101000101001101010111011010100000011010011011011011001011001100000001001000111010000101000110100110011000110100010001110000110101001011001101101110000111111110010000100011110000000110110111111001001110100001010101111001011001111110100111110110111110000010000010100111010011000100110011000001010111100110011001110000;
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
            deque <= $urandom()%2 && good_entropy_out && !empty;
        end
    end

    OHT dut (
        .adc_in(adc_in),
        .adc_en(adc_en),
        .clk(clk),
        .rst(rst),
        .deque(deque),
        .debug_mode(1'b0),
        .spi_reg_lsb('0),
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