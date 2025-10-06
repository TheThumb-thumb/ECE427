import le_types::*;
import params::*;
module oht_top_tb;

logic clk, rst;

initial clk = 1'b0;
always #1ns clk = ~clk;
initial rst = 1'b0;

    logic [es_sources-1:0] ES_in; // 0-31 latch 32-63 jitter
    logic deque;                  // tells us aes is reading? Does that matter?
    logic debug_mode;
    logic [15:0] spi_reg_lsb;

    logic [cond_width-1:0] cond_out;
    logic full;
    logic empty;
    logic [latch_sources-1:0][calib_bits-1:0] arr_n;
    logic [latch_sources-1:0][calib_bits-1:0] arr_p;
    logic [jitter_sources-1:0] j_disable_arr;

    always_ff @(posedge clk) begin
        for (int i = 0; i < es_sources; i++) begin
            ES_in[i] <= $urandom_range(0,1);
        end
    end

    assign deque = full && !empty;
    assign debug_mode = '0;
    assign spi_reg_lsb = '0;

    oht_top dut (
        .clk(clk),
        .rst(rst),

        .ES_in(ES_in),
        .deque(deque),
        .debug_mode(debug_mode),
        .spi_reg_lsb(spi_reg_lsb),

        .cond_out(cond_out),
        .full(full),
        .empty(empty),
        .arr_n(arr_n),
        .arr_p(arr_p),
        .j_disable_arr(j_disable_arr)

    );

    initial begin
		$fsdbDumpfile("oht_top_dump.fsdb");
		$fsdbDumpvars(0, "+all");
		rst = 1'b1;
        #10ns
		rst = 1'b0;
		#100000ns
		$finish();
	end

endmodule