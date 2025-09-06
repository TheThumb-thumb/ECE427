module top_tb;

	logic top_clk;
	logic top_reset;

	logic led;

	initial top_clk = 1'b0;
	always #1ns top_clk = ~top_clk;

	initial top_reset = 1'b1;

	top dut(.*);

	int fd;

	initial begin
		$fsdbDumpfile("dump.fsdb");
		$fsdbDumpvars(0, "+all");
		#10ns
		top_reset = 1'b0;

		#1000ns
		$finish();
	end

endmodule
