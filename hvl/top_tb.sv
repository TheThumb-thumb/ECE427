import le_types::*;
import params::*;
module top_tb;

	logic top_clk;
	logic top_reset;

	logic led;

	initial top_clk = 1'b0;
	always #1ns top_clk = ~top_clk;
	initial top_reset = 1'b0;

	logic                           RAND_instr_flag_i; 
    rand_width_t                    RAND_width_i;
    rand_instr_t                    RAND_type_i; 
    logic                           trng_ready_o;
    logic                           cf_next_o;
    logic   [OUTREG_MAX_WIDTH-1:0]  eax_next_o;

	top dut(
		.clk(top_clk),
		.rst_n(top_reset),

		.*
	);

	initial begin
		$fsdbDumpfile("dump.fsdb");
		$fsdbDumpvars(0, "+all");
		#10ns
		top_reset = 1'b1;
		RAND_instr_flag_i <= 1'b0;
		#10ns
		RAND_instr_flag_i <= 1'b1;
		#10ns
		RAND_instr_flag_i <= 1'b0;
		#1000ns
		$finish();
	end

endmodule
