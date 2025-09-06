import le_types::*;
import params::*;
module aes_cbc_mac_tb;

	logic top_clk;
	logic top_reset;

	initial top_clk = 1'b0;
	always #1ns top_clk = ~top_clk;
	initial top_reset = 1'b1;

    localparam DATA_WIDTH = 256;

    logic        start_i;
    logic        done_o;
    logic [(DATA_WIDTH/2)-1:0] key_i;
    logic [DATA_WIDTH-1:0] message_i;
    logic [DATA_WIDTH-1:0] mac_o ;


    aes_cbc_mac #(
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
		.clk(top_clk),
		.rst_n(top_reset),

		.*
	);

	initial begin 
		key_i =  {$urandom(), $urandom(), $urandom(), $urandom()};
		message_i =  {$urandom(), $urandom(), $urandom(), $urandom(),
                        $urandom(), $urandom(), $urandom(), $urandom()};
		start_i = 1'b1;
	end

	initial begin
		$fsdbDumpfile("dump.fsdb");
		$fsdbDumpvars(0, "+all");
		top_reset = 1'b0;
        #10ns
		top_reset = 1'b1;
		#1000ns
		$finish();
	end

endmodule : aes_cbc_mac_tb
