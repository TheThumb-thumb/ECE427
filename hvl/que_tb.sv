import le_types::*;
import params::*;
module que_tb;

logic clk, rst;
initial clk = 1'b0;
always #1ns clk = ~clk;
initial rst = 1'b0;


    // input logic clk,
    // input logic rst,
    // input logic inter_fail,
    // input logic perm_fail,

    // input logic [WIDTH-1:0] wdata,
    // output logic [WIDTH-1:0] rdata,

    // input logic enque,
    // input logic deque,

    // output logic full,
    // output logic empty
    
    logic inter_fail, perm_fail, enque, deque, full, empty;
    logic [255:0] rdata, wdata;

    que #(
        .DEPTH(8),
        .WIDTH(256)
    ) dut (
		.clk(clk),
		.rst(rst),
        .inter_fail(inter_fail),
        .perm_fail(perm_fail),

        .wdata(wdata),
        .rdata(rdata),
        .enque(enque),
        .deque(deque),
        .full(full),
        .empty(empty)
	);

    initial begin
        inter_fail = '0;
        perm_fail = '0;
        // enque = '0;
        // deque = '0;
        // #10ns
        // @(posedge clk);
        // wdata = {$urandom(), $urandom(), $urandom(), $urandom(), $urandom(), $urandom(), $urandom(), $urandom() };
        // #10ns
        // enque = 1'b0;
        // deque = 1'b0;
        // #2ns
        // enque = 1'b0;
        // deque = 1'b0;
        // #10ns
        // enque = 1'b1;
        // deque = 1'b0;
        // #2ns
        // enque = 1'b0;
        // deque = 1'b0;
        // #10ns
        // enque = 1'b1;
        // deque = 1'b1;
        // #2ns
        // enque = 1'b0;
        // deque = 1'b0;
        // #10ns
        // enque = 1'b0;
        // deque = 1'b1;
        // #2ns
        // enque = 1'b0;
        // deque = 1'b0;

    end

	initial begin
		$fsdbDumpfile("dump.fsdb");
		$fsdbDumpvars(0, "+all");
		rst = 1'b1;
        #10ns
		rst = 1'b0;
		#1000ns
		$finish();
	end

    always_ff @( posedge clk ) begin : blockName
        wdata <= {$urandom(), $urandom(), $urandom(), $urandom(), $urandom(), $urandom(), $urandom(), $urandom() };
        enque <= $urandom() % 2;
        deque <= $urandom() % 2;
    end


endmodule