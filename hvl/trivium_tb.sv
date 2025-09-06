import le_types::*;
import params::*;
module trivium_tb

logic clk, rst;
initial clk = 1'b0;
always #1ns clk = ~clk;
initial rst = 1'b0;

    // input logic                         clk,
    // input logic                         rst,
    
    // input logic                         adc_in,
    // input logic                         adc_wr,
    // input logic                         req,    // Requesting encryption keys

    // output logic [KEY_WIDTH-1:0]        p,
    // output logic [KEY_WIDTH-1:0]        q


endmodule