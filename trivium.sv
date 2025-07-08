module trivium 
import params::*;
import le_types::*;
#(
    localparam STATE = 228;
)
(
    input logic clk,
    input logic rst,
    input logic [IV_WIDTH-1:0] iv_,
    input logic [IV_WIDTH-1:0] key_,

    input logic [1:0] trivium_state_t state,

    output logic done,
    output logic iv_full,
    output logic [KEY_WIDTH-1:0] enc_key,

);

// Key and IV setup:

    logic [STATE-1:0] internal_state;

    always_comb begin

        

    end

    always_ff @(posedge clk) begin
        
    end

endmodule