module encrypt_top
import params::*;
import le_types::*;
(

    input clk,
    input rst,
    input logic [KEY_WIDTH-1:0] p,
    input logic [KEY_WIDTH-1:0] q,
    
    output logic [KEY_WIDTH-1:0] key


)


// 1. Run primality test on pq

fermat_test primality(
    .clk(),
    .rst(),


);

// 2. 

endmodule