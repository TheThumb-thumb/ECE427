module fermat_test 
import params::*;
import le_types::*;
(

    input clk,
    input rst,
    input logic start,

    input logic [KEY_WIDTH-1:0] p,
    input logic [KEY_WIDTH-1:0] q,
   
    output logic prime_q,
    output logic prime_p

)

primailty_state_t curr_state, next_state;

logic [31:0] a;

assign a = p[1] ? q[255:223] : p[255:223]; // randomly assign an a based on bits of p and q

// test

always_comb begin : primailty_state
    
    unique case ()

    endcase

end

always_ff @( posedge clk ) begin : primailty_state_next
    


end


endmodule