module encrypt_top
import params::*;
import le_types::*;
(

    input clk,
    input rst,
    input key_gen,  // signal from trng that p and q have been generated
    input logic [KEY_WIDTH-1:0] p,
    input logic [KEY_WIDTH-1:0] q,
    
    output logic [KEY_WIDTH-1:0] key

)

logic [KEY_WIDTH-1:0] p_odd, q_odd; 
logic prime_p, prime_q; // output of primality to determine if p and q are prime or not, 1: prime, 0: unprime

logic prim_start;

assign p_odd = {p[KEY_WIDTH-1:1], 1};
assign q_odd = {q[KEY_WIDTH-1:1], 1};

encryption_state_t curr_state, next_state;

// 1. Run primality test on pq

fermat_test primality(
    .clk(clk),
    .rst(rst),
    .start(prim_start),

    .p(p_odd),
    .q(q_odd),

    .prime_q(prime_q),
    .prime_p(prime_p)
);


always_comb begin : encryption_state

    curr_state = IDLE;
    prim_start = '0;
    unique case (curr_state)
        
        IDLE: begin

            // should not do anything, we are waiting for random values

        end
        PRIMALITY: begin
            prim_start = 1'b1;
        end
        MODULUS: begin

        end
        LAMBDA: begin

        end
        COPRIME: begin

        end
        INVERSE: begin

        end
        DONE: begin

        end

    endcase
end

always_ff @( posedge clk ) begin : encryption_state_next
    
    next_state = curr_state;

    if (key_gen) begin
        next_state = PRIMALITY;
    end

end

endmodule