import params::*;
import le_types::*;

module top 
#(
    parameter   OUTREG_MAX_WIDTH    = 64
)
(
    input   logic                           clk,
    input   logic                           rst_n,

    //maybe add some kind of request queue in the future?

    input   logic                           RAND_instr_flag_i,  // if =1, implies a RAND instr is incoming from CPU (valid signal)
    input   rand_width_t                    RAND_width_i,       // if =2'b00, width of RN is 16, if =2'b01, width of RN is 32, if =2'b10, width of RN is 64
    input   rand_instr_t                    RAND_type_i,        // if =0,  implies instr is RDRAND, if =1, implies instr is RDSEED

    output  logic                           trng_ready_o,       // if =1, trng is ready for a new request (otherwise the host should stall)
    output  logic                           cf_next_o,          // if =1, RAND instr was succesful (host will load into CF flag), =0 implies failure
    output  logic   [OUTREG_MAX_WIDTH-1:0]  eax_next_o          // data to be loaded into eax (width can vary based on instruction mode) 
    //will probably have to send output number in bytes of 8
); 

generate
    if(OUTREG_MAX_WIDTH != 16 && OUTREG_MAX_WIDTH != 32 && OUTREG_MAX_WIDTH != 64) begin 
        $fatal(1, "Error: OUTREG_MAX_WIDTH parameter must be 16, 32, or 64");
    end
endgenerate

rand_instr_t RAND_type;
rand_width_t RAND_width;

always_ff @ (posedge clk) begin : request_input_sampler
    if(!rst_n) begin
        RAND_type <= 'x;
        RAND_width <= 'x;
    end else if(RAND_instr_flag_i && trng_ready_o) begin
        RAND_type <= RAND_type_i;
        RAND_width <= RAND_width_i;
    end   
end : request_input_sampler

always_comb begin : request_manager
    trng_ready_o = 1'b1;
    cf_next_o = 1'bx;
    eax_next_o = 'x;
    if(RAND_instr_flag_i) begin
        trng_ready_o = '0;
        cf_next_o = 1'b1;
        eax_next_o = $urandom_range(2^32,-(2^32));
    end
end : request_manager

trivium_top trivium (
    .clk(clk),
    .rst(!rst_n),

    .adc_in(),
    .adc_wr(),

    .req(),
    
    .p(),
    .q()
);

endmodule
