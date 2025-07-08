module trivium_top #(
    parameter ADC_WIDTH = 8;
    parameter IV_WIDTH = 80;
    parameter SETUP_TIME = 1151; // Cycles needed for trivium to cycle through internal state 4 times = 4 x 288 = 1152
)(

    input logic                         clk,
    input logic                         rst,
    input logic [ADC_WIDTH-1:0]         adc_in,
    input logic                         adc_wr,

    output logic test

);


    enum logic [1:0] {IDLE=0, SETUP, GEN} curr_state, next_state;
    logic [10:0] setup_cnt;
    logic iv_full, iv_empty, done;

    always_comb begin
        next_state = IDLE;
        if (rst) begin
            next_state = IDLE;
        end
        else if (setup_cnt == SETUP_TIME) begin
            next_state = GEN;
        end
        else if (done) begin
            next_state = IDLE;
        end
        else if (iv_full) begin
            next_state = SETUP;
        end
        else begin
            next_state = IDLE;
        end

    end

    always_ff @( posedge clk ) begin : trivium_state
        
        curr_state <= next_state;

        setup_cnt <= '0;
        if (curr_state == SETUP) begin
            setup_cnt <= setup_cnt + 1'b1;
        end
    end

    

endmodule : trivium_top