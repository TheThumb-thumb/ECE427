module trivium_top 
import params::*;
import le_types::*;
(

    input logic                         clk,
    input logic                         rst,
    
    input logic                         adc_in,
    input logic                         adc_wr,
    input logic                         req,    // Requesting encryption keys

    output logic [KEY_WIDTH-1:0]        p,
    output logic [KEY_WIDTH-1:0]        q
    // maybe a done signal as well saying key is generated prepare to receive on bus?
    // ^^ might be handled based on bus protocol

);
    trivium_state_t curr_state, next_state;

    logic [IV_WIDTH-1:0] iv_, key_, vector;
    logic [10:0] setup_cnt;
    logic iv_full, iv_empty, done, key_full, cs_en, full, deque, key_req;

    adc_rng_fifo fifo0 (
         .clk(clk),
         .rst(rst),
         .enque(adc_wr),
         .deque(deque),
         .data(adc_in),
         .vector(vector),
         .full(full)
    );

    trivium rng (
        .clk(clk),
        .rst(rst),
        .iv_(iv_),
        .key_(key_),

        .state(curr_state),
        .done(done),
        .p(p),
        .q(q)
    );

    assign iv_full = full;
    assign deque = (full && curr_state != IDLE) ? '1 : '0;
    assign iv_ = iv_full ? vector : 'x;
    assign key_ = key_full ? vector : 'x;

    always_comb begin
        next_state = IDLE; 
        key_full = '0;
        cs_en = '0;
        key_req = '0;
        if (rst) begin
            next_state = IDLE;
        end

    /*  IDLE - Do nothing until request is sent for a key
        IV_GEN - Random key generated from ADC
        SETUP - Random iv generated from ADC start trivium setup
        GEN - Generating keys for encryption and hashing -> check for primality before validation */

        unique case (curr_state)
            IDLE: begin

                cs_en = 1'b0;
                if (req) begin
                    key_req = 1'b1;
                end
                else if (iv_full && key_req) begin
                    key_full = 1'b1;
                    next_state = IV_GEN;
                    key_req = 1'b0;
                end

            end

            IV_GEN: begin

                cs_en = 1'b0;
                if (iv_full) begin
                    key_full = 1'b0;
                    next_state = SETUP;
                end

            end

            SETUP: begin

                cs_en = 1'b1;
                if (setup_cnt == SETUP_TIME) begin
                    next_state = GEN;
                end

            end

            GEN: begin

                cs_en = 1'b1;
                if (done) begin
                    next_state = IDLE;
                end

            end

            default: begin
                cs_en = 'x;
                next_state = 'x;
                key_full = 'x;
            end
        endcase

    end

    always_ff @( posedge clk ) begin : trivium_state
        
        curr_state <= next_state;

        setup_cnt <= '0;
        if (curr_state == SETUP) begin
            setup_cnt <= setup_cnt + 1'b1;
        end else if (curr_state == GEN) begin
            if (setup_cnt == SETUP_TIME) begin
                setup_cnt <= '0;
            end
            setup_cnt <= setup_cnt + 1'b1;
        end

    end



endmodule : trivium_top
