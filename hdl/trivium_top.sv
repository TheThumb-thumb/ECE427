module trivium_top 
import params::*;
import le_types::*;
(

    input logic                         clk,
    input logic                         rst,
    
    input logic [DATA_WIDTH-1:0]        cond_in,
    input logic                         cond_valid,    // Conditioner has sent seed for trivium
    // input logic                         stall,         // if you want to stall trivium and check bits sent out

    output logic                        seed_req,      // request new seed after 2048 cycles of use so gives some cycles for buffers to fill up if needed
    output logic                        triv_ready,    // after initial 1152 steps it can start generating so this shows that
    output logic [7:0]                  rrand_out      // provide 8 random bits to pins if rrand instruction give
);
    trivium_state_t curr_state, next_state;

    logic [IV_WIDTH-1:0] iv_, key_;
    logic [159:0] vector;
    logic [10:0] setup_cnt;
    logic flag, done;

    trivium rng (
        .clk(clk),
        .rst(rst),
        .iv_(iv_),
        .key_(key_),

        .state(curr_state),
        .byte_stream(rrand_out),
        .done(done)
    );

    always_ff @(posedge clk) begin
        if (rst) begin
            vector <= 'x;
            flag <= '0;
        end else if (cond_valid) begin
            vector <= cond_in[159:0];
            flag <= '1;
        end else begin
            // do nothing
        end
    end

    // assign iv_full = full;
    // assign deque = (full && curr_state != TRIV_IDLE) ? '1 : '0;
    // assign iv_ = iv_full ? vector : 'x;
    // assign key_ = key_full ? vector : 'x;

    assign iv_ = vector[159:80];
    assign key_ = vector[79:0];

    always_comb begin
        next_state = curr_state; 

    /*  TRIV_IDLE - Do nothing until request is sent for a key
        SETUP - Random iv generated from ADC start trivium setup
        GEN - Generating keys for encryption and hashing -> check for primality before validation */

        unique case (curr_state)
            TRIV_IDLE: begin
                if (flag) begin
                    next_state = SETUP;
                end
                seed_req = 1'b0;
                triv_ready = 1'b0;
            end
            SETUP: begin
                if (setup_cnt == SETUP_TIME) begin
                    next_state = GEN;
                end
                seed_req = 1'b0;
                triv_ready = 1'b0;
            end
            GEN: begin
                triv_ready = 1'b1;
                seed_req = 1'b0;
                if (done) begin
                    next_state = TRIV_IDLE;
                    seed_req = 1'b1;
                end
            end
            default: begin
                next_state = curr_state;
                seed_req = 1'b0;
                triv_ready = 1'b0;
            end
        endcase
    end

    always_ff @( posedge clk ) begin : trivium_state
        if (rst) begin
            curr_state <= TRIV_IDLE;
            setup_cnt <= '0;
        end else if (curr_state == SETUP) begin
            curr_state <= next_state;
            setup_cnt <= setup_cnt + 1'b1;
        end else if (curr_state == GEN) begin
            curr_state <= next_state;
            if (setup_cnt == SETUP_TIME) begin
                setup_cnt <= '0;
            end
            // setup_cnt <= setup_cnt + 1'b1;
        end else begin
            curr_state <= next_state;
        end
    end

endmodule : trivium_top
