module adc_rng_fifo 
import params::*;

(
    input clk,
    input rst,
    input logic enque,
    input logic deque,
    input logic data,

    output logic [ADC_FIF0_DEPTH-1:0] vector,
    output logic full
);

    typedef enum logic [1:0] {
        idle = 2'b00,
        wr = 2'b10,
        rd = 2'b01,
        rd_wr = 2'b11
    } state_t;


    logic [3:0] head_next, head_cur;
    //  count_cur, count_next;
    logic [ADC_FIF0_DEPTH-1:0] vector_cur;
    logic [ADC_FIF0_DEPTH-1:0] vector_next;
    logic overflow;
    logic empty;

    always_ff @(posedge clk) begin

        if (rst) begin
            head_cur <= '0;
            // tail_cur <= '0;
            // count_cur <= '0;
        end else begin
            head_cur <= head_next;
            // tail_cur <= tail_next;
            vector_cur <= vector_next;
            // count_cur <= count_next;
        end
        
    end

    always_comb begin

        head_next = head_cur;
        // tail_next = tail_cur;
        // count_next = count_cur;
        vector_next = vector_cur;
        vector = '0;

        unique case ({enque, deque})
            
            idle : begin
                // DO NOTHING
            end

            rd : begin
                if (!empty) begin
                    vector = vector_cur;
                    head_next = '0;
                    // count_next = '0;
                    // tail_next = '0;
                end
            end

            wr : begin
                if (count_cur != 10) begin
                    vector_next[head_cur] = data;
                    // tail_next = tail_cur + 1'b1;
                    head_next = head_cur + 1'b1;
                    // count_next = count_cur + 1'b1;
                end
            end

            rd_wr : begin

                vector = vector_cur;
                head_next = 1'b1;
                // count_next = 1'b1;
                vector_next[head_next] = data;
                // vector_next[tail_cur] = data;
                // tail_next = tail_cur + 1'b1;
            end

            default: begin
                vector = '0;
                // count_next = '0;
            end
        endcase
    end

    always_comb begin

        full = 1'b0;
        empty = 1'b0;

        // if (count_cur == 10 && head_cur == 10) begin
        if (head_cur == 10) begin
            full = 1'b1;
        end
        // if (count_cur == 0 && head_cur == 0) begin
        if (head_cur == 0) begin
            empty = 1'b1;
        end

    end

endmodule : adc_rng_fifo
