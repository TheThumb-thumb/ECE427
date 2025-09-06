module que
import rv32i_types::*;
#(

    parameter DEPTH = 8,
    parameter WIDTH = 256
)(
    input logic clk,
    input logic rst,
    input logic inter_fail,
    input logic perm_fail,

    input logic [WIDTH-1:0] wdata,
    output logic [WIDTH-1:0] rdata,

    input logic enque,
    input logic deque,

    output logic full,
    output logic empty
    
);
    logic [$clog2(DEPTH)-1:0] head_reg, tail_reg;
    logic [$clog2(DEPTH)-1:0] head_next, tail_next;
    
    logic [WIDTH-1:0] que_data [DEPTH]; //holds DEPTH instructions that each consist of WIDTH bits
    logic filled;   //indicates overflow
    logic [$clog2(DEPTH):0] counter_reg, counter_next;    //tracks if overflow has occurred or not. if MSB is high, queue is full
    // state_t state;

    // state 0: idle state, nothing is happening
    // state 1: we have to enque an instruction
    // state 2: we have to deque an instruction
    // state 3: we have to enque and deque an instruction
    // state 4: full/empty?

    // always_ff @(posedge clk) begin

    //     if (rst)
    //         state <= idle;
    //     else
    //         state <= {enque, deque};
    //         // state <= state'({enque , deque});

    // end

    always_ff @(posedge clk) begin

        if (rst || inter_fail || perm_fail) begin
            counter_reg <= '0;
            head_reg <= '0;
            tail_reg <= '0;
        end
        else begin
            counter_reg <= counter_next;
            head_reg <= head_next;
            tail_reg <= tail_next;
        end

    end

    always_comb begin

        head_next = head_reg;
        tail_next = tail_reg;
        counter_next = counter_reg;
        
        unique case ({enque, deque})

            idle:
            begin
                if (rst) begin // pretty sure this does nothing now
                    head_next = '0;
                    tail_next = '0;
                end

                // do nothing if rst is low
                rdata = 'x;

            end

            que_wr:
            begin
                // enqueue is high -- insert data into tail location of queue and update tail location, if queue is not full
                if (!counter_reg[$clog2(DEPTH)]) begin
                    que_data[tail_reg] = wdata;
                    tail_next = tail_reg + 1'b1;
                    counter_next = counter_reg + 1'b1;
                end
                // if queue is full, set filled signal to high
                
                
            end

            que_rd:
            begin
                // dequeue is high -- remove head element by incrementing head location
                if (!empty && !counter_reg[$clog2(DEPTH)]) begin
                    rdata = que_data[head_reg];
                    head_next = head_reg + 1'b1;
                    counter_next = counter_reg - 1'b1;
                end
            end

            que_rd_wr:
            begin
                
                // if enque and deque at the same time then tail should not increment or decrement
                // 
                if(empty) begin
                    //if queue is empty -- do nothing
                    rdata = wdata;
                end
                
                else begin
                    // otherwise, dequeue then enqueue
                    rdata = que_data[head_reg];
                    head_next = head_reg + 1'b1;

                    que_data[tail_reg] = wdata;
                    tail_next = tail_reg + 1'b1;
                end
                
            end

            default:
            begin

                rdata = 'x;
                counter_next = '0;

            end

        endcase

    end

    always_comb begin

        full = 1'b0;
        empty = 1'b0;

        if (counter_next[$clog2(DEPTH)] && head_reg == tail_next)
            full = 1'b1;

        if (!counter_next[$clog2(DEPTH)] && head_reg == tail_next)
            empty = 1'b1;

    end

    
endmodule : que