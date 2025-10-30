/**
 * Output Buffer
 *
 * Manages the byte-slicing and returning of RDRAND and RDSEED numbers to the host CPU
 * also contains a seed queue that can fill up and halt operation (saving power) and provide
 * short term bursty performance for RDSEED
 *
 */
import le_types::*;
module output_buffer #(
    OUTPUT_WIDTH = 16,
    DATA_LENGTH = 256,
    RDSEED_QUEUE_LENGTH = 8
)(
    // System Signals
    input  logic        clk,
    input  logic        rst_n,
    input  logic        output_stall_temp,
    input  logic        triv_debug, // debug register is trying to stall debug

    //Connections to DRBG and Conditioner
    input logic                     seed_valid_i, 
    input logic [DATA_LENGTH-1:0]   seed_port_i,
    output logic                    seed_ready_o,

    input logic                         rand_valid_i,
    input logic [(DATA_LENGTH/2)-1:0]   rand_port_i,
    output logic                        rand_ready_o,

    input logic                         triv_valid_i,
    input logic [(DATA_LENGTH/4)-1:0]   triv_port_i,
    output logic                        triv_ready_o,

    //CPU I/O Pins
    input logic rand_req,                       // Request pin (active high)
    input rand_req_t rand_req_type,             // Request type (see types.sv for scheme) 
    output logic [OUTPUT_WIDTH-1:0] rand_byte,  // Byte-sliced output
    output logic rand_valid,                    // Output valid signal (active high)
    output logic slow_clk
);

//Constants
// Width for a value of (256 / OUTPUT_WIDTH)
localparam int OUTS_PER_SEED_WIDTH = (8 - $clog2(OUTPUT_WIDTH) + 1);
// Width for a value of (128 / OUTPUT_WIDTH)
localparam int OUTS_PER_RAND_WIDTH = (7 - $clog2(OUTPUT_WIDTH) + 1);

localparam logic [OUTS_PER_SEED_WIDTH:0] OUTS_PER_SEED = (DATA_LENGTH / OUTPUT_WIDTH) - 1;
localparam logic [OUTS_PER_RAND_WIDTH:0] OUTS_PER_RAND = (128 / OUTPUT_WIDTH) - 1;


//Output buffer sampled input registers
logic rand_req_reg, req_randflag;

//Rdseed queue stuff
localparam PTR_WIDTH = $clog2(RDSEED_QUEUE_LENGTH);
logic [PTR_WIDTH:0] seed_queue_head, seed_queue_tail;
logic [PTR_WIDTH-1:0] seed_queue_head_i, seed_queue_tail_i;
logic [DATA_LENGTH-1:0] rdseed_queue [RDSEED_QUEUE_LENGTH];
logic [2:0] out_counter;
logic [4:0] seed_counter;

//Rdrand buffer stuff
logic rdrand_buffer_valid, true_rand_ready, true_rand_valid;
logic [1:0] triv_counter;
localparam TRIV_INS_PER_BUFFER = (128 / 64);
logic [127:0] rdrand_buffer;
logic [2:0] rand_counter;


//Trivium/DRBG Switching logic
// If, of the last 64 requests, ~70% of them have been RDRAND (>= 45)
// We should switch to trivium for our RDRAND requests
logic [5:0] rdrand_request_counter;
logic triv_mode;

//Need to drive outputs at a slow clock of 100 MHz, or clk/5
logic [2:0] div_five_counter;
always_ff @ (posedge clk) begin
    if(!rst_n) begin
        div_five_counter <= '0;
        slow_clk <= '0;
    end else begin
        if(div_five_counter == 4) begin
            div_five_counter <= '0;
            slow_clk <= ~slow_clk;
        end
        else div_five_counter <= div_five_counter + 1;
    end
end

//Control the input buffers
always_ff @ (posedge clk) begin
    if(!rst_n) begin
        rand_req_reg <= '0;
        req_randflag <= '0;
    end else if (rand_req) begin
        req_randflag <= rand_req_type[2];
        if(out_counter == 3'd0) rand_req_reg <= 1'b0;
        else if(rand_req_reg == 1'b0) rand_req_reg <= 1'b1;
    end
end

// Control the seed queue
logic full, empty, overflow;
assign seed_ready_o = ~full;
assign seed_queue_head_i = seed_queue_head[PTR_WIDTH-1:0];
assign seed_queue_tail_i = seed_queue_tail[PTR_WIDTH-1:0];
assign overflow = seed_queue_head[PTR_WIDTH] != seed_queue_tail[PTR_WIDTH];
always_comb begin
    if(seed_queue_head_i == seed_queue_tail_i) begin
        if(overflow) begin // the true pointers line up but the overflow bit is high, queue is full
            full = '1;
            empty = '0;
        end else begin // the true pointers line up but the oveflow bit is low, queue is empty
            full = '0;
            empty = '1;
        end
    end else begin  //normal state, ready for standard operation
        full = '0;
        empty = '0;
    end
end

//Mux the inputs based on DRBG mode
always_comb begin
    if(rdrand_request_counter >= 45 || triv_debug) begin
        triv_mode = 1'b1;
    end else begin
        triv_mode = 1'b0;
    end

    if(triv_mode) begin
        true_rand_valid = triv_valid_i;
        triv_ready_o = true_rand_ready;
        rand_ready_o = 1'b0;
    end else begin
        true_rand_valid = rand_valid_i;
        triv_ready_o = 1'b0;
        rand_ready_o = true_rand_ready;
    end
end
assign true_rand_ready = (rand_counter == OUTS_PER_RAND && rdrand_buffer_valid == 1'b0) ? 1'b1 : 1'b0;

//Load the seed queue, rand buffer
always_ff @ (posedge clk) begin
    if(!rst_n) begin
        for(int i = 0; i < RDSEED_QUEUE_LENGTH; i++) rdseed_queue[i] <= '0;
        seed_queue_head <= '0;
        rdrand_buffer <= '0;
        triv_counter <= '0;
        rdrand_buffer_valid <= '0;
    end else begin
        if(seed_valid_i && seed_ready_o) begin
            rdseed_queue[seed_queue_head_i] <= seed_port_i;
            seed_queue_head <= seed_queue_head + 1;
        end

        if(true_rand_ready && true_rand_valid) begin
            if(triv_mode) begin 
                rdrand_buffer[64 * triv_counter +: 64] <= triv_port_i;
                triv_counter <= triv_counter + 1;
                if(triv_counter == TRIV_INS_PER_BUFFER) rdrand_buffer_valid <= '1;
            end else begin 
                rdrand_buffer <= rand_port_i;
                rdrand_buffer_valid <= '1;
            end
        end else if(true_rand_valid && rand_counter == OUTS_PER_RAND && rand_valid && req_randflag) begin
            if(triv_mode) triv_counter <= '0;
            rdrand_buffer_valid <= '0;
        end
        
    end
end

//Empty the queue/buffer
always_ff @(posedge slow_clk or negedge rst_n) begin
    if(!rst_n) begin
        seed_counter <= '0;
        rand_counter <= OUTS_PER_RAND;
        out_counter <= '0;
        seed_queue_tail <= '0;
        rdrand_request_counter <= '0;
    end else if (!empty) begin

        if(rand_req && !rand_req_reg && ((rdrand_buffer_valid && req_randflag) || (!empty && !req_randflag))) begin
            unique case (rand_req_type)
                RDSEED_16, RDRAND_16: begin 
                    out_counter <= 3'd1;
                end RDSEED_32, RDRAND_32: begin
                    out_counter <= 3'd2;
                end RDSEED_64, RDRAND_64: begin 
                    out_counter <= 3'd4;
                end
                default: begin
                end
            endcase

            if(req_randflag && rdrand_request_counter != '1) begin
                rdrand_request_counter <= rdrand_request_counter + 1'b1;
            end else if (!req_randflag && rdrand_request_counter != '0) begin
                rdrand_request_counter <= rdrand_request_counter - 1'b1;
            end

        end else if(rand_req_reg) begin
            if(!req_randflag) begin
                out_counter <= out_counter - 1;
                if(seed_counter == OUTS_PER_SEED) begin
                    seed_counter <= '0;
                    seed_queue_tail <= seed_queue_tail + 1;
                end else begin
                    seed_counter <= seed_counter + 1;
                end
            end else if(rdrand_buffer_valid) begin
                out_counter <= out_counter - 1;
                rand_counter <= rand_counter + 1;
            end
        end

    end
end

always_comb begin
    rand_byte = '0;
    rand_valid = 1'b0;

    if(out_counter != '0) begin
        //  THIS IS SOMETHING I ADDED FOR output buffer stall on temp - Rohan 10/26 5:13pm
        if (output_stall_temp) begin 
            rand_valid = 1'b0;
        end else begin
            rand_valid = 1'b1;
        end
        // OG Code: rand_valid = 1'b1;
        if(req_randflag) begin 
            rand_byte = rdrand_buffer[OUTPUT_WIDTH * rand_counter +: OUTPUT_WIDTH];
        end else begin 
            rand_byte = rdseed_queue[seed_queue_tail_i][OUTPUT_WIDTH * seed_counter +: OUTPUT_WIDTH];
        end 
    end
end


endmodule