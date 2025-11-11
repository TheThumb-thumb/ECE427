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
    input  logic        debug, 
    input  logic [5:0]  output_buffer_control,

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
logic req_is_rdrand;
assign req_is_rdrand = rand_req_type[2];

//Rdseed queue stuff
localparam PTR_WIDTH = $clog2(RDSEED_QUEUE_LENGTH);
logic [PTR_WIDTH:0] seed_queue_head, seed_queue_tail;
logic [PTR_WIDTH-1:0] seed_queue_head_i, seed_queue_tail_i;
logic [DATA_LENGTH-1:0] rdseed_queue [RDSEED_QUEUE_LENGTH];
logic [4:0] seed_counter;
logic rdseed_valid;

//Rdrand buffer stuff
rdrand_load_state_t rdrand_cur_state, rdrand_next_state;
logic [1:0] triv_counter;
localparam TRIV_INS_PER_BUFFER = (128 / 64);
logic [127:0] rdrand_buffer;
logic [3:0] rand_counter;
logic [5:0] rdrand_request_counter;
logic triv_mode, triv_mode_true;
logic rdrand_valid;

//Misc + for both
output_buffer_state_t ob_cur_state, ob_next_state;
logic [2:0] out_counter;
logic extended_rst_n;

//Drive registers based on if debug mode is active
logic [4:0] slow_clk_threshold;
always_comb begin
    if(debug && output_buffer_control[5:1] != '0) begin
        slow_clk_threshold = output_buffer_control[5:1];
        triv_mode_true = output_buffer_control[0];
    end else begin
        slow_clk_threshold = 4;
        triv_mode_true = triv_mode;
    end
end 

//Need to drive outputs at a slow clock of 100 MHz, or clk/5
logic [4:0] slow_clk_counter;
always_ff @ (posedge clk) begin
    if(!rst_n) begin
        slow_clk_counter <= '0;
        slow_clk <= '0;
        extended_rst_n <= '0;
    end else begin
        if(slow_clk_counter == slow_clk_threshold) begin
            slow_clk_counter <= '0;
            slow_clk <= ~slow_clk;
            if(!extended_rst_n && slow_clk) extended_rst_n <= '1;
        end
        else slow_clk_counter <= slow_clk_counter + 1;
    end
end

//Register host pins

// Control the seed queue
logic seedq_full, seedq_empty, overflow;
assign seed_ready_o = ~seedq_full;
assign seed_queue_head_i = seed_queue_head[PTR_WIDTH-1:0];
assign seed_queue_tail_i = seed_queue_tail[PTR_WIDTH-1:0];
assign overflow = seed_queue_head[PTR_WIDTH] != seed_queue_tail[PTR_WIDTH];
always_comb begin
    if(seed_queue_head_i == seed_queue_tail_i) begin
        if(overflow) begin // the true pointers line up but the overflow bit is high, queue is seedq_full
            seedq_full = '1;
            seedq_empty = '0;
        end else begin // the true pointers line up but the oveflow bit is low, queue is seedq_empty
            seedq_full = '0;
            seedq_empty = '1;
        end
    end else begin  //normal state, ready for standard operation
        seedq_full = '0;
        seedq_empty = '0;
    end
end

//Process block for loading the RDSEED Queue
always_ff @ (posedge clk) begin
    if(!rst_n) begin
        for(int i = 0; i < RDSEED_QUEUE_LENGTH; i++) rdseed_queue[i] <= '0;
        seed_queue_head <= '0;
    end else begin
        if(seed_valid_i && seed_ready_o) begin
            rdseed_queue[seed_queue_head_i] <= seed_port_i;
            seed_queue_head <= seed_queue_head + 1;
        end
    end
end

//Process blocks for loading the RDRAND Buffer
always_ff @ (posedge clk) begin
    if(!rst_n) begin
        rdrand_cur_state <= RDRAND_BUF_INVALID;
        triv_counter <= '0;
    end else begin

        case (rdrand_cur_state)
            RDRAND_BUF_INVALID: begin

            end RDRAND_LOAD_DRBG: begin
                if(rand_valid_i) rdrand_buffer <= rand_port_i;
            end RDRAND_LOAD_TRIV: begin
                if(triv_valid_i) begin
                    rdrand_buffer[64 * triv_counter +: 64] <= triv_port_i;
                    triv_counter <= triv_counter + 1'b1;
                end
            end RDRAND_BUF_VALID: begin

            end default: begin
                
            end
        endcase

        rdrand_cur_state <= rdrand_next_state;
    end
end

always_comb begin
    if(rdrand_request_counter >= 45 || triv_debug) triv_mode = 1'b1;
    else triv_mode = 1'b0;

    triv_ready_o = 1'b0;
    rand_ready_o = 1'b0;
    rdrand_next_state = rdrand_cur_state;

    case (rdrand_cur_state)
        RDRAND_BUF_INVALID: begin
            if(!rdrand_valid) begin
                if(triv_mode_true) rdrand_next_state = RDRAND_LOAD_TRIV;
                else rdrand_next_state = RDRAND_LOAD_DRBG;
            end
        end RDRAND_LOAD_DRBG: begin
            rand_ready_o = 1'b1;
            if(rand_valid_i) rdrand_next_state = RDRAND_BUF_VALID;
        end RDRAND_LOAD_TRIV: begin
            triv_ready_o = 1'b1;
            if(triv_counter == '1) rdrand_next_state = RDRAND_BUF_VALID;
        end RDRAND_BUF_VALID: begin
            if(rand_counter == 4'd8 && rdrand_valid) begin
                rdrand_next_state = RDRAND_BUF_INVALID;
            end
        end default: begin
            
        end
    endcase
end

//Process blocks for outputting numbers to Host 
always_ff @ (posedge slow_clk) begin
    if(!extended_rst_n) begin
        seed_queue_tail <= '0;
        seed_counter <= '0;
        rand_counter <= '0;
        out_counter <= '0;
        rdrand_request_counter <= '0;
        ob_cur_state <= OUTPUT_IDLE;
        rdrand_valid <= '0;
        rdseed_valid <= '0;
    end else begin

        if(ob_cur_state != ob_next_state) begin
            if(ob_next_state == OUTPUT_RAND && rdrand_request_counter != '1) begin
                rdrand_request_counter <= rdrand_request_counter + 1'b1;
            end else if (ob_next_state == OUTPUT_SEED && rdrand_request_counter != '0) begin
                rdrand_request_counter <= rdrand_request_counter - 1'b1;
            end
        end

        case(ob_cur_state)
            OUTPUT_IDLE: begin
                if(rand_req) begin
                    unique case (rand_req_type)
                        RDSEED_16, RDRAND_16: begin 
                            out_counter <= 3'd0;
                        end RDSEED_32, RDRAND_32: begin
                            out_counter <= 3'd1;
                        end RDSEED_64, RDRAND_64: begin 
                            out_counter <= 3'd3;
                        end
                        default: begin
                        end
                    endcase

                end
            end OUTPUT_SEED: begin
                if(rdseed_valid) begin 
                    if(seed_counter == OUTS_PER_SEED) begin
                        seed_counter <= '0;
                        seed_queue_tail <= seed_queue_tail + 1;
                    end else begin
                        seed_counter <= seed_counter + 1;
                    end
                    if(out_counter != '0) out_counter <= out_counter - 1'b1;
                end
            end OUTPUT_RAND: begin
                if(rand_counter != 4'd8 && rdrand_valid) begin
                    rand_counter <= rand_counter + 1'b1;
                    if(out_counter != '0) out_counter <= out_counter - 1'b1;
                end
            end default: begin
                
            end
        endcase
        
        if(rdrand_cur_state == RDRAND_BUF_VALID) rdrand_valid <= '1;
        else if(rdrand_cur_state == RDRAND_BUF_INVALID) begin 
            rdrand_valid <= '0;
            rand_counter <= '0;
        end

        if(!seedq_empty) rdseed_valid <= 1'b1;
        else rdseed_valid <= 1'b0;

        ob_cur_state <= ob_next_state;
    end
end

always_comb begin
    rand_valid = 1'b0;
    rand_byte = '0;
    ob_next_state = ob_cur_state;
    if(!output_stall_temp) begin
        case(ob_cur_state)
            OUTPUT_IDLE: begin
                if(rand_req) begin
                    if(req_is_rdrand) ob_next_state = OUTPUT_RAND;
                    else ob_next_state = OUTPUT_SEED;
                end
            end OUTPUT_SEED: begin
                if(rdseed_valid) begin
                    rand_byte = rdseed_queue[seed_queue_tail_i][OUTPUT_WIDTH * seed_counter +: OUTPUT_WIDTH];
                    rand_valid = 1'b1;
                    if(out_counter == '0) ob_next_state = OUTPUT_IDLE;
                end
            end OUTPUT_RAND: begin
                if(rand_counter != 4'd8 && rdrand_valid) begin
                    rand_byte = rdrand_buffer[OUTPUT_WIDTH * rand_counter +: OUTPUT_WIDTH];
                    rand_valid = 1'b1;
                    if(out_counter == '0) ob_next_state = OUTPUT_IDLE;
                end
            end default: begin
                
            end
        endcase
    end
end


endmodule