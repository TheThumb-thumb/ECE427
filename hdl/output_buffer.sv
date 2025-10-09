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
    DATA_LENGTH = 256,
    RDSEED_QUEUE_LENGTH = 8
)(
    // System Signals
    input  logic        clk,
    input  logic        rst_n,

    //Connections to DRBG and Conditioner
    input logic                     seed_valid_i, 
    input logic [DATA_LENGTH-1:0]   seed_port_i,
    output logic                    seed_ready_o,

    input logic                         rand_valid_i,
    input logic [(DATA_LENGTH/2)-1:0]   rand_port_i,
    output logic                        rand_ready_o,

    //CPU I/O Pins
    input logic rand_req,               // Request pin (active high)
    input rand_req_t rand_req_type,     // Request type (see types.sv for scheme) 
    output logic [7:0] rand_byte,       // Byte-sliced output
    output logic rand_valid             // Output valid signal (active high)

);

localparam PTR_LENGTH = $clog2(RDSEED_QUEUE_LENGTH);
logic [PTR_LENGTH-1:0] seed_queue_head, seed_queue_tail;
logic [256:0] rdseed_queue [RDSEED_QUEUE_LENGTH];
logic [256:0] rdrand_reg;
logic [2:0] byte_counter;

//Need to drive outputs at a slow clock of 100 MHz, or clk/5
logic slow_clk;
logic [2:0] div_five_counter;
always_ff @ (posedge clk) begin
    if(!rst_n) begin
        seed_queue_head <= '0;
        slow_clk <= '0;
        div_five_counter <= '0;
    end else begin
        if(div_five_counter == 4) begin
            div_five_counter <= '0;
            slow_clk <= ~slow_clk;
        end
        else div_five_counter <= div_five_counter + 1;
    end
end

output_buffer_state_t current_state, next_state;

always_ff @ (posedge slow_clk) begin
    if(!rst_n) begin
        for(int i = 0; i < RDSEED_QUEUE_LENGTH; i++) rdseed_queue[i] <= '0;
        rdrand_reg <= '0;
        byte_counter <= '0;
        current_state <= OUTPUT_IDLE;
    end else begin
        current_state <= next_state;

        if(current_state == OUTPUT_IDLE && rand_req) begin
            unique case (rand_req_type)
                RDSEED_16, RDRAND_16: begin 
                    byte_counter <= 3'd1;
                end RDSEED_32, RDRAND_32: begin
                    byte_counter <= 3'd3;
                end RDSEED_64, RDRAND_64: begin 
                    byte_counter <= 3'd7;
                end
                default: begin
                    
                end
            endcase
        end else if(current_state == OUTPUT_BYTES) begin
            byte_counter <= byte_counter - 1'b1;
        end else if(current_state == OUTPUT_DONE) begin
            
        end

    end
end

always_comb begin
    next_state = current_state;
    rand_byte = '0;

    rand_byte = 1'b0;
    rand_valid = 1'b0;

    seed_ready_o = 1'b1;
    rand_ready_o = 1'b1;

    unique case (current_state)
        OUTPUT_IDLE:begin 
            if(rand_req) begin
                next_state = OUTPUT_BYTES;
            end
        end OUTPUT_BYTES: begin
            rand_valid = 1'b1;
            if(byte_counter == 0) begin 
                next_state = OUTPUT_IDLE;
            end
            rand_byte = rdseed_queue[seed_queue_head][8 * byte_counter +: 8];
        end default: begin
            
        end
    endcase
end


endmodule