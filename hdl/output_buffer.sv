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

    input logic                     rand_valid_i,
    input logic [DATA_LENGTH-1:0]   rand_port_i,
    output logic                    rand_ready_o

    //CPU I/O Pins
    input logic rand_req,               // Request pin (active high)
    input rand_req_t rand_req_type,     // Request type (see types.sv for scheme) 
    output logic [7:0] rand_byte,       // Byte-sliced output
    output logic rand_valid,            // Output valid signal (active high)

);

localparam PTR_LENGTH = clog2(RDSEED_QUEUE_LENGTH);
logic 
logic [256:0] rdseed_queue [RDSEED_QUEUE_LENGTH];
logic [256:0] rdrand_reg;
logic [2:0] byte_counter;

typedef enum logic [3:0] { 
    IDLE,
    OUTPUT_BYTES,
    DONE
} output_buffer_state_t;

output_buffer_state_t current_state, next_state;

always_ff @ (posedge clk) begin
    if(!rst_n) begin
        rdseed_queue <= '0;
        rdrand_reg <= '0;
        byte_counter <= '0;
        current_state <= IDLE;
    end else begin
        current_state <= next_state;

        if(current_state == IDLE && rand_req) begin
            unique case (rand_req_type)
                RDSEED_16, RDRAND_16: begin 
                    byte_counter <= 3'd1;
                end RDSEED_32, RDRAND_32: begin
                    byte_counter <= 3'd3;
                end RDSEED_64, RDRAND_64: begin 
                    byte_counter <= 3'd7;
                end
            endcase
        end
    end
end

always_comb begin
    next_state = current_state;

    rand_byte = 1'b0;
    rand_valid = 1'b0;

    seed_ready_o = 1'b1;
    rand_ready_o = 1'b1;

    unique case (current_state)
        IDLE:
            if(rand_req) begin
                next_state = OUTPUT_BYTES;
            end
        OUTPUT_BYTES:
            rand_valid = 1'b1;

        DONE:

    endcase
end


endmodule