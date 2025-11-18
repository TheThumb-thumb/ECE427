module streaming_bit_compactor #(
    parameter int WIDTH = 32,
    parameter int BUFFER_WIDTH = 64
)(
    input  logic                 clk,
    input  logic                 rst,
    input  logic [WIDTH-1:0]     data_in,
    input  logic [WIDTH-1:0]     mask_in,
    input  logic                 valid_in,       // asserts when new data_in/mask_in are valid
    output logic [WIDTH-1:0]     data_out,       // full word of compacted bits
    output logic                 valid_out      // one-cycle pulse when data_out is valid
);

    // Internal state
    logic [BUFFER_WIDTH-1:0] buffer;
    logic [$clog2(BUFFER_WIDTH+1)-1:0] buffer_count;

    // Temporary signals
    logic [WIDTH-1:0] compacted;
    logic [$clog2(WIDTH+1)-1:0] num_good_bits;

    logic [BUFFER_WIDTH-1:0] next_buffer;
    logic [$clog2(BUFFER_WIDTH+1)-1:0] next_count;

    logic flag;

    always_comb begin
        compacted = '0;
        num_good_bits = '0;
        if (!rst) begin
            compacted = '0;
            num_good_bits = '0;
        end else begin
            for (int i = 0; i < WIDTH; i++) begin
                if (mask_in[i] && valid_in) begin
                    compacted[num_good_bits] = data_in[i];
                    num_good_bits++;
                end
            end
        end
    end

    always_comb begin
        next_buffer = buffer;
        next_count = num_good_bits;
        if (!rst) begin
            next_buffer = '0;
            next_count = '0;
        end else begin
            if (valid_in) begin
                next_buffer = buffer[WIDTH-1:0] | (compacted << buffer_count);
                next_count  = buffer_count + num_good_bits;
            end
        end
    end

    always_ff @(posedge clk) begin
        if (!rst) begin
            buffer          <= '0;
            buffer_count    <= '0;
            valid_out       <= 1'b0;
            data_out        <= '0;
            flag <= '0;
        end else begin
            valid_out <= 1'b0;  // default low

            if (valid_in) begin
                // Predict next state

                // Append new bits

                // Check if we have a full output word
                if (next_count >= WIDTH && !flag) begin
                    flag <= 1'b1;
                    data_out     <= next_buffer[WIDTH-1:0];
                    buffer       <= next_buffer >> WIDTH;
                    buffer_count <= next_count - WIDTH;
                end else if (next_count >= WIDTH && flag) begin
                    // Output one full 32-bit word
                    data_out  <= next_buffer[WIDTH-1:0];
                    valid_out <= 1'b1;
                    // Shift leftover bits and update buffer
                    buffer       <= next_buffer >> WIDTH;
                    buffer_count <= next_count - WIDTH;
                end else begin
                    // Not enough bits yet, update partial buffer
                    buffer       <= next_buffer;
                    buffer_count <= next_count;
                end
            end
        end
    end

endmodule

