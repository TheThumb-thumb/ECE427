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
    output logic                 valid_out,      // one-cycle pulse when data_out is valid
    output logic [$clog2(WIDTH+1)-1:0] num_good_bits_debug
);

    // Internal state
    logic [BUFFER_WIDTH-1:0] buffer;
    logic [$clog2(BUFFER_WIDTH+1)-1:0] buffer_count;

    // Temporary signals
    logic [WIDTH-1:0] compacted;
    logic [$clog2(WIDTH+1)-1:0] num_good_bits;

    // ------------------------------------------
    // Compact data_in based on mask_in
    // ------------------------------------------
    always_comb begin
        compacted = '0;
        num_good_bits = '0;
        for (int i = 0; i < WIDTH; i++) begin
            if (mask_in[i]) begin
                compacted[num_good_bits] = data_in[i];
                num_good_bits++;
            end
        end
    end

    // ------------------------------------------
    // Streaming buffer / output logic
    // ------------------------------------------
    always_ff @(posedge clk) begin
        if (rst) begin
            buffer        <= '0;
            buffer_count  <= '0;
            valid_out     <= 1'b0;
            data_out      <= '0;
        end else begin
            valid_out <= 1'b0;  // default low

            if (valid_in) begin
                // Predict next state
                logic [BUFFER_WIDTH-1:0] next_buffer;
                logic [$clog2(BUFFER_WIDTH+1)-1:0] next_count;

                // Append new bits (concatenate compacted at current buffer_count position)
                next_buffer = buffer | (compacted << buffer_count);
                next_count  = buffer_count + num_good_bits;

                // Check if we have a full output word
                if (next_count >= WIDTH) begin
                    // Output one full 32-bit word
                    data_out  <= next_buffer[WIDTH-1:0];
                    valid_out <= 1'b1;

                    // Shift leftover bits and update buffer
                    buffer       <= next_buffer >> WIDTH;
                    buffer_count <= next_count - WIDTH;
                end else begin
                    // Not enough bits yet — just update partial buffer
                    buffer       <= next_buffer;
                    buffer_count <= next_count;
                end
            end
        end
    end

    assign num_good_bits_debug = num_good_bits;

endmodule
