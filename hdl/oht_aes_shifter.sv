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
    output logic                 valid_out,      // asserts when data_out is full
    output logic [$clog2(WIDTH+1)-1:0] num_good_bits_debug
);

    logic [BUFFER_WIDTH-1:0] buffer;
    logic [$clog2(BUFFER_WIDTH+1)-1:0] buffer_count;

    logic [WIDTH-1:0] compacted;
    logic [$clog2(WIDTH+1)-1:0] num_good_bits;

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

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            buffer        <= '0;
            buffer_count  <= '0;
            valid_out     <= 1'b0;
            data_out      <= '0;
        end else if (valid_in) begin
            buffer[buffer_count +: WIDTH] <= compacted;
            buffer_count <= buffer_count + num_good_bits;

            if (buffer_count + num_good_bits >= WIDTH) begin
                data_out  <= buffer[WIDTH-1:0];
                valid_out <= 1'b1;

                buffer     <= buffer >> WIDTH;
                buffer_count <= (buffer_count + num_good_bits) - WIDTH;
            end else begin
                valid_out <= 1'b0;
            end
        end else begin
            valid_out <= 1'b0;
        end
    end

    assign num_good_bits_debug = num_good_bits;

endmodule
