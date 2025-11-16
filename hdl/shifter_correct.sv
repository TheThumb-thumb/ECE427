// module streaming_bit_compactor #(
//     parameter int WIDTH = 32,
//     parameter int BUFFER_WIDTH = 64
// )(
//     input  logic                 clk,
//     input  logic                 rst,
//     input  logic [WIDTH-1:0]     data_in,
//     input  logic [WIDTH-1:0]     mask_in,
//     input  logic                 valid_in,       // asserts when new data_in/mask_in are valid
//     output logic [WIDTH-1:0]     data_out,       // full word of compacted bits
//     output logic                 valid_out      // one-cycle pulse when data_out is valid
// );

// logic [31:0] good_buff;
// logic [4:0] num_good_bits;

// always_comb begin
//     good_buff = '0;
//     num_good_bits = '0;
//     for (int i =0; i < WIDTH; i++) begin
//         if (mask_in[num_good_bits] == 1'b1) begin
//             num_good_bits++;
//         end
//     end
//     if (valid_in) begin
//         good_buff[]
//     end

// end

// endmodule