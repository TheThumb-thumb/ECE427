/*
 * Module: aes_round_final.sv
 *
 * Description: SystemVerilog implementation of a AES trasnformation final round
 *
 * Behavior: Implements three AES steps (SubBtyes, ShiftRows, AddRoundKey)
 * on a 128 bit input vector with a 128 bit roundkey
 */
module aes_round_final (
    input  logic [127:0] state_in_i,
    input  logic [127:0] round_key_in_i,
    output logic [127:0] state_out_o
);

// Step 1: SubBytes
logic [7:0] sub_bytes_in    [16];
logic [7:0] sub_bytes_out   [16];
logic [127:0] sub_bytes_concat;

generate for (genvar i = 0; i < 16; i++) begin : gen_sub_bytes
    sbox sbox (sub_bytes_in[i], sub_bytes_out[i]);
    assign sub_bytes_in[i] = state_in_i[127 - 8*i -: 8];
    assign sub_bytes_concat[127 - 8*i -: 8] = sub_bytes_out[i];
end endgenerate

// Step 2: ShiftRows
logic [127:0] shift_rows_out;

always_comb begin
    // Row 0 (no shift)
    shift_rows_out[127:120] = sub_bytes_concat[127:120];
    shift_rows_out[95:88]   = sub_bytes_concat[95:88];
    shift_rows_out[63:56]   = sub_bytes_concat[63:56];
    shift_rows_out[31:24]   = sub_bytes_concat[31:24];
    // Row 1 (shift left by 1)
    shift_rows_out[119:112] = sub_bytes_concat[87:80];
    shift_rows_out[87:80]   = sub_bytes_concat[55:48];
    shift_rows_out[55:48]   = sub_bytes_concat[23:16];
    shift_rows_out[23:16]   = sub_bytes_concat[119:112];
    // Row 2 (shift left by 2)
    shift_rows_out[111:104] = sub_bytes_concat[47:40];
    shift_rows_out[79:72]   = sub_bytes_concat[15:8];
    shift_rows_out[47:40]   = sub_bytes_concat[111:104];
    shift_rows_out[15:8]    = sub_bytes_concat[79:72];
    // Row 3 (shift left by 3)
    shift_rows_out[103:96]  = sub_bytes_concat[7:0];
    shift_rows_out[71:64]   = sub_bytes_concat[103:96];
    shift_rows_out[39:32]   = sub_bytes_concat[71:64];
    shift_rows_out[7:0]     = sub_bytes_concat[39:32];
end

//Step 3: AddRoundKey
assign state_out_o = shift_rows_out ^ round_key_in_i;

endmodule : aes_round_final