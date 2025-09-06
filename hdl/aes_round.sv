/*
 * Module: aes_round.sv
 *
 * Description: SystemVerilog implementation of an AES trasnformation round
 *
 * Behavior: Implements the four AES steps (SubBtyes, ShiftRows, MixColumns, AddRoundKey)
 * on a 128 bit input vector with a 128 bit roundkey
 */
module aes_round (
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

//Step 3: MixColumns

// Helper function for Galois Field Mulitplication
function logic [7:0] gmul(logic [7:0] b);
    return (b[7]) ? ((b << 1) ^ 8'h1B) : (b << 1);
endfunction

logic [127:0] mix_cols_out;
logic [7:0] s [4][4];
logic [7:0] s_prime [4][4];
    
always_comb begin
    // Map 1D vector to 2D state array
    for (int c=0; c<4; c++) begin
        for (int r=0; r<4; r++) begin
                s[r][c] = shift_rows_out[127-(c*32 + r*8) -: 8];
        end
    end

    // Perform MixColumns matrix multiplication
    for (int i = 0; i < 4; i++) begin
        s_prime[0][i] = gmul(s[0][i]) ^ (gmul(s[1][i]) ^ s[1][i]) ^ s[2][i] ^ s[3][i];
        s_prime[1][i] = s[0][i] ^ gmul(s[1][i]) ^ (gmul(s[2][i]) ^ s[2][i]) ^ s[3][i];
        s_prime[2][i] = s[0][i] ^ s[1][i] ^ gmul(s[2][i]) ^ (gmul(s[3][i]) ^ s[3][i]);
        s_prime[3][i] = (gmul(s[0][i]) ^ s[0][i]) ^ s[1][i] ^ s[2][i] ^ gmul(s[3][i]);
    end

    // Map 2D array back to 1D vector
    for (int c=0; c<4; c++) begin
        for (int r=0; r<4; r++) begin
                mix_cols_out[127-(c*32 + r*8) -: 8] = s_prime[r][c];
        end
    end
end

//Step 4: AddRoundKey
assign state_out_o = mix_cols_out ^ round_key_in_i;

endmodule : aes_round