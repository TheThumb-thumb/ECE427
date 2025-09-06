/*
Module: aes_df_90a.sv

Purpose:
    - NIST SP 800-90A Rev1 Block_Cipher_df (AES-128)
    - Derive OUT_BITS (= seedlen, typically 256) bits of seed material from an
    - arbitrary-length input_string using the approved Block_Cipher_df algorithm.

In Progress:
    - Using aes_core (ECB encrypt, 128-bit) for Block_Encrypt
    - Implements BCC (same thing as CBC-MAC with zero iv) internally
    - All byte ordering assumes leftmost byte map to MSBs of vectors

    - Algorithm(SP 800-90A §10.3.2):
        Let outlen=128, keylen=128 (AES-128)
        InputString = user supp bytes
        1) L = bitlen(InputString) as a 32-bit big-endian integer
        2) N = OUT_BITS as a 32-bit big-endian integer
        3) S = L || N || InputString || 0x80 || 0x00 ...  (pad to 128-bit multiple)
        4) temp = "" ; i = 0 ; K = 0x00010203_04050607_08090A0B_0C0D0E0F
            while |temp| < (keylen + outlen = 256):
                IV = i (32 bits) || 0^(96)
                temp = temp || BCC(K, IV || S)
                i = i + 1
        5) K = leftmost 128 bits of temp
        6) X = next 128 bits of temp
        7) temp2 = ""
            while |temp2| < OUT_BITS:
                X = AES-Encrypt(K, X)
                temp2 = temp2 || X
        8) requested_bits = leftmost OUT_BITS of temp2
 */


module aes_df_90a #(
    parameter int MAX_IN_BYTES = 256,     // max supported input_string length(bytes)
    parameter int OUT_BITS = 256          // req number of output bits(seedlen)
)(
    input  logic                          clk,
    input  logic                          rst_n,
    input  logic                          start_i,                     // one-cycle start pulse
    
    // inp string(bytes) & its actual len in bytes (<= MAX_IN_BYTES)
    input  logic [$clog2(MAX_IN_BYTES+1)-1:0] in_len_bytes_i,
    input  logic [8*MAX_IN_BYTES-1:0]         in_bytes_i,              // left-aligned (MSB=first byte)

    
    output logic                          done_o,                      // pulses high when output valid
    output logic [OUT_BITS-1:0]              requested_bits_o          // OUT_BITS seed material (left-aligned/MSB-first)
);
// K Init from 10.3.2 Intel DRNG

// Gonna implement S = L || N || InputString || 0x80 || pad0s to multiple of 16 bytes
// S_bytes as left aligned B vector of length S_len_bytes

// Combinationally make S, assuming in_len_bytes_i is stable

// AES core instantiation

// DF FSM

// Need to work out rest of logic for registers & AES driving

endmodule