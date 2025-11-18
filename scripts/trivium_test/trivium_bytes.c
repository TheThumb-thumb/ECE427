// /* trivium_bytes.c
//  *
//  * Simple, standalone Trivium implementation (bit-oriented).
//  * Generates 8-bit outputs (one byte = 8 Trivium keystream bits, LSB-first).
//  *
//  * Key/IV format:
//  *   - key[10] and iv[10] are 80-bit values, stored as bytes.
//  *   - Bit ordering inside each byte is LSB-first: bit position j (0..79)
//  *     is (arr[j/8] >> (j%8)) & 1.
//  *
//  * This follows the TRIVIUM specification (De Canniere & Preneel).
//  *
//  * Output: prints keystream bytes in hex to stdout.
//  */

// #include <stdio.h>
// #include <stdint.h>
// #include <string.h>

// #define STATE_BITS 288

// /* Number of output bytes to print by default */
// #define OUT_BYTES 1

// /* Internal state: s[0] is s1 in the paper, s[287] is s288 */
// static uint8_t s[STATE_BITS];

// /* Utility: extract bit i (0..79) from byte array arr[10], LSB-first in each byte */
// static inline uint8_t bit_from_bytes_lsb(const uint8_t *arr, int i)
// {
//     return (arr[i / 8] >> (i & 7)) & 1;
// }

// /* Initialize state with 80-bit key and 80-bit IV (both 10 bytes).
//    Bits are placed according to the paper:
//    s1..s93 = K1..K80, 0..0
//    s94..s177 = IV1..IV80, 0..0
//    s178..s288 = 0..0 except s286=s287=s288=1
// */
// void trivium_init(const uint8_t key[10], const uint8_t iv[10])
// {
//     int i;

//     /* s1..s93  -> indices 0..92 (zero-based) */
//     for (i = 0; i < 93; ++i) {
//         if (i < 80) s[i] = bit_from_bytes_lsb(key, i);
//         else s[i] = 0;
//     }

//     /* s94..s177 -> indices 93..176 */
//     for (i = 93; i < 177; ++i) {
//         int j = i - 93;
//         if (j < 80) s[i] = bit_from_bytes_lsb(iv, j);
//         else s[i] = 0;
//     }

//     /* s178..s288 -> indices 177..287 */
//     for (i = 177; i < 288; ++i) s[i] = 0;

//     /* Set s286, s287, s288 = 1  (note indices are 0-based: 285,286,287) */
//     s[285] = 1;
//     s[286] = 1;
//     s[287] = 1;

//     /* Perform 4 * 288 initial update cycles without producing output (warm up) */
//     for (i = 0; i < 4 * 288; ++i) {
//         /* taps are 1-based in paper; convert to 0-based */
//         uint8_t t1 = s[65] ^ (s[90] & s[91]) ^ s[92] ^ s[170];
//         uint8_t t2 = s[161] ^ (s[174] & s[175]) ^ s[176] ^ s[263];
//         uint8_t t3 = s[242] ^ (s[285] & s[286]) ^ s[287] ^ s[68];

//         /* rotate registers */
//         /* (s1..s93) <- (t3, s1..s92)  */
//         /* (s94..s177) <- (t1, s94..s176) */
//         /* (s178..s288) <- (t2, s178..s287) */
//         int idx;
//         /* shift 1..93 */
//         for (idx = 92; idx >= 1; --idx) s[idx] = s[idx - 1];
//         s[0] = t3;

//         /* shift 94..177 (indices 93..176) */
//         for (idx = 176; idx >= 94; --idx) s[idx] = s[idx - 1];
//         s[93] = t1;

//         /* shift 178..288 (indices 177..287) */
//         for (idx = 287; idx >= 178; --idx) s[idx] = s[idx - 1];
//         s[177] = t2;
//     }
// }

// /* Produce one keystream bit (z) and update state */
// static inline uint8_t trivium_keystream_bit(void)
// {
//     uint8_t t1 = s[65] ^ (s[90] & s[91]) ^ s[92] ^ s[170];
//     uint8_t t2 = s[161] ^ (s[174] & s[175]) ^ s[176] ^ s[263];
//     uint8_t t3 = s[242] ^ (s[285] & s[286]) ^ s[287] ^ s[68];

//     uint8_t z = t1 ^ t2 ^ t3;

//     int idx;
//     /* rotate as in init */
//     for (idx = 92; idx >= 1; --idx) s[idx] = s[idx - 1];
//     s[0] = t3;

//     for (idx = 176; idx >= 94; --idx) s[idx] = s[idx - 1];
//     s[93] = t1;

//     for (idx = 287; idx >= 178; --idx) s[idx] = s[idx - 1];
//     s[177] = t2;

//     return z;
// }

// /* Produce one keystream byte (8 bits). Bits are appended LSB-first:
//    returned_byte bit0 = first generated keystream bit, bit7 = last (8th) generated bit.
// */
// uint8_t trivium_keystream_byte(void)
// {
//     uint8_t out = 0;
//     for (int i = 0; i < 8; ++i) {
//         uint8_t b = trivium_keystream_bit();
//         out |= (b << i);
//     }
//     return out;
// }

// /* Helper printing: print N keystream bytes as hex */
// void print_keystream_bytes(int n)
// {
//     for (int i = 0; i < n; ++i) {
//         uint8_t b = trivium_keystream_byte();
//         printf("%02x", b);
//         if ((i & 0xF) == 0xF) printf("\n");
//         else if (i != n - 1) printf(" ");
//     }
//     if (n % 16) printf("\n");
// }

// /* Example main: uses a sample key/iv; replace with your chosen values */
// int main(void)
// {
//     /* Example key and IV: 80 bits (10 bytes) each.
//        Replace these literals with desired key/IV bytes.
//        Format: { 0x12, 0x34, ..., 0xAB }
//        Bit ordering: LSB-first inside each byte (i.e., lowest-order bit of byte is K1, etc.)
//     */
//     uint8_t key[10] = { 0xAD, 0xBF, 0x13, 0x1A, 0xB2, 0xC9, 0x3A, 0xAE, 0x16, 0x5D }; /* example */
//     uint8_t iv[10]  = { 0x2F, 0xD9, 0xA2, 0xAC, 0xF3, 0x77, 0x58, 0x1D, 0x8B, 0xA1 }; /* example */

//     /* Initialize and warm-up */
//     trivium_init(key, iv);

//     /* Print keystream bytes */
//     print_keystream_bytes(OUT_BYTES);

//     return 0;
// }


// single bit:


/* trivium_bit.c
 *
 * Standalone Trivium implementation (bit-oriented).
 * Generates a single keystream bit (0 or 1).
 */

#include <stdio.h>
#include <stdint.h>

#define STATE_BITS 288

/* Internal state: s[0] is s1 in the paper, s[287] is s288 */
static uint8_t s[STATE_BITS];

/* Utility: extract bit i (0..79) from byte array arr[10], LSB-first */
static inline uint8_t bit_from_bytes_lsb(const uint8_t *arr, int i)
{
    return (arr[i / 8] >> (i & 7)) & 1;
}

/* Initialize with 80-bit key and 80-bit IV */
void trivium_init(const uint8_t key[10], const uint8_t iv[10])
{
    int i;

    /* s1..s93 = K1..K80, 0..0 */
    for (i = 0; i < 93; ++i)
        s[i] = (i < 80) ? bit_from_bytes_lsb(key, i) : 0;

    /* s94..s177 = IV1..IV80, 0..0 */
    for (i = 93; i < 177; ++i) {
        int j = i - 93;
        s[i] = (j < 80) ? bit_from_bytes_lsb(iv, j) : 0;
    }

    /* s178..s288 = 0..0 except last three bits = 1 */
    for (i = 177; i < 288; ++i) s[i] = 0;
    s[285] = s[286] = s[287] = 1;

    /* 4×288 warm-up cycles */
    for (i = 0; i < 4 * 288; ++i) {
        uint8_t t1 = s[65] ^ (s[90] & s[91]) ^ s[92] ^ s[170];
        uint8_t t2 = s[161] ^ (s[174] & s[175]) ^ s[176] ^ s[263];
        uint8_t t3 = s[242] ^ (s[285] & s[286]) ^ s[287] ^ s[68];

        /* rotate */
        for (int idx = 92; idx >= 1; --idx) s[idx] = s[idx - 1];
        s[0] = t3;

        for (int idx = 176; idx >= 94; --idx) s[idx] = s[idx - 1];
        s[93] = t1;

        for (int idx = 287; idx >= 178; --idx) s[idx] = s[idx - 1];
        s[177] = t2;
    }
}

/* Generate one keystream bit */
uint8_t trivium_keystream_bit(void)
{
    uint8_t t1 = s[65] ^ (s[90] & s[91]) ^ s[92] ^ s[170];
    uint8_t t2 = s[161] ^ (s[174] & s[175]) ^ s[176] ^ s[263];
    uint8_t t3 = s[242] ^ (s[285] & s[286]) ^ s[287] ^ s[68];

    uint8_t z = t1 ^ t2 ^ t3;

    /* rotate */
    for (int idx = 92; idx >= 1; --idx) s[idx] = s[idx - 1];
    s[0] = t3;

    for (int idx = 176; idx >= 94; --idx) s[idx] = s[idx - 1];
    s[93] = t1;

    for (int idx = 287; idx >= 178; --idx) s[idx] = s[idx - 1];
    s[177] = t2;

    return z & 1;
}

int main(void)
{
    uint8_t key[10] = { 0xAD, 0xBF, 0x13, 0x1A, 0xB2, 0xC9, 0x3A, 0xAE, 0x16, 0x5D };
    uint8_t iv[10]  = { 0x2F, 0xD9, 0xA2, 0xAC, 0xF3, 0x77, 0x58, 0x1D, 0x8B, 0xA1 };

    int N = 1024;  /* number of keystream bits to generate */

    FILE *f = fopen("trivium_bits.txt", "w");
    if (!f) {
        perror("fopen");
        return 1;
    }

    trivium_init(key, iv);

    for (int i = 0; i < N; ++i) {
        uint8_t bit = trivium_keystream_bit();
        printf("%d\n", bit);            // console output, each bit per line
        fprintf(f, "%d\n", bit);        // file output, each bit per line
    }

    fclose(f);
    printf("Wrote %d bits (line-separated) to trivium_bits.txt\n", N);
    return 0;
}