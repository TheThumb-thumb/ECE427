/* trivium_8parallel.c
 *
 * Standalone Trivium implementation (reference-style word ops),
 * producing 8-bit-parallel outputs (one byte = 8 keystream bits,
 * LSB-first). Uses the same style macros as the reference C.
 *
 * Compile:
 *   gcc -O2 trivium_8parallel.c -o trivium_8parallel
 *
 * Usage:
 *   ./trivium_8parallel [key80hex] [iv80hex] [nbytes]
 *
 * Example:
 *   ./trivium_8parallel 0123456789ABCDEF0010 1032547698BADCFE0001 32
 *
 * If key/iv not supplied, example defaults are used.
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <ctype.h>

/* --- types & helpers (small subset of ecrypt-sync.h used by reference) --- */
typedef uint8_t u8;
typedef uint32_t u32;

static u32 U8TO32_LITTLE(const u8 *b) {
    return ((u32)b[0]) | ((u32)b[1] << 8) | ((u32)b[2] << 16) | ((u32)b[3] << 24);
}
static void U32TO8_LITTLE(u8 *b, u32 v) {
    b[0] = (u8)(v & 0xFF);
    b[1] = (u8)((v >> 8) & 0xFF);
    b[2] = (u8)((v >> 16) & 0xFF);
    b[3] = (u8)((v >> 24) & 0xFF);
}
static u8 U8V(u32 x) { return (u8)(x & 0xFF); }

/* --- context --- */
typedef struct {
    u8 key[10];
    u8 s[37]; /* storage of 288-bit state & small padding (same layout used by ref code) */
    u32 keylen; /* bytes */
    u32 ivlen;  /* bytes */
} ECRYPT_ctx;

/* --- Reference-style S/T macros adapted for local variables used by LOAD/STORE --- */
/* We'll keep S(a,n) to expand to s##a##n local variables inside functions. */
/* The code below uses the same UPDATE/ROTATE/LOAD/STORE macros as the reference. */

#define S00(a, b) ((S(a, 1) << ( 32 - (b))))
#define S32(a, b) ((S(a, 2) << ( 64 - (b))) | (S(a, 1) >> ((b) - 32)))
#define S64(a, b) ((S(a, 3) << ( 96 - (b))) | (S(a, 2) >> ((b) - 64)))
#define S96(a, b) ((S(a, 4) << (128 - (b))) | (S(a, 3) >> ((b) - 96)))

/* UPDATE and ROTATE macros follow the reference implementation */
#define UPDATE()                                                             \
  do {                                                                       \
    T(1) = S64(1,  66) ^ S64(1,  93);                                        \
    T(2) = S64(2,  69) ^ S64(2,  84);                                        \
    T(3) = S64(3,  66) ^ S96(3, 111);                                        \
                                                                             \
    Z(T(1) ^ T(2) ^ T(3));                                                   \
                                                                             \
    T(1) ^= (S64(1,  91) & S64(1,  92)) ^ S64(2,  78);                       \
    T(2) ^= (S64(2,  82) & S64(2,  83)) ^ S64(3,  87);                       \
    T(3) ^= (S96(3, 109) & S96(3, 110)) ^ S64(1,  69);                       \
  } while (0)

#define ROTATE()                                                             \
  do {                                                                       \
    S(1, 3) = S(1, 2); S(1, 2) = S(1, 1); S(1, 1) = T(3);                    \
    S(2, 3) = S(2, 2); S(2, 2) = S(2, 1); S(2, 1) = T(1);                    \
    S(3, 4) = S(3, 3); S(3, 3) = S(3, 2); S(3, 2) = S(3, 1); S(3, 1) = T(2); \
  } while (0)

#define LOAD(sarr)                                                            \
  do {                                                                       \
    S(1, 1) = U8TO32_LITTLE((sarr) +  0);                                    \
    S(1, 2) = U8TO32_LITTLE((sarr) +  4);                                    \
    S(1, 3) = U8TO32_LITTLE((sarr) +  8);                                    \
                                                                             \
    S(2, 1) = U8TO32_LITTLE((sarr) + 12);                                    \
    S(2, 2) = U8TO32_LITTLE((sarr) + 16);                                    \
    S(2, 3) = U8TO32_LITTLE((sarr) + 20);                                    \
                                                                             \
    S(3, 1) = U8TO32_LITTLE((sarr) + 24);                                    \
    S(3, 2) = U8TO32_LITTLE((sarr) + 28);                                    \
    S(3, 3) = U8TO32_LITTLE((sarr) + 32);                                    \
    S(3, 4) = U8TO32_LITTLE((sarr) + 36);                                    \
  } while (0)

#define STORE(sarr)                                                            \
  do {                                                                       \
    U32TO8_LITTLE((sarr) +  0, S(1, 1));                                     \
    U32TO8_LITTLE((sarr) +  4, S(1, 2));                                     \
    U32TO8_LITTLE((sarr) +  8, S(1, 3));                                     \
                                                                             \
    U32TO8_LITTLE((sarr) + 12, S(2, 1));                                     \
    U32TO8_LITTLE((sarr) + 16, S(2, 2));                                     \
    U32TO8_LITTLE((sarr) + 20, S(2, 3));                                     \
                                                                             \
    U32TO8_LITTLE((sarr) + 24, S(3, 1));                                     \
    U32TO8_LITTLE((sarr) + 28, S(3, 2));                                     \
    U32TO8_LITTLE((sarr) + 32, S(3, 3));                                     \
    U32TO8_LITTLE((sarr) + 36, S(3, 4));                                     \
  } while (0)

/* Small helpers for hex parsing (expects exactly 20 hex digits for 80 bits) */
static int hexchar2int(char c) {
    if ('0' <= c && c <= '9') return c - '0';
    if ('a' <= c && c <= 'f') return 10 + (c - 'a');
    if ('A' <= c && c <= 'F') return 10 + (c - 'A');
    return -1;
}
static int parse80bits_hex(const char *hex20, u8 out[10]) {
    if (!hex20) return 0;
    int len = (int)strlen(hex20);
    /* allow optional 0x prefix */
    const char *p = hex20;
    if (len >= 2 && hex20[0] == '0' && (hex20[1] == 'x' || hex20[1] == 'X')) p += 2;
    int rem = (int)strlen(p);
    if (rem != 20) return 0;
    for (int i = 0; i < 10; ++i) {
        int hi = hexchar2int(p[2*i]);
        int lo = hexchar2int(p[2*i + 1]);
        if (hi < 0 || lo < 0) return 0;
        out[i] = (u8)((hi << 4) | lo);
    }
    return 1;
}

/* --- Implementation adapted from the reference code (ECRYPT_keysetup / ivsetup / process) --- */

/* ECRYPT_init does nothing here */
void ECRYPT_init(void) { }

/* ECRYPT_keysetup: store key bytes and keylen */
void ECRYPT_keysetup(ECRYPT_ctx *ctx, const u8 *key, u32 keysize, u32 ivsize) {
    ctx->keylen = (keysize + 7) / 8;
    ctx->ivlen  = (ivsize  + 7) / 8;
    memset(ctx->key, 0, sizeof(ctx->key));
    for (u32 i = 0; i < ctx->keylen && i < 10; ++i) ctx->key[i] = key[i];
}

/* In the reference code the s[] array is 37 bytes; we follow that layout */
#define S(a, n) (s##a##n)
#define T(a) (t##a)
void ECRYPT_ivsetup(ECRYPT_ctx* ctx, const u8* iv) {
    u32 i;
    /* s[] initial bytes: key (12 bytes region), iv next, rest zeros as reference did.
       We'll populate ctx->s[] according to the reference code expectations. */
    /* note: reference code copied 12 bytes of key into ctx->s[0..11] though keylen <=10; we follow original layout */
    for (i = 0; i < ctx->keylen && i < 12; ++i) ctx->s[i] = ctx->key[i];
    for (i = ctx->keylen; i < 12; ++i) ctx->s[i] = 0;
    for (i = 0; i < ctx->ivlen && i < 12; ++i) ctx->s[i + 12] = iv[i];
    for (i = ctx->ivlen; i < 12; ++i) ctx->s[i + 12] = 0;
    for (i = 0; i < 13; ++i) ctx->s[i + 24] = 0;
    ctx->s[13 + 24] = 0x70; /* as in ref */

    /* Now load into 32-bit local words and run 4*9 cycles (warm-up) */
    {
        u32 s11, s12, s13;
        u32 s21, s22, s23;
        u32 s31, s32, s33, s34;
        u32 t11, t12, t13; /* T(1)..T(3) locals */

        /* map macro names to local vars used by macros:
           we use names s11..s34 and t11.. so the macros below expand correctly */
        /* Bind local names to macro expectation via defines */
        /* We'll simulate LOAD(ctx->s) */
        S(1,1) = U8TO32_LITTLE(ctx->s + 0);
        S(1,2) = U8TO32_LITTLE(ctx->s + 4);
        S(1,3) = U8TO32_LITTLE(ctx->s + 8);
        S(2,1) = U8TO32_LITTLE(ctx->s + 12);
        S(2,2) = U8TO32_LITTLE(ctx->s + 16);
        S(2,3) = U8TO32_LITTLE(ctx->s + 20);
        S(3,1) = U8TO32_LITTLE(ctx->s + 24);
        S(3,2) = U8TO32_LITTLE(ctx->s + 28);
        S(3,3) = U8TO32_LITTLE(ctx->s + 32);
        S(3,4) = U8TO32_LITTLE(ctx->s + 36);

#define Z(w) /* warmup ignores outputs */
        for (i = 0; i < 4 * 9; ++i) {
            u32 t1, t2, t3;
            /* the UPDATE/ROTATE macros operate on S(.,.) and T(.) macros */
            /* To let the macros pick up our local variable names, we create aliases via defines below */
            /* However to keep things simple and avoid redefining macros per-block, we'll implement a direct expansion here */
            /* Expand same operations as UPDATE + ROTATE but using local S/T names */
            /* Use the same formulas as macros but with our S(.,.) and T(.) */
            /* compute t1,t2,t3 exactly as macros would */
            t1 = S64(1,  66) ^ S64(1,  93);
            t2 = S64(2,  69) ^ S64(2,  84);
            t3 = S64(3,  66) ^ S96(3, 111);
            /* Z(t1 ^ t2 ^ t3) -> ignored */
            t1 ^= (S64(1,  91) & S64(1,  92)) ^ S64(2,  78);
            t2 ^= (S64(2,  82) & S64(2,  83)) ^ S64(3,  87);
            t3 ^= (S96(3, 109) & S96(3, 110)) ^ S64(1,  69);

            /* rotate */
            S(1,3) = S(1,2); S(1,2) = S(1,1); S(1,1) = t3;
            S(2,3) = S(2,2); S(2,2) = S(2,1); S(2,1) = t1;
            S(3,4) = S(3,3); S(3,3) = S(3,2); S(3,2) = S(3,1); S(3,1) = t2;
        }
#undef Z

        /* store back */
        U32TO8_LITTLE(ctx->s + 0, S(1,1));
        U32TO8_LITTLE(ctx->s + 4, S(1,2));
        U32TO8_LITTLE(ctx->s + 8, S(1,3));
        U32TO8_LITTLE(ctx->s + 12, S(2,1));
        U32TO8_LITTLE(ctx->s + 16, S(2,2));
        U32TO8_LITTLE(ctx->s + 20, S(2,3));
        U32TO8_LITTLE(ctx->s + 24, S(3,1));
        U32TO8_LITTLE(ctx->s + 28, S(3,2));
        U32TO8_LITTLE(ctx->s + 32, S(3,3));
        U32TO8_LITTLE(ctx->s + 36, S(3,4));
    }
}

/* Produce one byte (8 keystream bits LSB-first) using 8 UPDATE/ROTATE cycles but using word macros.
   This re-loads the ctx->s bytes into local 32-bit words, runs 8 cycles capturing each Z, then stores back.
*/
uint8_t trivium_keystream_byte(ECRYPT_ctx *ctx) {
    /* local 32-bit state words matching macros S(.,.) */
    u32 s11, s12, s13;
    u32 s21, s22, s23;
    u32 s31, s32, s33, s34;
    u32 t1, t2, t3;
    u8 out = 0;

    /* LOAD */
    s11 = U8TO32_LITTLE(ctx->s + 0);
    s12 = U8TO32_LITTLE(ctx->s + 4);
    s13 = U8TO32_LITTLE(ctx->s + 8);
    s21 = U8TO32_LITTLE(ctx->s + 12);
    s22 = U8TO32_LITTLE(ctx->s + 16);
    s23 = U8TO32_LITTLE(ctx->s + 20);
    s31 = U8TO32_LITTLE(ctx->s + 24);
    s32 = U8TO32_LITTLE(ctx->s + 28);
    s33 = U8TO32_LITTLE(ctx->s + 32);
    s34 = U8TO32_LITTLE(ctx->s + 36);

    /* To let macros work, provide macro aliases to local names */
#undef S
#undef T
#define S(a,n) ( (a==1 && n==1) ? s11 : \
                 (a==1 && n==2) ? s12 : \
                 (a==1 && n==3) ? s13 : \
                 (a==2 && n==1) ? s21 : \
                 (a==2 && n==2) ? s22 : \
                 (a==2 && n==3) ? s23 : \
                 (a==3 && n==1) ? s31 : \
                 (a==3 && n==2) ? s32 : \
                 (a==3 && n==3) ? s33 : \
                 (a==3 && n==4) ? s34 : 0 )
#define T(a) ( (a==1) ? t1 : (a==2) ? t2 : t3 )

    /* Define Z to capture the produced 32-bit w but we only want its LSB(s) as bits.
       The reference UPDATE macro's Z(w) is expected to put w into output; here we
       need each Z output (w) to be reduced to a single bit value per bit-iteration:
       in Trivium the Z output is a single bit (since used with U8TO32 in ref when processing bytes).
       However in the 32-bit-word variant the Z macro writes a 32-bit word when processing 32-bit blocks.
       For 8-bit parallel we want the lowest-order bit of the XOR output for each UPDATE.
    */
#define Z(w) do { uint32_t wtmp = (w); uint8_t zbit = (uint8_t)(wtmp & 1u); /* take LSB */ \
                   /* pack into out (LSB-first) */ out |= (zbit << bit_iter); } while(0)

    /* Perform 8 UPDATE+ROTATE steps, collecting 8 bits */
    for (int bit_iter = 0; bit_iter < 8; ++bit_iter) {
        /* compute t1,t2,t3 using macros S64,S96 which in turn use S(...) above */
        t1 = S64(1,  66) ^ S64(1,  93);
        t2 = S64(2,  69) ^ S64(2,  84);
        t3 = S64(3,  66) ^ S96(3, 111);

        Z(t1 ^ t2 ^ t3);

        t1 ^= (S64(1,  91) & S64(1,  92)) ^ S64(2,  78);
        t2 ^= (S64(2,  82) & S64(2,  83)) ^ S64(3,  87);
        t3 ^= (S96(3, 109) & S96(3, 110)) ^ S64(1,  69);

        /* rotate: set S(1,3)=S(1,2); S(1,2)=S(1,1); S(1,1)=t3; etc.
           We must write back into the correct local variables.
        */
        /* expand rotate assignments manually */
        s13 = s12; s12 = s11; s11 = t3;
        s23 = s22; s22 = s21; s21 = t1;
        s34 = s33; s33 = s32; s32 = s31; s31 = t2;
    }

    /* clean up macros */
#undef Z
#undef S
#undef T

    /* STORE back into ctx->s */
    U32TO8_LITTLE(ctx->s + 0, s11);
    U32TO8_LITTLE(ctx->s + 4, s12);
    U32TO8_LITTLE(ctx->s + 8, s13);
    U32TO8_LITTLE(ctx->s + 12, s21);
    U32TO8_LITTLE(ctx->s + 16, s22);
    U32TO8_LITTLE(ctx->s + 20, s23);
    U32TO8_LITTLE(ctx->s + 24, s31);
    U32TO8_LITTLE(ctx->s + 28, s32);
    U32TO8_LITTLE(ctx->s + 32, s33);
    U32TO8_LITTLE(ctx->s + 36, s34);

    return out;
}

/* Convenience: create ctx, keysetup, ivsetup */
void setup_ctx_with_keyiv(ECRYPT_ctx *ctx, const u8 key[10], const u8 iv[10]) {
    ECRYPT_keysetup(ctx, key, 80, 80);
    memset(ctx->s, 0, sizeof(ctx->s));
    /* Reference code expects some initial s[] assignment inside ivsetup; we call ivsetup directly */
    ECRYPT_ivsetup(ctx, iv);
}

/* --- main: parse args and print keystream bytes in hex --- */
int main(int argc, char **argv) {
    u8 iv[10] = { 0x2F,0xD9,0xA2,0xAC,0xF3,0x77,0x58,0x1D,0x8B,0xA1 }; /* default example */
    u8 key[10]  = { 0xAD,0xBF,0x13,0x1A,0xB2,0xC9,0x3A,0xAE,0x16,0x5D }; /* default example */
    int nbytes = 32;

    if (argc >= 2) {
        if (!parse80bits_hex(argv[1], key)) {
            fprintf(stderr, "Bad key hex (expect 20 hex digits). Using default key.\n");
        }
    }
    if (argc >= 3) {
        if (!parse80bits_hex(argv[2], iv)) {
            fprintf(stderr, "Bad iv hex (expect 20 hex digits). Using default iv.\n");
        }
    }
    if (argc >= 4) {
        nbytes = atoi(argv[3]);
        if (nbytes <= 0) nbytes = 32;
    }

    ECRYPT_ctx ctx;
    setup_ctx_with_keyiv(&ctx, key, iv);

    for (int i = 0; i < nbytes; ++i) {
        uint8_t b = trivium_keystream_byte(&ctx);
        printf("%02x", b);
        if (i + 1 == nbytes) printf("\n");
        else if ((i & 0xF) == 0xF) printf("\n");
        else printf(" ");
    }

    return 0;
}
