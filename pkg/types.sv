package params;
    localparam IV_WIDTH = 80;
    localparam SETUP_TIME = 1151; // Cycles needed for trivium to cycle through internal state 4 times = 4 x 288 = 1152
    localparam ADC_FIF0_DEPTH = 80;
    localparam ENTROPY_SAMPLE = 1024;   
    localparam ENTROPY_CUTOFF = 588;
    localparam SAMPLE_SIZE = 256;   
    localparam C_INTER = 22;
    localparam C_PERM = 32;
    localparam OUTREG_MAX_WIDTH = 64;

endpackage : params

package le_types;

    typedef enum logic [1:0] {
        TRIV_IDLE, 
        IV_GEN, 
        SETUP, 
        GEN
    } trivium_state_t;

    typedef enum logic {  
        RDRAND  = 1'b0,
        RDSEED  = 1'b1
    } rand_instr_t;

    typedef enum logic [1:0] {  
        _16bit   = 2'b00,
        _32bit   = 2'b01,
        _64bit   = 2'b10
    } rand_width_t;

    // typedef enum logic [2:0] {

    //     // Idle while generating primes from trng
    //     ENCR_IDLE,
    //     // from Idle we go into primality once the trng outputs two odd random values
    //     PRIMALITY,
    //     // if primality fails then go into idle after dumping values and wait for two random values again
    //     // Modulus is waiting for p*q to output for our key n to be generated of length 2048
    //     MODULUS,
    //     // find lcm(p-1, q-1) using euclidean algo
    //     LAMBDA,
    //     // check if e we picked is coprime, e is between 1 < lcm(p-1,q-1)
    //     COPRIME,
    //     // e inverse mod lambda of n is d which is our secret decryption key! find d using extended euclid algo
    //     INVERSE,
    //     // output public key, store decryption key, discard everything else and return back to idle
    //     ENCR_DONE

    // } encryption_state_t;

    // typedef enum logic [2:0] {
    //     GCD_IDLE,    
    //     INIT_K,
    //     NORMALIZE_A,
    //     NORMALIZE_B,
    //     COMPUTE,
    //     GCD_DONE
    // } gcd_state_t;

    // typedef enum logic [2:0] {
    //     IDLE,
    //     MONT_SPACE_A,
    //     MONT_SPACE_B,
    //     MONT_MULT,
    //     INVERSE,
    //     DONE
    // } mont_mult_state_t;


endpackage: le_types
