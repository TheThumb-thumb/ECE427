package params
    localparam IV_WIDTH = 80;
    localparam SETUP_TIME = 1151; // Cycles needed for trivium to cycle through internal state 4 times = 4 x 288 = 1152
    localparam ADC_FIF0_DEPTH = 80;
    localparam KEY_WIDTH = 1024;    

endpackage

package le_types
import params::*;

    typedef enum logic [1:0] {
        IDLE = 2'b00, 
        IV_GEN = 2'b01, 
        SETUP = 2'b11, 
        GEN = 2'b10

    } trivium_state_t;

    typedef enum logic [2:0] {

        // Idle while generating primes from trng
        IDLE = 3'b000;    
        // from Idle we go into primality once the trng outputs two odd random values
        PRIMALITY = 3'b001;
        // if primality fails then go into idle after dumping values and wait for two random values again
        // Modulus is waiting for p*q to output for our key n to be generated of length 2048
        MODULUS = 3'b011;
        // find lcm(p-1, q-1) using euclidean algo
        LAMBDA = 3'b010;
        // check if e we picked is coprime, e is between 1 < lcm(p-1,q-1)
        COPRIME = 3'b100;
        // e inverse mod lambda of n is d which is our secret decryption key! find d using extended euclid algo
        INVERSE = 3'b101;
        // output public key, store decryption key, discard everything else and return back to idle
        DONE = 3'b111;

    } encryption_state_t;

    typedef enum logic [2:0] {

        IDLE = 3'b000;    
        INIT_K = 3'b001;
        NORMALIZE_A = 3'b011;
        NORMALIZE_A = 3'b010;
        COMPUTE = 3'b100;
        DONE = 3'b101;


    } gcd_state_t;


endpackage
