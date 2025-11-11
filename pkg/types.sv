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
    localparam DATA_WIDTH = 256;
    localparam cond_width = 384;
    localparam calib_bits = 6;
    localparam es_sources = 64;
    localparam latch_sources = 32;
    localparam jitter_sources = 32;
    localparam sram_addr = 2048;
    localparam sram_word = 32;
    localparam OUTPUT_WIDTH = 16;
    localparam TEMP_WIDTH = 14;
endpackage : params

package le_types;
    import params::*;

    typedef enum logic [2:0] {
        RDSEED_16 = 3'b000,
        RDRAND_16 = 3'b100,
        RDSEED_32 = 3'b001,
        RDRAND_32 = 3'b101,
        RDSEED_64 = 3'b010,
        RDRAND_64 = 3'b110
    } rand_req_t;

    typedef enum logic [1:0] {
        idle = 2'b00,
        que_wr = 2'b10,
        que_rd = 2'b01,
        que_rd_wr = 2'b11
    } fifo_state_t;

    typedef enum logic [2:0] {
        TRIV_IDLE, 
        SETUP, 
        GEN,
        DEBUG_SETUP,
        DEBUG_GEN
    } trivium_state_t;

    typedef enum logic [2:0] {
        S_IDLE,
        S_INIT_ADD_KEY,
        S_PROCESS_ROUNDS,
        S_FINAL_ROUND,
        S_DONE
    } aes_core_state_t;

    typedef enum logic [1:0] { 
        IDLE,
        FIRST_HALF,
        SECOND_HALF,
        DONE
    } aes_cbc_mac_state_t;

    typedef struct packed {
        // BASIC IO PINS
        logic [10:0] addr;
        logic [31:0] data;
        logic flag; // indicates whether we should start using the values provided by input for comparison
    } sram_dp_reg_t;

    //Output buffer

    //State machine for loading the RDRAND Buffer
    typedef enum logic [1:0] {
        RDRAND_BUF_INVALID,
        RDRAND_LOAD_DRBG,
        RDRAND_LOAD_TRIV,
        RDRAND_BUF_VALID
    } rdrand_load_state_t;

    typedef enum logic [1:0] { 
        OUTPUT_IDLE,
        OUTPUT_SEED,
        OUTPUT_RAND
    } output_buffer_state_t;

    typedef struct packed {
        logic [es_sources-1:0] ES_in;
        logic [latch_sources-1:0][calib_bits-1:0] arr_n, arr_p;
        logic [jitter_sources-1:0] j_disable_arr;
        logic [es_sources-1:0] rd_good_arr;
    } oht_output_t;

endpackage: le_types
