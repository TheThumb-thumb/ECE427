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
    localparam calib_bits = 8;
    localparam es_sources = 64;
    localparam latch_sources = 32;
    localparam jitter_sources = 32;
    localparam sram_addr = 2048;
    localparam sram_word = 32;
endpackage : params

package le_types;

    typedef enum logic [2:0] {
        RDSEED_16 = 3'd0,
        RDRAND_16 = 3'd1,
        RDSEED_32 = 3'd2,
        RDRAND_32 = 3'd3,
        RDSEED_64 = 3'd4,
        RDRAND_64 = 3'd5
    } rand_req_t;

    typedef enum logic [1:0] {
        idle = 2'b00,
        que_wr = 2'b10,
        que_rd = 2'b01,
        que_rd_wr = 2'b11
    } fifo_state_t;

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

endpackage: le_types
