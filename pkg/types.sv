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
        logic [10:0] A;     // input | addresses A[0] = LSB
        logic [31:0] D;     // input | data inputs D[0] = LSB
        logic CEN;          // input | chip enable, active low
        logic WEN;          // input | write enable, active low
        logic CLK;          // input | clock
        logic [31:0] Q;     // output | Data outputs Q[0] = LSB
        // EXTRA MARGIN ADJUSTMENT PINS
        logic [2:0] EMA;    // Extra margin adjustment pins EMA[0] = LSB
        // BIST MUX PINS
        logic TEN;          // input | test mode enable, active low 0 = Test operation and 1 = Normal operation
        logic [10:0] TA;    // input | address test input
        logic [10:0] AY;    // output | write enable mux output
        logic [31:0] TD;    // input | test mode data inputs
        logic [31:0] DY;    // output | data mux output
        logic TCEN;         // input | chip enable test input, active low
        logic CENY;         // output | chip enable mux output?
        logic TWEN;         // input | write enable test inputs, active low
        logic WENY;         // output | write enable mux output?
        logic BEN;          // input | bypass mode enable, active low 0 = bypass operation and 1 = normal operation
        logic [31:0] TQ;    // wtf?
        // PIPELINE SUPPORT PINS
        logic TPEN;         // input | pipeline test mode enable
        logic PEN;          // input | pipeline enable, active low
        logic PENY;         // output | output of pipeline enable register for scan testing
        logic [31:0] QI;    // output | non-pipelined memory outputs
        //POWER DOWN MODE PINS
        logic RETN;         // input | retention mode enable, active low

    } sram_sp_reg_t;


endpackage: le_types
