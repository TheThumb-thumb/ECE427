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

endpackage
