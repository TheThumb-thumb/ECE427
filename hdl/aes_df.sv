/*
Module: aes_df.sv

Purpose: 
    - AES based derivation function to spit out 256bit seed material using the aes_cbc_mac block.
        + seed_material = CBC_MAC_256(k_df_i, formatted_input)
        + formatted_input = entropy_i ^ nonce_i ^ personalization_i (256bit)

Handshake:
    - pulse start_i for 1 cycle
    - done_o pulses when seed_material_o is valid/stable


In Progress: SP 800-90A full implementation
*/


module aes_df #(parameter int DATA_WIDTH = 256)(
    // System Signals
    input  logic        clk,
    input  logic        rst_n,

    // Control Signals & Data
    input  logic                        start_i,                // start pulse
    input  logic [DATA_WIDTH-1:0]       entropy_i,              // entropy input 256b
    input  logic [DATA_WIDTH-1:0]       nonce_i,                // nonce input 256b
    input  logic [DATA_WIDTH-1:0]       personalization_i,      // personalization string 256b
    input  logic [127:0]                k_df_i,                 // 128b key for CBC_MAC

    output logic                        done_o,                 // high when seed is ready
    output logic [DATA_WIDTH-1:0]       seed_material_o         // 256b seed material
);

typedef enum logic [1:0] {S_IDLE, S_START, S_WAIT, S_DONE} state_t;
state_t state, state_n;

logic cbc_start;
logic cbc_done;
logic [DATA_WIDTH-1:0] msg_256;
logic [DATA_WIDTH-1:0] mac_256;

// combine inputs (could replace with 90A) ---> L || N || input || 0x80 || pad (instead for now use xor for compression)
// instead i directly uses k_df_i as the AES key (In SP 800-90A, the DF uses a fixed constant key like 0x00010203... for BCC, not an external key)

assign msg_256 = entropy_i ^ nonce_i ^ personalization_i;

// aes_cbc_mac instance (needs 256b message w/ 128b key)
aes_cbc_mac #(.DATA_WIDTH(DATA_WIDTH)) u_cbc (
    .clk (clk),
    .rst_n (rst_n),
    .start_i(cbc_start),
    .done_o(cbc_done),
    .key_i(k_df_i), // check this one *****************************
    .message_i(msg_256), 
    .mac_o(mac_256)
);

// seq: states/outputs
always_ff @(posedge clk)begin // n-edge rst? 
    if(!rst_n)begin
        state <= S_IDLE;
        seed_material_o <= '0;
        done_o <= 1'b0;
    end
    else begin
        state <= state_n;
        // pulse done on S_DONE
        done_o <= (state_n == S_DONE);
        if (cbc_done) begin
            seed_material_o <= mac_256;
            // could instead duplicate the final MAC: seed_material_o <= {mac_256[127:0], mac_256[127:0]};
        end
    end

end


// comb FSM
always_comb begin
    state_n = state;
    cbc_start = 1'b0;

    // states step through
    unique case(state)
        // waiting for start_i
        S_IDLE: begin
            if(start_i) state_n = S_START;
        end
        // issue start pulse to aes_cbc_mac
        S_START: begin
            cbc_start = 1'b1; // assert start for 1 cycle
            state_n = S_WAIT; // wait for CBC-MAC done
        end
        // wait for aes_cbc_mac done
        S_WAIT: begin
            if(cbc_done) state_n = S_DONE;
        end
        // latch result, pulse done
        S_DONE: begin
            state = S_IDLE; // return to bein idle
        end
    endcase
end

endmodule
