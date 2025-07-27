module trivium 
import params::*;
import le_types::*;
#(
    localparam STATE = 288;
)
(
    input logic clk,
    input logic rst,
    input logic [IV_WIDTH-1:0] iv_,
    input logic [IV_WIDTH-1:0] key_,

    input trivium_state_t state,

    output logic done,
    output logic [KEY_WIDTH-1:0] p,
    output logic [KEY_WIDTH-1:0] q

);

    logic [STATE-1:0] internal_state, internal_state_next;
    logic t1, t2, t3, key1, key2, gt1, gt2, gt3;
    logic [IV_WIDTH-1:0] 
    logic [10:0] count;

    always_comb begin
        // Key and IV setup:
        done = 1'b0;
        internal_state_next[KEY_WIDTH-1:0] = key_;
        internal_state_next[92:80] = '0;
        internal_state_next[173:93] = iv_;
        internal_state_next[176:174] = '0;
        internal_state_next[284:177] = '0;
        internal_state_next[STATE-1:285] = '1;
        t1 = 'x;
        t2 = 'x;
        t3 = 'x;
        gt1 = 'x;
        gt2 = 'x;
        gt3 = 'x;
        key1 = 'x;
        key2 = 'x;
        if (state == IDLE || IV_GEN) begin
            key1 = '0;
            key2 = '0;
        end
        else if (state == SETUP) begin
            t1 = internal_state[65] + internal_state[90] & internal_state[91] + internal_state[93] + internal_state[171];
            t2 = internal_state[161] + internal_state[175] & internal_state[176] + internal_state[177] + internal_state[264];
            t3 = internal_state[243] + internal_state[286] & internal_state[287] + internal_state[288] + internal_state[69];

            internal_state_next[92:0] = {t3, internal_state[91:0]};
            internal_state_next[176:93] = {t1, internal_state[175:93]};
            internal_state_next[STATE-1:177] = {t2, internal_state[286:177]};
        end 
        else if (state == GEN) begin

            t1 = internal_state[65] + internal_state[92];
            t2 = internal_state[161] + internal_state[176];
            t3 = internal_state[242] + internal_state[287];

            if (!key1) begin
                p[count] = t1 + t2 + t3;    
            end else begin
                q[count] = t1 + t2 + t3;
            end

            if (count == KEY_WIDTH && key1) begin
                key2 = 1'b1;
            end 
            else if (count == KEY_WIDTH) begin
                key1 = 1'b1
            end

            gt1 = t1 + internal_state[90] & internal_state[91] + internal_state[170];
            gt2 = t2 + internal_state[174] & internal_state[175] + internal_state[263];
            gt3 = t3 + internal_state[285] & internal_state[286] + internal_state[68];

            internal_state_next[92:0] = {gt3, internal_state[91:0]};
            internal_state_next[176:93] = {gt1, internal_state[175:93]};
            internal_state_next[STATE-1:177] = {gt2, internal_state[286:177]};
          
        end

        if (key1 && key2) begin
            done = 1'b1;
        end

    end

    always_ff @(posedge clk) begin  
        if (rst) begin
            internal_state <= '0;
            count <= '0;
        end else begin
            internal_state <= internal_state_next;
            count <= '0;
            if (state == GEN) begin
                count <= count + 1'b1;
                if (count == KEY_WIDTH) begin
                    count <= '0;
                end
            end
        end
    end

endmodule
