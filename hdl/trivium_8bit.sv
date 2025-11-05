module trivium_8bit
import params::*;
import le_types::*;
#(
    localparam STATE = 288
)
(
    input logic clk,
    input logic rst,
    input logic [IV_WIDTH-1:0] iv_,
    input logic [IV_WIDTH-1:0] key_,
    input logic stall,

    input trivium_state_t state,

    output logic [7:0] byte_stream,
    // output logic test_out
    output logic done

);

    logic [STATE-1:0] internal_state, internal_state_next;
    logic [7:0] t1, t2, t3, gt1, gt2, gt3;
    logic [7:0] z;
    logic [10:0] count;

    // assign done = (count == 2047) ? 1'b1 : 1'b0;
    assign done = '0;
    always_comb begin
        // Key and IV setup:
        // done = 1'b0;
        internal_state_next[IV_WIDTH-1:0] = key_;
        internal_state_next[92:80] = '0;
        internal_state_next[173:93] = iv_;
        internal_state_next[176:174] = '0;
        internal_state_next[284:177] = '0;
        internal_state_next[STATE-1:285] = '1;
        t1 = '0;
        t2 = '0;
        t3 = '0;
        gt1 = '0;
        gt2 = '0;
        gt3 = '0;
        z = '0;

        if (state == SETUP) begin
            t1[0] = internal_state[65] ^ internal_state[90] & internal_state[91] ^ internal_state[92] ^ internal_state[170];
            t2[0] = internal_state[161] ^ internal_state[174] & internal_state[175] ^ internal_state[176] ^ internal_state[263];
            t3[0] = internal_state[242] ^ internal_state[285] & internal_state[286] ^ internal_state[287] ^ internal_state[68];

            internal_state_next[92:0] = {internal_state[91:0], t3[0]};
            internal_state_next[176:93] = {internal_state[175:93], t1[0]};
            internal_state_next[STATE-1:177] = {internal_state[286:177], t2[0]};
        end 
        else if (state == GEN) begin

            t1[0] = internal_state[65] ^ internal_state[92];
            t2[0] = internal_state[161] ^ internal_state[176];
            t3[0] = internal_state[242] ^ internal_state[287];

            t1[1] = internal_state[64] ^ internal_state[93];
            t2[1] = internal_state[160] ^ internal_state[177];
            t3[1] = internal_state[241] ^ internal_state[0];

            t1[2] = internal_state[63] ^ internal_state[94];
            t2[2] = internal_state[159] ^ internal_state[178];
            t3[2] = internal_state[240] ^ internal_state[1];

            t1[3] = internal_state[62] ^ internal_state[95];
            t2[3] = internal_state[158] ^ internal_state[179];
            t3[3] = internal_state[239] ^ internal_state[2];

            t1[4] = internal_state[61] ^ internal_state[96];
            t2[4] = internal_state[157] ^ internal_state[180];
            t3[4] = internal_state[238] ^ internal_state[3];

            t1[5] = internal_state[60] ^ internal_state[97];
            t2[5] = internal_state[156] ^ internal_state[181];
            t3[5] = internal_state[237] ^ internal_state[4];

            t1[6] = internal_state[59] ^ internal_state[98];
            t2[6] = internal_state[155] ^ internal_state[182];
            t3[6] = internal_state[236] ^ internal_state[5];

            t1[7] = internal_state[58] ^ internal_state[99];
            t2[7] = internal_state[154] ^ internal_state[183];
            t3[7] = internal_state[235] ^ internal_state[6];

            // testing parallelism
            z[7:0] = t1[7:0] ^ t2[7:0] ^ t3[7:0];

            gt1[0] = t1[0] ^ (internal_state[90] & internal_state[91]) ^ internal_state[170];
            gt2[0] = t2[0] ^ (internal_state[174] & internal_state[175]) ^ internal_state[263];
            gt3[0] = t3[0] ^ (internal_state[285] & internal_state[286]) ^ internal_state[68];

            gt1[1] = t1[1] ^ (internal_state[89] & internal_state[90]) ^ internal_state[169];
            gt2[1] = t2[1] ^ (internal_state[173] & internal_state[174]) ^ internal_state[262];
            gt3[1] = t3[1] ^ (internal_state[284] & internal_state[285]) ^ internal_state[67];

            gt1[2] = t1[2] ^ (internal_state[88] & internal_state[89]) ^ internal_state[168];
            gt2[2] = t2[2] ^ (internal_state[172] & internal_state[173]) ^ internal_state[261];
            gt3[2] = t3[2] ^ (internal_state[283] & internal_state[284]) ^ internal_state[66];

            gt1[3] = t1[3] ^ (internal_state[87] & internal_state[88]) ^ internal_state[167];
            gt2[3] = t2[3] ^ (internal_state[171] & internal_state[172]) ^ internal_state[260];
            gt3[3] = t3[3] ^ (internal_state[282] & internal_state[283]) ^ internal_state[65];

            gt1[4] = t1[4] ^ (internal_state[86] & internal_state[87]) ^ internal_state[166];
            gt2[4] = t2[4] ^ (internal_state[170] & internal_state[171]) ^ internal_state[259];
            gt3[4] = t3[4] ^ (internal_state[281] & internal_state[282]) ^ internal_state[64];

            gt1[5] = t1[5] ^ (internal_state[85] & internal_state[86]) ^ internal_state[165];
            gt2[5] = t2[5] ^ (internal_state[169] & internal_state[170]) ^ internal_state[258];
            gt3[5] = t3[5] ^ (internal_state[280] & internal_state[281]) ^ internal_state[63];

            gt1[6] = t1[6] ^ (internal_state[84] & internal_state[85]) ^ internal_state[164];
            gt2[6] = t2[6] ^ (internal_state[168] & internal_state[169]) ^ internal_state[257];
            gt3[6] = t3[6] ^ (internal_state[279] & internal_state[280]) ^ internal_state[62];

            gt1[7] = t1[7] ^ (internal_state[83] & internal_state[84]) ^ internal_state[163];
            gt2[7] = t2[7] ^ (internal_state[167] & internal_state[168]) ^ internal_state[256];
            gt3[7] = t3[7] ^ (internal_state[278] & internal_state[279]) ^ internal_state[61];

            internal_state_next[92:0] = {internal_state[84:0], gt3[0], gt3[1], gt3[2], gt3[3], gt3[4], gt3[5], gt3[6], gt3[7]};
            internal_state_next[176:93] = {internal_state[168:93], gt1[0], gt1[1], gt1[2], gt1[3], gt1[4], gt1[5], gt1[6], gt1[7]};
            internal_state_next[STATE-1:177] = {internal_state[279:177],  gt2[0], gt2[1], gt2[2], gt2[3], gt2[4], gt2[5], gt2[6], gt2[7]};
          
        end

    end

    always_ff @(posedge clk) begin  
        if (rst) begin
            internal_state <= '0;
            count <= '0;
            byte_stream <= '0;
        end else begin
            internal_state <= internal_state_next;
            count <= '0;
            byte_stream <= '0;
            if (stall) begin
                internal_state <= internal_state;
                byte_stream <= '0;
                count <= count;
            end else if (state == GEN) begin
                byte_stream <= z;
                count <= count + 1'b1;
            end
        end
    end

endmodule