module trivium 
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

    output logic [63:0] byte_stream,
    // output logic test_out
    output logic done

);

    logic [STATE-1:0] internal_state, internal_state_next;
    logic [63:0] t1, t2, t3, gt1, gt2, gt3;
    logic [63:0] z;
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

        if (state == SETUP || state == DEBUG_SETUP) begin
            t1[0] = internal_state[65] ^ internal_state[90] & internal_state[91] ^ internal_state[92] ^ internal_state[170];
            t2[0] = internal_state[161] ^ internal_state[174] & internal_state[175] ^ internal_state[176] ^ internal_state[263];
            t3[0] = internal_state[242] ^ internal_state[285] & internal_state[286] ^ internal_state[287] ^ internal_state[68];

            internal_state_next[92:0] = {internal_state[91:0], t3[0]};
            internal_state_next[176:93] = {internal_state[175:93], t1[0]};
            internal_state_next[STATE-1:177] = {internal_state[286:177], t2[0]};
        end 
        else if (state == GEN || state == DEBUG_GEN) begin

            t1[0] = internal_state[65] ^ internal_state[92];
            t2[0] = internal_state[161] ^ internal_state[176];
            t3[0] = internal_state[242] ^ internal_state[287];

            t1[1] = internal_state[64] ^ internal_state[91];
            t2[1] = internal_state[160] ^ internal_state[175];
            t3[1] = internal_state[241] ^ internal_state[286];

            t1[2] = internal_state[63] ^ internal_state[90];
            t2[2] = internal_state[159] ^ internal_state[174];
            t3[2] = internal_state[240] ^ internal_state[285];

            t1[3] = internal_state[62] ^ internal_state[89];
            t2[3] = internal_state[158] ^ internal_state[173];
            t3[3] = internal_state[239] ^ internal_state[284];

            t1[4] = internal_state[61] ^ internal_state[88];
            t2[4] = internal_state[157] ^ internal_state[172];
            t3[4] = internal_state[238] ^ internal_state[283];

            t1[5] = internal_state[60] ^ internal_state[87];
            t2[5] = internal_state[156] ^ internal_state[171];
            t3[5] = internal_state[237] ^ internal_state[282];

            t1[6] = internal_state[59] ^ internal_state[86];
            t2[6] = internal_state[155] ^ internal_state[170];
            t3[6] = internal_state[236] ^ internal_state[281];

            t1[7] = internal_state[58] ^ internal_state[85];
            t2[7] = internal_state[154] ^ internal_state[169];
            t3[7] = internal_state[235] ^ internal_state[280];

            t1[8] = internal_state[57] ^ internal_state[84];
            t2[8] = internal_state[153] ^ internal_state[168];
            t3[8] = internal_state[234] ^ internal_state[279];

            t1[9] = internal_state[56] ^ internal_state[83];
            t2[9] = internal_state[152] ^ internal_state[167];
            t3[9] = internal_state[233] ^ internal_state[278];

            t1[10] = internal_state[55] ^ internal_state[82];
            t2[10] = internal_state[151] ^ internal_state[166];
            t3[10] = internal_state[232] ^ internal_state[277];

            t1[11] = internal_state[54] ^ internal_state[81];
            t2[11] = internal_state[150] ^ internal_state[165];
            t3[11] = internal_state[231] ^ internal_state[276];

            t1[12] = internal_state[53] ^ internal_state[80];
            t2[12] = internal_state[149] ^ internal_state[164];
            t3[12] = internal_state[230] ^ internal_state[275];

            t1[13] = internal_state[52] ^ internal_state[79];
            t2[13] = internal_state[148] ^ internal_state[163];
            t3[13] = internal_state[229] ^ internal_state[274];

            t1[14] = internal_state[51] ^ internal_state[78];
            t2[14] = internal_state[147] ^ internal_state[162];
            t3[14] = internal_state[228] ^ internal_state[273];

            t1[15] = internal_state[50] ^ internal_state[77];
            t2[15] = internal_state[146] ^ internal_state[161];
            t3[15] = internal_state[227] ^ internal_state[272];

            t1[16] = internal_state[49] ^ internal_state[76];
            t2[16] = internal_state[145] ^ internal_state[160];
            t3[16] = internal_state[226] ^ internal_state[271];

            t1[17] = internal_state[48] ^ internal_state[75];
            t2[17] = internal_state[144] ^ internal_state[159];
            t3[17] = internal_state[225] ^ internal_state[270];

            t1[18] = internal_state[47] ^ internal_state[74];
            t2[18] = internal_state[143] ^ internal_state[158];
            t3[18] = internal_state[224] ^ internal_state[269];

            t1[19] = internal_state[46] ^ internal_state[73];
            t2[19] = internal_state[142] ^ internal_state[157];
            t3[19] = internal_state[223] ^ internal_state[268];

            t1[20] = internal_state[45] ^ internal_state[72];
            t2[20] = internal_state[141] ^ internal_state[156];
            t3[20] = internal_state[222] ^ internal_state[267];

            t1[21] = internal_state[44] ^ internal_state[71];
            t2[21] = internal_state[140] ^ internal_state[155];
            t3[21] = internal_state[221] ^ internal_state[266];

            t1[22] = internal_state[43] ^ internal_state[70];
            t2[22] = internal_state[139] ^ internal_state[154];
            t3[22] = internal_state[220] ^ internal_state[265];

            t1[23] = internal_state[42] ^ internal_state[69];
            t2[23] = internal_state[138] ^ internal_state[153];
            t3[23] = internal_state[219] ^ internal_state[264];

            t1[24] = internal_state[41] ^ internal_state[68];
            t2[24] = internal_state[137] ^ internal_state[152];
            t3[24] = internal_state[218] ^ internal_state[263];

            t1[25] = internal_state[40] ^ internal_state[67];
            t2[25] = internal_state[136] ^ internal_state[151];
            t3[25] = internal_state[217] ^ internal_state[262];

            t1[26] = internal_state[39] ^ internal_state[66];
            t2[26] = internal_state[135] ^ internal_state[150];
            t3[26] = internal_state[216] ^ internal_state[261];

            t1[27] = internal_state[38] ^ internal_state[65];
            t2[27] = internal_state[134] ^ internal_state[149];
            t3[27] = internal_state[215] ^ internal_state[260];

            t1[28] = internal_state[37] ^ internal_state[64];
            t2[28] = internal_state[133] ^ internal_state[148];
            t3[28] = internal_state[214] ^ internal_state[259];

            t1[29] = internal_state[36] ^ internal_state[63];
            t2[29] = internal_state[132] ^ internal_state[147];
            t3[29] = internal_state[213] ^ internal_state[258];

            t1[30] = internal_state[35] ^ internal_state[62];
            t2[30] = internal_state[131] ^ internal_state[146];
            t3[30] = internal_state[212] ^ internal_state[257];

            t1[31] = internal_state[34] ^ internal_state[61];
            t2[31] = internal_state[130] ^ internal_state[145];
            t3[31] = internal_state[211] ^ internal_state[256];

            t1[32] = internal_state[33] ^ internal_state[60];
            t2[32] = internal_state[129] ^ internal_state[144];
            t3[32] = internal_state[210] ^ internal_state[255];

            t1[33] = internal_state[32] ^ internal_state[59];
            t2[33] = internal_state[128] ^ internal_state[143];
            t3[33] = internal_state[209] ^ internal_state[254];

            t1[34] = internal_state[31] ^ internal_state[58];
            t2[34] = internal_state[127] ^ internal_state[142];
            t3[34] = internal_state[208] ^ internal_state[253];

            t1[35] = internal_state[30] ^ internal_state[57];
            t2[35] = internal_state[126] ^ internal_state[141];
            t3[35] = internal_state[207] ^ internal_state[252];

            t1[36] = internal_state[29] ^ internal_state[56];
            t2[36] = internal_state[125] ^ internal_state[140];
            t3[36] = internal_state[206] ^ internal_state[251];

            t1[37] = internal_state[28] ^ internal_state[55];
            t2[37] = internal_state[124] ^ internal_state[139];
            t3[37] = internal_state[205] ^ internal_state[250];

            t1[38] = internal_state[27] ^ internal_state[54];
            t2[38] = internal_state[123] ^ internal_state[138];
            t3[38] = internal_state[204] ^ internal_state[249];

            t1[39] = internal_state[26] ^ internal_state[53];
            t2[39] = internal_state[122] ^ internal_state[137];
            t3[39] = internal_state[203] ^ internal_state[248];

            t1[40] = internal_state[25] ^ internal_state[52];
            t2[40] = internal_state[121] ^ internal_state[136];
            t3[40] = internal_state[202] ^ internal_state[247];

            t1[41] = internal_state[24] ^ internal_state[51];
            t2[41] = internal_state[120] ^ internal_state[135];
            t3[41] = internal_state[201] ^ internal_state[246];

            t1[42] = internal_state[23] ^ internal_state[50];
            t2[42] = internal_state[119] ^ internal_state[134];
            t3[42] = internal_state[200] ^ internal_state[245];

            t1[43] = internal_state[22] ^ internal_state[49];
            t2[43] = internal_state[118] ^ internal_state[133];
            t3[43] = internal_state[199] ^ internal_state[244];

            t1[44] = internal_state[21] ^ internal_state[48];
            t2[44] = internal_state[117] ^ internal_state[132];
            t3[44] = internal_state[198] ^ internal_state[243];

            t1[45] = internal_state[20] ^ internal_state[47];
            t2[45] = internal_state[116] ^ internal_state[131];
            t3[45] = internal_state[197] ^ internal_state[242];

            t1[46] = internal_state[19] ^ internal_state[46];
            t2[46] = internal_state[115] ^ internal_state[130];
            t3[46] = internal_state[196] ^ internal_state[241];

            t1[47] = internal_state[18] ^ internal_state[45];
            t2[47] = internal_state[114] ^ internal_state[129];
            t3[47] = internal_state[195] ^ internal_state[240];

            t1[48] = internal_state[17] ^ internal_state[44];
            t2[48] = internal_state[113] ^ internal_state[128];
            t3[48] = internal_state[194] ^ internal_state[239];

            t1[49] = internal_state[16] ^ internal_state[43];
            t2[49] = internal_state[112] ^ internal_state[127];
            t3[49] = internal_state[193] ^ internal_state[238];

            t1[50] = internal_state[15] ^ internal_state[42];
            t2[50] = internal_state[111] ^ internal_state[126];
            t3[50] = internal_state[192] ^ internal_state[237];

            t1[51] = internal_state[14] ^ internal_state[41];
            t2[51] = internal_state[110] ^ internal_state[125];
            t3[51] = internal_state[191] ^ internal_state[236];

            t1[52] = internal_state[13] ^ internal_state[40];
            t2[52] = internal_state[109] ^ internal_state[124];
            t3[52] = internal_state[190] ^ internal_state[235];

            t1[53] = internal_state[12] ^ internal_state[39];
            t2[53] = internal_state[108] ^ internal_state[123];
            t3[53] = internal_state[189] ^ internal_state[234];

            t1[54] = internal_state[11] ^ internal_state[38];
            t2[54] = internal_state[107] ^ internal_state[122];
            t3[54] = internal_state[188] ^ internal_state[233];

            t1[55] = internal_state[10] ^ internal_state[37];
            t2[55] = internal_state[106] ^ internal_state[121];
            t3[55] = internal_state[187] ^ internal_state[232];

            t1[56] = internal_state[9] ^ internal_state[36];
            t2[56] = internal_state[105] ^ internal_state[120];
            t3[56] = internal_state[186] ^ internal_state[231];

            t1[57] = internal_state[8] ^ internal_state[35];
            t2[57] = internal_state[104] ^ internal_state[119];
            t3[57] = internal_state[185] ^ internal_state[230];

            t1[58] = internal_state[7] ^ internal_state[34];
            t2[58] = internal_state[103] ^ internal_state[118];
            t3[58] = internal_state[184] ^ internal_state[229];

            t1[59] = internal_state[6] ^ internal_state[33];
            t2[59] = internal_state[102] ^ internal_state[117];
            t3[59] = internal_state[183] ^ internal_state[228];

            t1[60] = internal_state[5] ^ internal_state[32];
            t2[60] = internal_state[101] ^ internal_state[116];
            t3[60] = internal_state[182] ^ internal_state[227];

            t1[61] = internal_state[4] ^ internal_state[31];
            t2[61] = internal_state[100] ^ internal_state[115];
            t3[61] = internal_state[181] ^ internal_state[226];

            t1[62] = internal_state[3] ^ internal_state[30];
            t2[62] = internal_state[99] ^ internal_state[114];
            t3[62] = internal_state[180] ^ internal_state[225];

            t1[63] = internal_state[2] ^ internal_state[29];
            t2[63] = internal_state[98] ^ internal_state[113];
            t3[63] = internal_state[179] ^ internal_state[224];


            // testing parallelism
            z[63:0] = t1[63:0] ^ t2[63:0] ^ t3[63:0];

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

            gt1[8] = t1[8] ^ (internal_state[82] & internal_state[83]) ^ internal_state[162];
            gt2[8] = t2[8] ^ (internal_state[166] & internal_state[167]) ^ internal_state[255];
            gt3[8] = t3[8] ^ (internal_state[277] & internal_state[278]) ^ internal_state[60];

            gt1[9] = t1[9] ^ (internal_state[81] & internal_state[82]) ^ internal_state[161];
            gt2[9] = t2[9] ^ (internal_state[165] & internal_state[166]) ^ internal_state[254];
            gt3[9] = t3[9] ^ (internal_state[276] & internal_state[277]) ^ internal_state[59];

            gt1[10] = t1[10] ^ (internal_state[80] & internal_state[81]) ^ internal_state[160];
            gt2[10] = t2[10] ^ (internal_state[164] & internal_state[165]) ^ internal_state[253];
            gt3[10] = t3[10] ^ (internal_state[275] & internal_state[276]) ^ internal_state[58];

            gt1[11] = t1[11] ^ (internal_state[79] & internal_state[80]) ^ internal_state[159];
            gt2[11] = t2[11] ^ (internal_state[163] & internal_state[164]) ^ internal_state[252];
            gt3[11] = t3[11] ^ (internal_state[274] & internal_state[275]) ^ internal_state[57];

            gt1[12] = t1[12] ^ (internal_state[78] & internal_state[79]) ^ internal_state[158];
            gt2[12] = t2[12] ^ (internal_state[162] & internal_state[163]) ^ internal_state[251];
            gt3[12] = t3[12] ^ (internal_state[273] & internal_state[274]) ^ internal_state[56];

            gt1[13] = t1[13] ^ (internal_state[77] & internal_state[78]) ^ internal_state[157];
            gt2[13] = t2[13] ^ (internal_state[161] & internal_state[162]) ^ internal_state[250];
            gt3[13] = t3[13] ^ (internal_state[272] & internal_state[273]) ^ internal_state[55];

            gt1[14] = t1[14] ^ (internal_state[76] & internal_state[77]) ^ internal_state[156];
            gt2[14] = t2[14] ^ (internal_state[160] & internal_state[161]) ^ internal_state[249];
            gt3[14] = t3[14] ^ (internal_state[271] & internal_state[272]) ^ internal_state[54];

            gt1[15] = t1[15] ^ (internal_state[75] & internal_state[76]) ^ internal_state[155];
            gt2[15] = t2[15] ^ (internal_state[159] & internal_state[160]) ^ internal_state[248];
            gt3[15] = t3[15] ^ (internal_state[270] & internal_state[271]) ^ internal_state[53];

            gt1[16] = t1[16] ^ (internal_state[74] & internal_state[75]) ^ internal_state[154];
            gt2[16] = t2[16] ^ (internal_state[158] & internal_state[159]) ^ internal_state[247];
            gt3[16] = t3[16] ^ (internal_state[269] & internal_state[270]) ^ internal_state[52];

            gt1[17] = t1[17] ^ (internal_state[73] & internal_state[74]) ^ internal_state[153];
            gt2[17] = t2[17] ^ (internal_state[157] & internal_state[158]) ^ internal_state[246];
            gt3[17] = t3[17] ^ (internal_state[268] & internal_state[269]) ^ internal_state[51];

            gt1[18] = t1[18] ^ (internal_state[72] & internal_state[73]) ^ internal_state[152];
            gt2[18] = t2[18] ^ (internal_state[156] & internal_state[157]) ^ internal_state[245];
            gt3[18] = t3[18] ^ (internal_state[267] & internal_state[268]) ^ internal_state[50];

            gt1[19] = t1[19] ^ (internal_state[71] & internal_state[72]) ^ internal_state[151];
            gt2[19] = t2[19] ^ (internal_state[155] & internal_state[156]) ^ internal_state[244];
            gt3[19] = t3[19] ^ (internal_state[266] & internal_state[267]) ^ internal_state[49];

            gt1[20] = t1[20] ^ (internal_state[70] & internal_state[71]) ^ internal_state[150];
            gt2[20] = t2[20] ^ (internal_state[154] & internal_state[155]) ^ internal_state[243];
            gt3[20] = t3[20] ^ (internal_state[265] & internal_state[266]) ^ internal_state[48];

            gt1[21] = t1[21] ^ (internal_state[69] & internal_state[70]) ^ internal_state[149];
            gt2[21] = t2[21] ^ (internal_state[153] & internal_state[154]) ^ internal_state[242];
            gt3[21] = t3[21] ^ (internal_state[264] & internal_state[265]) ^ internal_state[47];

            gt1[22] = t1[22] ^ (internal_state[68] & internal_state[69]) ^ internal_state[148];
            gt2[22] = t2[22] ^ (internal_state[152] & internal_state[153]) ^ internal_state[241];
            gt3[22] = t3[22] ^ (internal_state[263] & internal_state[264]) ^ internal_state[46];

            gt1[23] = t1[23] ^ (internal_state[67] & internal_state[68]) ^ internal_state[147];
            gt2[23] = t2[23] ^ (internal_state[151] & internal_state[152]) ^ internal_state[240];
            gt3[23] = t3[23] ^ (internal_state[262] & internal_state[263]) ^ internal_state[45];

            gt1[24] = t1[24] ^ (internal_state[66] & internal_state[67]) ^ internal_state[146];
            gt2[24] = t2[24] ^ (internal_state[150] & internal_state[151]) ^ internal_state[239];
            gt3[24] = t3[24] ^ (internal_state[261] & internal_state[262]) ^ internal_state[44];

            gt1[25] = t1[25] ^ (internal_state[65] & internal_state[66]) ^ internal_state[145];
            gt2[25] = t2[25] ^ (internal_state[149] & internal_state[150]) ^ internal_state[238];
            gt3[25] = t3[25] ^ (internal_state[260] & internal_state[261]) ^ internal_state[43];

            gt1[26] = t1[26] ^ (internal_state[64] & internal_state[65]) ^ internal_state[144];
            gt2[26] = t2[26] ^ (internal_state[148] & internal_state[149]) ^ internal_state[237];
            gt3[26] = t3[26] ^ (internal_state[259] & internal_state[260]) ^ internal_state[42];

            gt1[27] = t1[27] ^ (internal_state[63] & internal_state[64]) ^ internal_state[143];
            gt2[27] = t2[27] ^ (internal_state[147] & internal_state[148]) ^ internal_state[236];
            gt3[27] = t3[27] ^ (internal_state[258] & internal_state[259]) ^ internal_state[41];

            gt1[28] = t1[28] ^ (internal_state[62] & internal_state[63]) ^ internal_state[142];
            gt2[28] = t2[28] ^ (internal_state[146] & internal_state[147]) ^ internal_state[235];
            gt3[28] = t3[28] ^ (internal_state[257] & internal_state[258]) ^ internal_state[40];

            gt1[29] = t1[29] ^ (internal_state[61] & internal_state[62]) ^ internal_state[141];
            gt2[29] = t2[29] ^ (internal_state[145] & internal_state[146]) ^ internal_state[234];
            gt3[29] = t3[29] ^ (internal_state[256] & internal_state[257]) ^ internal_state[39];

            gt1[30] = t1[30] ^ (internal_state[60] & internal_state[61]) ^ internal_state[140];
            gt2[30] = t2[30] ^ (internal_state[144] & internal_state[145]) ^ internal_state[233];
            gt3[30] = t3[30] ^ (internal_state[255] & internal_state[256]) ^ internal_state[38];

            gt1[31] = t1[31] ^ (internal_state[59] & internal_state[60]) ^ internal_state[139];
            gt2[31] = t2[31] ^ (internal_state[143] & internal_state[144]) ^ internal_state[232];
            gt3[31] = t3[31] ^ (internal_state[254] & internal_state[255]) ^ internal_state[37];

            gt1[32] = t1[32] ^ (internal_state[58] & internal_state[59]) ^ internal_state[138];
            gt2[32] = t2[32] ^ (internal_state[142] & internal_state[143]) ^ internal_state[231];
            gt3[32] = t3[32] ^ (internal_state[253] & internal_state[254]) ^ internal_state[36];

            gt1[33] = t1[33] ^ (internal_state[57] & internal_state[58]) ^ internal_state[137];
            gt2[33] = t2[33] ^ (internal_state[141] & internal_state[142]) ^ internal_state[230];
            gt3[33] = t3[33] ^ (internal_state[252] & internal_state[253]) ^ internal_state[35];

            gt1[34] = t1[34] ^ (internal_state[56] & internal_state[57]) ^ internal_state[136];
            gt2[34] = t2[34] ^ (internal_state[140] & internal_state[141]) ^ internal_state[229];
            gt3[34] = t3[34] ^ (internal_state[251] & internal_state[252]) ^ internal_state[34];

            gt1[35] = t1[35] ^ (internal_state[55] & internal_state[56]) ^ internal_state[135];
            gt2[35] = t2[35] ^ (internal_state[139] & internal_state[140]) ^ internal_state[228];
            gt3[35] = t3[35] ^ (internal_state[250] & internal_state[251]) ^ internal_state[33];

            gt1[36] = t1[36] ^ (internal_state[54] & internal_state[55]) ^ internal_state[134];
            gt2[36] = t2[36] ^ (internal_state[138] & internal_state[139]) ^ internal_state[227];
            gt3[36] = t3[36] ^ (internal_state[249] & internal_state[250]) ^ internal_state[32];

            gt1[37] = t1[37] ^ (internal_state[53] & internal_state[54]) ^ internal_state[133];
            gt2[37] = t2[37] ^ (internal_state[137] & internal_state[138]) ^ internal_state[226];
            gt3[37] = t3[37] ^ (internal_state[248] & internal_state[249]) ^ internal_state[31];

            gt1[38] = t1[38] ^ (internal_state[52] & internal_state[53]) ^ internal_state[132];
            gt2[38] = t2[38] ^ (internal_state[136] & internal_state[137]) ^ internal_state[225];
            gt3[38] = t3[38] ^ (internal_state[247] & internal_state[248]) ^ internal_state[30];

            gt1[39] = t1[39] ^ (internal_state[51] & internal_state[52]) ^ internal_state[131];
            gt2[39] = t2[39] ^ (internal_state[135] & internal_state[136]) ^ internal_state[224];
            gt3[39] = t3[39] ^ (internal_state[246] & internal_state[247]) ^ internal_state[29];

            gt1[40] = t1[40] ^ (internal_state[50] & internal_state[51]) ^ internal_state[130];
            gt2[40] = t2[40] ^ (internal_state[134] & internal_state[135]) ^ internal_state[223];
            gt3[40] = t3[40] ^ (internal_state[245] & internal_state[246]) ^ internal_state[28];

            gt1[41] = t1[41] ^ (internal_state[49] & internal_state[50]) ^ internal_state[129];
            gt2[41] = t2[41] ^ (internal_state[133] & internal_state[134]) ^ internal_state[222];
            gt3[41] = t3[41] ^ (internal_state[244] & internal_state[245]) ^ internal_state[27];

            gt1[42] = t1[42] ^ (internal_state[48] & internal_state[49]) ^ internal_state[128];
            gt2[42] = t2[42] ^ (internal_state[132] & internal_state[133]) ^ internal_state[221];
            gt3[42] = t3[42] ^ (internal_state[243] & internal_state[244]) ^ internal_state[26];

            gt1[43] = t1[43] ^ (internal_state[47] & internal_state[48]) ^ internal_state[127];
            gt2[43] = t2[43] ^ (internal_state[131] & internal_state[132]) ^ internal_state[220];
            gt3[43] = t3[43] ^ (internal_state[242] & internal_state[243]) ^ internal_state[25];

            gt1[44] = t1[44] ^ (internal_state[46] & internal_state[47]) ^ internal_state[126];
            gt2[44] = t2[44] ^ (internal_state[130] & internal_state[131]) ^ internal_state[219];
            gt3[44] = t3[44] ^ (internal_state[241] & internal_state[242]) ^ internal_state[24];

            gt1[45] = t1[45] ^ (internal_state[45] & internal_state[46]) ^ internal_state[125];
            gt2[45] = t2[45] ^ (internal_state[129] & internal_state[130]) ^ internal_state[218];
            gt3[45] = t3[45] ^ (internal_state[240] & internal_state[241]) ^ internal_state[23];

            gt1[46] = t1[46] ^ (internal_state[44] & internal_state[45]) ^ internal_state[124];
            gt2[46] = t2[46] ^ (internal_state[128] & internal_state[129]) ^ internal_state[217];
            gt3[46] = t3[46] ^ (internal_state[239] & internal_state[240]) ^ internal_state[22];

            gt1[47] = t1[47] ^ (internal_state[43] & internal_state[44]) ^ internal_state[123];
            gt2[47] = t2[47] ^ (internal_state[127] & internal_state[128]) ^ internal_state[216];
            gt3[47] = t3[47] ^ (internal_state[238] & internal_state[239]) ^ internal_state[21];

            gt1[48] = t1[48] ^ (internal_state[42] & internal_state[43]) ^ internal_state[122];
            gt2[48] = t2[48] ^ (internal_state[126] & internal_state[127]) ^ internal_state[215];
            gt3[48] = t3[48] ^ (internal_state[237] & internal_state[238]) ^ internal_state[20];

            gt1[49] = t1[49] ^ (internal_state[41] & internal_state[42]) ^ internal_state[121];
            gt2[49] = t2[49] ^ (internal_state[125] & internal_state[126]) ^ internal_state[214];
            gt3[49] = t3[49] ^ (internal_state[236] & internal_state[237]) ^ internal_state[19];

            gt1[50] = t1[50] ^ (internal_state[40] & internal_state[41]) ^ internal_state[120];
            gt2[50] = t2[50] ^ (internal_state[124] & internal_state[125]) ^ internal_state[213];
            gt3[50] = t3[50] ^ (internal_state[235] & internal_state[236]) ^ internal_state[18];

            gt1[51] = t1[51] ^ (internal_state[39] & internal_state[40]) ^ internal_state[119];
            gt2[51] = t2[51] ^ (internal_state[123] & internal_state[124]) ^ internal_state[212];
            gt3[51] = t3[51] ^ (internal_state[234] & internal_state[235]) ^ internal_state[17];

            gt1[52] = t1[52] ^ (internal_state[38] & internal_state[39]) ^ internal_state[118];
            gt2[52] = t2[52] ^ (internal_state[122] & internal_state[123]) ^ internal_state[211];
            gt3[52] = t3[52] ^ (internal_state[233] & internal_state[234]) ^ internal_state[16];

            gt1[53] = t1[53] ^ (internal_state[37] & internal_state[38]) ^ internal_state[117];
            gt2[53] = t2[53] ^ (internal_state[121] & internal_state[122]) ^ internal_state[210];
            gt3[53] = t3[53] ^ (internal_state[232] & internal_state[233]) ^ internal_state[15];

            gt1[54] = t1[54] ^ (internal_state[36] & internal_state[37]) ^ internal_state[116];
            gt2[54] = t2[54] ^ (internal_state[120] & internal_state[121]) ^ internal_state[209];
            gt3[54] = t3[54] ^ (internal_state[231] & internal_state[232]) ^ internal_state[14];

            gt1[55] = t1[55] ^ (internal_state[35] & internal_state[36]) ^ internal_state[115];
            gt2[55] = t2[55] ^ (internal_state[119] & internal_state[120]) ^ internal_state[208];
            gt3[55] = t3[55] ^ (internal_state[230] & internal_state[231]) ^ internal_state[13];

            gt1[56] = t1[56] ^ (internal_state[34] & internal_state[35]) ^ internal_state[114];
            gt2[56] = t2[56] ^ (internal_state[118] & internal_state[119]) ^ internal_state[207];
            gt3[56] = t3[56] ^ (internal_state[229] & internal_state[230]) ^ internal_state[12];

            gt1[57] = t1[57] ^ (internal_state[33] & internal_state[34]) ^ internal_state[113];
            gt2[57] = t2[57] ^ (internal_state[117] & internal_state[118]) ^ internal_state[206];
            gt3[57] = t3[57] ^ (internal_state[228] & internal_state[229]) ^ internal_state[11];

            gt1[58] = t1[58] ^ (internal_state[32] & internal_state[33]) ^ internal_state[112];
            gt2[58] = t2[58] ^ (internal_state[116] & internal_state[117]) ^ internal_state[205];
            gt3[58] = t3[58] ^ (internal_state[227] & internal_state[228]) ^ internal_state[10];

            gt1[59] = t1[59] ^ (internal_state[31] & internal_state[32]) ^ internal_state[111];
            gt2[59] = t2[59] ^ (internal_state[115] & internal_state[116]) ^ internal_state[204];
            gt3[59] = t3[59] ^ (internal_state[226] & internal_state[227]) ^ internal_state[9];

            gt1[60] = t1[60] ^ (internal_state[30] & internal_state[31]) ^ internal_state[110];
            gt2[60] = t2[60] ^ (internal_state[114] & internal_state[115]) ^ internal_state[203];
            gt3[60] = t3[60] ^ (internal_state[225] & internal_state[226]) ^ internal_state[8];

            gt1[61] = t1[61] ^ (internal_state[29] & internal_state[30]) ^ internal_state[109];
            gt2[61] = t2[61] ^ (internal_state[113] & internal_state[114]) ^ internal_state[202];
            gt3[61] = t3[61] ^ (internal_state[224] & internal_state[225]) ^ internal_state[7];

            gt1[62] = t1[62] ^ (internal_state[28] & internal_state[29]) ^ internal_state[108];
            gt2[62] = t2[62] ^ (internal_state[112] & internal_state[113]) ^ internal_state[201];
            gt3[62] = t3[62] ^ (internal_state[223] & internal_state[224]) ^ internal_state[6];

            gt1[63] = t1[63] ^ (internal_state[27] & internal_state[28]) ^ internal_state[107];
            gt2[63] = t2[63] ^ (internal_state[111] & internal_state[112]) ^ internal_state[200];
            gt3[63] = t3[63] ^ (internal_state[222] & internal_state[223]) ^ internal_state[5];

            internal_state_next[92:0] = {internal_state[28:0], gt3[0], gt3[1], gt3[2], gt3[3], gt3[4], gt3[5], gt3[6], gt3[7], gt3[8], gt3[9], gt3[10], gt3[11], gt3[12], gt3[13], gt3[14], gt3[15], gt3[16], gt3[17], gt3[18], gt3[19], gt3[20], gt3[21], gt3[22], gt3[23], gt3[24], gt3[25], gt3[26], gt3[27], gt3[28], gt3[29], gt3[30], gt3[31], gt3[32], gt3[33], gt3[34], gt3[35], gt3[36], gt3[37], gt3[38], gt3[39], gt3[40], gt3[41], gt3[42], gt3[43], gt3[44], gt3[45], gt3[46], gt3[47], gt3[48], gt3[49], gt3[50], gt3[51], gt3[52], gt3[53], gt3[54], gt3[55], gt3[56], gt3[57], gt3[58], gt3[59], gt3[60], gt3[61], gt3[62], gt3[63]};
            internal_state_next[176:93] = {internal_state[112:93], gt1[0], gt1[1], gt1[2], gt1[3], gt1[4], gt1[5], gt1[6], gt1[7], gt1[8], gt1[9], gt1[10], gt1[11], gt1[12], gt1[13], gt1[14], gt1[15], gt1[16], gt1[17], gt1[18], gt1[19], gt1[20], gt1[21], gt1[22], gt1[23], gt1[24], gt1[25], gt1[26], gt1[27], gt1[28], gt1[29], gt1[30], gt1[31], gt1[32], gt1[33], gt1[34], gt1[35], gt1[36], gt1[37], gt1[38], gt1[39], gt1[40], gt1[41], gt1[42], gt1[43], gt1[44], gt1[45], gt1[46], gt1[47], gt1[48], gt1[49], gt1[50], gt1[51], gt1[52], gt1[53], gt1[54], gt1[55], gt1[56], gt1[57], gt1[58], gt1[59], gt1[60], gt1[61], gt1[62], gt1[63]};
            internal_state_next[287:177] = {internal_state[223:177], gt2[0], gt2[1], gt2[2], gt2[3], gt2[4], gt2[5], gt2[6], gt2[7], gt2[8], gt2[9], gt2[10], gt2[11], gt2[12], gt2[13], gt2[14], gt2[15], gt2[16], gt2[17], gt2[18], gt2[19], gt2[20], gt2[21], gt2[22], gt2[23], gt2[24], gt2[25], gt2[26], gt2[27], gt2[28], gt2[29], gt2[30], gt2[31], gt2[32], gt2[33], gt2[34], gt2[35], gt2[36], gt2[37], gt2[38], gt2[39], gt2[40], gt2[41], gt2[42], gt2[43], gt2[44], gt2[45], gt2[46], gt2[47], gt2[48], gt2[49], gt2[50], gt2[51], gt2[52], gt2[53], gt2[54], gt2[55], gt2[56], gt2[57], gt2[58], gt2[59], gt2[60], gt2[61], gt2[62], gt2[63]};          
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
            end else if (state == GEN || state == DEBUG_GEN) begin
                byte_stream <= z;
                count <= count + 1'b1;
            end
        end
    end

endmodule