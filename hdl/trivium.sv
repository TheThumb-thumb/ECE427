// module trivium 
// import params::*;
// import le_types::*;
// #(
//     localparam STATE = 288;
// )
// (
//     input logic clk,
//     input logic rst,
//     input logic [IV_WIDTH-1:0] iv_,
//     input logic [IV_WIDTH-1:0] key_,

//     input trivium_state_t state,

//     output logic [7:0] byte_stream,
//     output logic done

// );

//     logic [STATE-1:0] internal_state, internal_state_next;
//     logic [7:0] t1, t2, t3, gt1, gt2, gt3;
//     logic [IV_WIDTH-1:0] 
//     logic [10:0] count;

//     always_comb begin
//         // Key and IV setup:
//         done = 1'b0;
//         internal_state_next[KEY_WIDTH-1:0] = key_;
//         internal_state_next[92:80] = '0;
//         internal_state_next[173:93] = iv_;
//         internal_state_next[176:174] = '0;
//         internal_state_next[284:177] = '0;
//         internal_state_next[STATE-1:285] = '1;
//         t1 = 'x;
//         t2 = 'x;
//         t3 = 'x;
//         gt1 = 'x;
//         gt2 = 'x;
//         gt3 = 'x;

//         if (state == SETUP) begin
//             t1 = internal_state[65] + internal_state[90] & internal_state[91] + internal_state[93] + internal_state[171];
//             t2 = internal_state[161] + internal_state[175] & internal_state[176] + internal_state[177] + internal_state[264];
//             t3 = internal_state[243] + internal_state[286] & internal_state[287] + internal_state[288] + internal_state[69];

//             internal_state_next[92:0] = {t3, internal_state[91:0]};
//             internal_state_next[176:93] = {t1, internal_state[175:93]};
//             internal_state_next[STATE-1:177] = {t2, internal_state[286:177]};
//         end 
//         else if (state == GEN) begin

//             t1 = internal_state[65] + internal_state[92];
//             t2 = internal_state[161] + internal_state[176];
//             t3 = internal_state[242] + internal_state[287];

//             // testing parallelism


//             // if (!key1) begin
//             //     p[count] = t1 + t2 + t3;    
//             // end else begin
//             //     q[count] = t1 + t2 + t3;
//             // end

//             gt1 = t1 + internal_state[90] & internal_state[91] + internal_state[170];
//             gt2 = t2 + internal_state[174] & internal_state[175] + internal_state[263];
//             gt3 = t3 + internal_state[285] & internal_state[286] + internal_state[68];

//             internal_state_next[92:0] = {gt3, internal_state[91:0]};
//             internal_state_next[176:93] = {gt1, internal_state[175:93]};
//             internal_state_next[STATE-1:177] = {gt2, internal_state[286:177]};
          
//         end

//     end

//     always_ff @(posedge clk) begin  
//         if (rst) begin
//             internal_state <= '0;
//             count <= '0;
//         end else begin
//             internal_state <= internal_state_next;
//             count <= '0;
//             if (state == GEN) begin
//                 count <= count + 1'b1;
//             end
//         end
//     end

// endmodule

module trivium 
import params::*;
import le_types::*;
#(
    localparam STATE = 288
)
(
    input  logic clk,
    input  logic rst,
    input  logic [IV_WIDTH-1:0] iv_,
    input  logic [IV_WIDTH-1:0] key_,

    input  trivium_state_t state,

    output logic [7:0] byte_stream,
    output logic done
);

    // Internal registers
    logic [STATE-1:0] internal_state, internal_state_next;
    logic [10:0] count;
    logic [7:0] z; // 8 keystream bits

    // Temporary unrolled states
    logic [STATE-1:0] s [0:8];
    logic t1, t2, t3;
    integer i;

    assign done = (count == '1) ? 1'b1 : 1'b0;

    always_comb begin
        internal_state_next = internal_state;

        // ========== Initialization ==========
        if (state == SETUP) begin
            internal_state_next = '0;
            internal_state_next[IV_WIDTH-1:0] = key_;
            internal_state_next[173:93] = iv_;
            internal_state_next[STATE-1:285] = 3'b111;
        end

        // ========== Keystream Generation ==========
        else if (state == GEN) begin
            // Initialize stage 0
            s[0] = internal_state;

            // Unroll 8 rounds combinationally
            for (i = 0; i < 8; i++) begin
                t1 = s[i][65]  ^ (s[i][90]  & s[i][91]) ^ s[i][92]  ^ s[i][170];
                t2 = s[i][161] ^ (s[i][174] & s[i][175]) ^ s[i][176] ^ s[i][263];
                t3 = s[i][242] ^ (s[i][285] & s[i][286]) ^ s[i][287] ^ s[i][68];

                z[i] = t1 ^ t2 ^ t3;

                // Advance state
                s[i+1] = {
                    t3, s[i][92:1],        // A-register
                    t1, s[i][176:94],      // B-register
                    t2, s[i][287:177]      // C-register
                };
            end

            // Update internal state
            internal_state_next = s[8];
        end
    end

    // ========== Sequential Update ==========
    always_ff @(posedge clk) begin
        if (rst) begin
            internal_state <= '0;
            count <= '0;
            byte_stream <= '0;
        end else begin
            internal_state <= internal_state_next;
            if (state == GEN) begin
                byte_stream <= z;
                count <= count + 1'b1;
            end else begin
                byte_stream <= '0;
            end
        end
    end

endmodule
