module sha1 (
    input  logic         clk,
    input  logic         reset_n,
    input  logic         start,
    input  logic [511:0] block,      // Input block (512 bits)
    output logic [159:0] hash_out,    // Output hash
    output logic         done
);

    // Fixed constants 
    localparam [31:0] H0_INIT = 32'h67452301;
    localparam [31:0] H1_INIT = 32'hEFCDAB89;
    localparam [31:0] H2_INIT = 32'h98BADCFE;
    localparam [31:0] H3_INIT = 32'h10325476;
    localparam [31:0] H4_INIT = 32'hC3D2E1F0;

    // 80 rounds 4 phases for 20 rounds each
    localparam [31:0] K0 = 32'h5A827999;
    localparam [31:0] K1 = 32'h6ED9EBA1;
    localparam [31:0] K2 = 32'h8F1BBCDC;
    localparam [31:0] K3 = 32'hCA62C1D6;

    // State
    typedef enum logic [1:0] {
        IDLE, LOAD, COMPRESS, DONE
    } state_t;

    state_t state, next_state;
    logic [6:0] t;

    logic [31:0] W[0:79];
    logic [31:0] a, b, c, d, e;
    logic [31:0] h0, h1, h2, h3, h4;

    logic [31:0] f, k, temp;

    // FSM
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) state <= IDLE;
        else          state <= next_state;
    end

    always_comb begin
        case (state)
            IDLE:      next_state = start ? LOAD : IDLE;
            LOAD:      next_state = COMPRESS;
            COMPRESS:  next_state = (t == 79) ? DONE : COMPRESS;
            DONE:      next_state = IDLE;
            default:   next_state = IDLE;
        endcase
    end

    // W[t] with initialization & compression
    always_ff @(posedge clk) begin
        if (state == LOAD) begin
            for (int i = 0; i < 16; i++) begin
                W[i] <= block[511 - 32*i -: 32];
            end
            for (int i = 16; i < 80; i++) begin
                W[i] <= {W[i-3] ^ W[i-8] ^ W[i-14] ^ W[i-16], 1'b0} <<< 1;
            end
        end
    end

    // Main Compression 
    always_ff @(posedge clk) begin
        if (state == LOAD) begin
            h0 <= H0_INIT; h1 <= H1_INIT; h2 <= H2_INIT; h3 <= H3_INIT; h4 <= H4_INIT;
            a <= H0_INIT; b <= H1_INIT; c <= H2_INIT; d <= H3_INIT; e <= H4_INIT;
            t <= 0;
        end
        else if (state == COMPRESS) begin
            // Select funct & const
            if (t < 20) begin 
                f = (b & c) | ((~b) & d);
                k = K0;
            end 
            else if (t < 40) begin
                f = b ^ c ^ d;
                k = K1;
                // this part is wrong -----------------------------------------------------------------------------------
            end 
            else if (t < 60) begin
                f = (b & c) | (b & d) | (c & d);
                k = K2;
            end 
            else begin
                f = b ^ c ^ d;
                k = K3;
            end

            temp = ({a[26:0], a[31:27]} + f + e + k + W[t]);
            e <= d;
            d <= c;
            c <= {b[1:0], b[31:2]}; // b <<< 30
            b <= a;
            a <= temp;

            t <= t + 1;
        end
        else if (state == DONE) begin
            h0 <= h0 + a;
            h1 <= h1 + b;
            h2 <= h2 + c;
            h3 <= h3 + d;
            h4 <= h4 + e;
        end
    end

    // Output
    assign digest = {h0, h1, h2, h3, h4};
    assign hash_out   = (state == DONE);

endmodule
