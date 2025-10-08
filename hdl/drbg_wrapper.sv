module ctr_drbg_wrapper #(
    parameter int KEY_BITS        = 128,  // AES
    parameter int DATA_WIDTH      = 256,  // Seed width from conditioner
    parameter int RESEED_INTERVAL = 511   // simple reseed guard (count of generate calls)

)(
    input  logic                      clk,
    input  logic                      rst_n,

    // Handshake to/from conditioner
    output logic                   drbg_ready_o, // -> conditioner.drbg_ready_i
    input  logic                   drbg_valid_i, // <- conditioner.drbg_valid_o
    input  logic [DATA_WIDTH-1:0]  seed_i,       // <- conditioner.seed_o (256-bit)

    // DRBG signals from control
    input  logic                   instantiate_i, // 1-cycle (IDLE only)
    input  logic                   reseed_i,      // 1-cycle (IDLE only)
    input  logic                   generate_i,    // 1-cycle (IDLE only)
    input  logic [15:0]            num_blocks_i,  // # of 128b encrypt blocks to output

    // DRBG status & data outputs
    output logic                   busy_o,         // high when DRBG not idle
    output logic                   buffer_ready,         //when op completes
    output logic                   random_valid_o,      //  per 128b block
    output logic [KEY_BITS-1:0]    random_block_o       // capture on random_valid_o
    
);

// seed handoff to DRBG:
logic [DATA_WIDTH-1:0] seed_latched;
logic seed_valid_pulse;
logic core_done;

// FSM: request seed, capture seed, chuck @ DRBG
typedef enum logic [1:0] {W_IDLE, W_WAIT_SEED, W_PULSE_DRBG} wstate_t;
wstate_t wstate, wstate_n;

// Seq Logic
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        wstate           <= W_IDLE;
        seed_latched     <= '0;
        seed_valid_pulse <= 1'b0;
    end else begin
        wstate           <= wstate_n;
        // goes into DRBG
        seed_valid_pulse <= (wstate_n == W_PULSE_DRBG);

        // Latch the 256b seed exactly when conditioner asserts valid
        if (drbg_valid_i && (wstate == W_WAIT_SEED)) begin
            seed_latched <= seed_i;
        end
    end
end

// Comb Logic
always_comb begin
    wstate_n      = wstate;
    drbg_ready_o  = 1'b0;

    unique case (wstate)
        W_IDLE: begin
            // @ instan or reseed request, ask conditioner for a seed
            if (instantiate_i || reseed_i) begin
                drbg_ready_o = 1'b1;
                wstate_n     = W_WAIT_SEED;
            end
        end

        W_WAIT_SEED: begin
            // stays ready asserted until conditioner sends valid
            drbg_ready_o = 1'b1;
            if (drbg_valid_i) begin
                wstate_n = W_PULSE_DRBG;  // next cycle: strobe seed into DRBG core
            end
        end

        W_PULSE_DRBG: begin
            // seed_valid is generated, return to idle
            wstate_n = W_IDLE;
        end

        default: wstate_n = W_IDLE;
    endcase
end


// drbg core
aes_ctr_drbg #(
    .KEY_BITS        (KEY_BITS),
    .BLOCK_BITS      (128),
    .SEED_BITS       (DATA_WIDTH),
    .RESEED_INTERVAL (RESEED_INTERVAL)
) u_drbg (
    .clk               (clk),
    .rst_n             (rst_n),

    // command pulses & size
    .instantiate_i     (instantiate_i),
    .reseed_i          (reseed_i),
    .generate_i        (generate_i),
    .num_blocks_i      (num_blocks_i),

    // seed from wrapper (latched + 1-cycle strobe)
    .seed_material_i   (seed_latched),
    .seed_valid_i      (seed_valid_pulse),

    // optional additional input (post-generate update)
    .additional_input_i('0),

    // status & data
    .busy_o            (busy_o),
    .done_o            (core_done),
    .random_valid_o    (random_valid_o),
    .random_block_o    (random_block_o)
);

assign buffer_ready = core_done;

endmodule