module clkmux (
    input  logic rst_n,
    input  logic A,     // clock A
    input  logic B,     // clock B
    input  logic S0,    // select: 1 → choose A, 0 → choose B
    output logic Y
);

    // ------------------------------------------------------------
    // Two-FF synchronizers (one in each clock domain)
    // ------------------------------------------------------------
    logic selA_ff1, selA_ff2;   // S0 synced into clock A domain
    logic selB_ff1, selB_ff2;   // S0 synced into clock B domain

    // Sync S0 into A domain
    always_ff @(posedge A) begin
        if(!rst_n) begin
            selA_ff1 <= '0;
            selA_ff2 <= '0;
        end else begin
            selA_ff1 <= S0;
            selA_ff2 <= selA_ff1;
        end
    end

    // Sync S0 into B domain
    always_ff @(posedge B) begin
        if(!rst_n) begin
            selB_ff1 <= '0;
            selB_ff2 <= '0;
        end else begin 
            selB_ff1 <= S0;
            selB_ff2 <= selB_ff1;
        end
    end

    // ------------------------------------------------------------
    // Clock gating
    // ------------------------------------------------------------
    logic A_gated;
    logic B_gated;

    assign A_gated = A & selA_ff2;      // enable A when S0=1 (synced to A)
    assign B_gated = B & ~selB_ff2;     // enable B when S0=0 (synced to B)

    // Final OR
    assign Y = A_gated | B_gated;

endmodule