/**
 * A 3-input Least Recently Used (LRU) Arbiter with Grant Accept.
 *
 * Grants access to the requesting module that was least recently used.
 * The LRU state is only updated when a grant is accepted by the server.
 *
 * - req: 3-bit request vector
 * - gnt_accept: 1-bit signal indicating the server has accepted the grant
 * - gnt: 3-bit one-hot grant vector
 */
module lru_arbiter_3 (
    input  logic        clk,
    input  logic        rst_n,

    // Requests from 3 modules
    input  logic [2:0]  req,

    // Server accepts the *current* grant
    input  logic        gnt_accept,

    // Grants to 3 modules (one-hot)
    output logic [2:0]  gnt
);

    // State registers to hold the permutation of use.
    // Each holds a client ID (0, 1, or 2).
    logic [1:0] mru_id; // Most Recently Used ID
    logic [1:0] mid_id; // Middle ID
    logic [1:0] lru_id; // Least Recently Used ID

    // --- Combinational Logic ---

    // Next-cycle values
    logic [2:0] gnt_next;
    logic [1:0] mru_id_next;
    logic [1:0] mid_id_next;
    logic [1:0] lru_id_next;

    // --- Part 1: Grant Logic (Calculates gnt_next) ---
    // Decides who to grant to based on requests and current state.
    always_comb begin
        gnt_next = 3'b000;

        // Check requests in LRU-to-MRU priority
        if (req[lru_id]) begin
            gnt_next[lru_id] = 1'b1;
        end else if (req[mid_id]) begin
            gnt_next[mid_id] = 1'b1;
        end else if (req[mru_id]) begin
            gnt_next[mru_id] = 1'b1;
        end
    end

    // --- Part 2: State Update Logic (Calculates ..._id_next) ---
    // Decides what the *next* state should be, based on the *current*
    // grant and whether it was accepted.
    always_comb begin
        // By default, state remains the same
        mru_id_next = mru_id;
        mid_id_next = mid_id;
        lru_id_next = lru_id;
        
        // Only update LRU state if a grant is active AND accepted
        if ((gnt != 3'b000) && gnt_accept) begin
            // Find out which ID is currently being granted
            logic [1:0] gnt_id_current;
            if (gnt[0])      gnt_id_current = 2'd0;
            else if (gnt[1]) gnt_id_current = 2'd1;
            else             gnt_id_current = 2'd2; // Assumes gnt is one-hot

            // A grant occurred, update the LRU order.
            // The granted client becomes the new MRU.
            if (gnt_id_current == lru_id) begin
                // LRU was granted: [mru, mid, lru] -> [lru, mru, mid]
                mru_id_next = lru_id;
                mid_id_next = mru_id;
                lru_id_next = mid_id;
            end else if (gnt_id_current == mid_id) begin
                // MID was granted: [mru, mid, lru] -> [mid, mru, lru]
                mru_id_next = mid_id;
                mid_id_next = mru_id;
                lru_id_next = lru_id; // lru_id remains the same
            end else begin // gnt_id_current == mru_id
                // MRU was granted: [mru, mid, lru] -> [mru, mid, lru]
                // No change to the order.
            end
        end
    end

    // --- Sequential Logic (Registers) ---

    always_ff @(posedge clk) begin
        if (!rst_n) begin
            // Asynchronous reset
            // Initialize to an arbitrary order: 0=MRU, 1=MID, 2=LRU
            mru_id <= 2'd0;
            mid_id <= 2'd1;
            lru_id <= 2'd2;
            gnt    <= 3'b000;
        end else begin
            // Update state and registered output
            mru_id <= mru_id_next;
            mid_id <= mid_id_next;
            lru_id <= lru_id_next;
            gnt    <= gnt_next;
        end
    end

endmodule