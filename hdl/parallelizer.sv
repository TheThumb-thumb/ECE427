module parallelizer (
    // System Inputs
    input  logic clk,
    input  logic rst_n,

    // Data Inputs
    input  logic serial_in,
    input  logic debug,
    input  logic [1:0] sel, // 2'b00 (Conditioner) or 2'b10(DRBG) for 384; 2'b01(Trivium) for 160

    // Data Outputs
    output logic [383:0] parallel_out,
    output logic data_valid_out
);

    // State-holding registers are essential for this operation
    logic [383:0] shift_reg;
    logic [8:0]   bit_count;
    logic [8:0]   latched_target_count;

    // Determine the target packet size from 'sel'
    wire [8:0] target_count = (sel == 2'b01) ? 160 : 384;

    // Sequential logic block for state transitions
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            // Asynchronous active-low reset
            shift_reg            <= '0;
            bit_count            <= '0;
            data_valid_out       <= 1'b0;
            latched_target_count <= 384;
        end else begin
            // Default assignment ensures data_valid_out is a single-cycle pulse
            data_valid_out <= 1'b0;

            if (debug) begin
                // Shift in the new serial bit
                shift_reg <= {shift_reg[382:0], serial_in};

                // Latch the packet size at the beginning of reception
                if (bit_count == 0) begin
                    latched_target_count <= target_count;
                end

                // Check if the packet is complete
                if (bit_count == latched_target_count - 1) begin
                    bit_count      <= '0;       // Reset counter for the next packet
                    data_valid_out <= 1'b1;      // Signal that parallel data is ready
                end else begin
                    bit_count <= bit_count + 1;  // Increment bit counter
                end
            end
        end
    end

    // Continuously assign the register's content to the output
    assign parallel_out = shift_reg;

endmodule