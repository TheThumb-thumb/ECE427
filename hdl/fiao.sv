module que_fiao #(
    parameter ENQ_WIDTH = 32,
    parameter CHUNKS = 12,
    parameter OUT_WIDTH = ENQ_WIDTH * CHUNKS
)(
    input  logic clk,
    input  logic rst,

    input  logic [ENQ_WIDTH-1:0] wdata,
    output logic [OUT_WIDTH-1:0] rdata,

    input  logic enque,
    input  logic deque,

    output logic full,
    output logic empty
);

    // Internal registers
    logic [OUT_WIDTH-1:0] buffer_reg, buffer_next;
    logic [$clog2(CHUNKS+1)-1:0] counter_reg, counter_next;

    // Sequential logic
    always_ff @(posedge clk) begin
        if (rst) begin
            buffer_reg  <= '0;
            counter_reg <= '0;
        end else begin
            buffer_reg  <= buffer_next;
            counter_reg <= counter_next;
        end
    end

    // Combinational logic
    always_comb begin

        if (rst) begin

            full = 1'b0;
            empty = 1'b1;

        end

        buffer_next  = buffer_reg;
        counter_next = counter_reg;
        rdata        = '0;

        full  = (counter_reg == CHUNKS);
        empty = (counter_reg == 0);

        if (enque && !full) begin
            // Shift existing data and insert new chunk at LSB side
            buffer_next = {buffer_reg[OUT_WIDTH-ENQ_WIDTH-1:0], wdata};
            counter_next = counter_reg + 1'b1;
        end

        if (deque && full) begin
            // Output all data when full
            rdata = buffer_reg;
            // Reset for next batch
            counter_next = '0;
            buffer_next  = '0;
        end
    end

endmodule : que_fiao
