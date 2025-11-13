import le_types::*;
import params::*;
module oht_top_tb;

logic clk, rst;
int timeout;

initial clk = 1'b0;
always #1ns clk = ~clk;
initial rst = 1'b0;

    logic [es_sources-1:0] ES_in; // 0-31 latch 32-63 jitter
    logic deque;                  // tells us aes is reading? Does that matter?
    logic debug_mode;
    logic [15:0] spi_reg_lsb;

    logic [cond_width-1:0] cond_out;
    logic full;
    logic empty;
    logic [latch_sources-1:0][calib_bits-1:0] arr_n;
    logic [latch_sources-1:0][calib_bits-1:0] arr_p;
    logic [jitter_sources-1:0] j_disable_arr;
    logic [es_sources-1:0] rd_good_arr;

    logic [31:0] sram_read_addr;
    logic sram_read_valid;
    logic [31:0] sram_write_addr;
    logic sram_write_valid;
    logic [31:0] good_entropy_out;

    // operational tb now need to sweep all bias and then make sure good_entropy_flag outputs
    // have another teammate check my logic and sanity ;-;
    // check sram reads and write never occur at the same time, I think that means that initial address is always 32 ahead for write port and 32 behind for read port
    // ensure shifter actually works correctly
    // ensure fiao works properly for output


function automatic logic is_write_ahead_by_32(
    input logic [31:0] w,
    input logic [31:0] r,
    input int depth
);
    logic [31:0] diff;

    // Compute diff = (w - r) mod depth
    if (w >= r)
        diff = w - r;
    else
        diff = (depth - r) + w;

    return (diff >= 32);
endfunction

`define ASSERT(name, prop) \
    assert property (prop) else \
        $fatal("[%0t] ASSERTION FAILED: %s", $time, `"name`");

// 1. No simultaneous read and write valid at same address
property no_simultaneous_rw;
    @(posedge clk) disable iff (rst)
        !(sram_write_valid && sram_read_valid && (sram_write_addr == sram_read_addr));
endproperty
`ASSERT(no_simultaneous_rw, no_simultaneous_rw);

// 2. Check signals are never X or Z after reset
function automatic bit has_xz(input logic [1023:0] sig);
    return (^sig === 1'bx) || (^sig === 1'bz);
endfunction

// Using immediate assertions for non-scalar arrays:
always_ff @(posedge clk) begin
    if (!rst) begin
        if (has_xz(cond_out))
            $fatal("[%0t] cond_out has X or Z", $time);
        if (has_xz(full))
            $fatal("[%0t] full has X or Z", $time);
        if (has_xz(empty))
            $fatal("[%0t] empty has X or Z", $time);
        if (has_xz(j_disable_arr))
            $fatal("[%0t] j_disable_arr has X or Z", $time);
        if (has_xz(rd_good_arr))
            $fatal("[%0t] rd_good_arr has X or Z", $time);
        if (has_xz(good_entropy_out))
            $fatal("[%0t] good_entropy_out has X or Z", $time);
    end
end

// 3. full and empty should never both be 1
property full_empty_exclusive;
    @(posedge clk) disable iff (rst)
        !(full && empty);
endproperty
`ASSERT(full_empty_exclusive, full_empty_exclusive);

// 4. Optional: SRAM write should always lead read by at least 32
property write_ahead_of_read;
    @(posedge clk) disable iff (rst)
        (sram_write_valid && sram_read_valid)
            |-> is_write_ahead_by_32(sram_write_addr, sram_read_addr, 2048);
endproperty
`ASSERT(write_ahead_of_read, write_ahead_of_read)

// 5. Optional sanity: cond_out should be stable when full or empty asserted
// property cond_out_stable_when_full;
//     @(posedge clk) disable iff (rst)
//         (full) |=> $stable(cond_out);
// endproperty
// `ASSERT(cond_out_stable_when_full, cond_out_stable_when_full);



  always_ff @(posedge clk) begin

        // functionality of calibration is coming from mixed simulation
        // functionality of OHT_top, what to check:
        // make sure sram read and write never occur at the same time at the same address while valid is high!
        // ensure that cond_out is never X's, disable array is never X's, full/empty never X's
        // rd_good_arr and good_entropy out is never X's
        ES_in <= {$urandom, $urandom};
        deque <= $urandom;
        debug_mode <= 1'b1;
        spi_reg_lsb <= 12'hF0F;

    if (rst) begin
        debug_mode <= '0;
        // deque <= '0;
        spi_reg_lsb <= '0;

    end else begin
        // if (full) begin
        //     deque <= '1;
        // end else begin
        //     deque <= '0;
        // end

    end

    end

    oht_top_test dut (
        .clk(clk),
        .rst(rst),

        .ES_in(ES_in),
        .deque(deque),
        .debug_mode(debug_mode),
        .spi_reg_lsb(spi_reg_lsb),

        .cond_out(cond_out),
        .full(full),
        .empty(empty),
        .arr_n(arr_n),
        .arr_p(arr_p),
        .j_disable_arr(j_disable_arr),
        .rd_good_arr(rd_good_arr),
        .good_entropy_out(good_entropy_out),

        .sram_write_addr(sram_write_addr),
        .sram_write_valid(sram_write_valid),
        .sram_read_addr(sram_read_addr),
        .sram_read_valid(sram_read_valid)
        
    );

    initial begin
		$fsdbDumpfile("oht_top_dump.fsdb");
		$fsdbDumpvars(0, "+all");
		rst = 1'b1;
        #10ns
		rst = 1'b0;
        #10000ns
        rst = 1'b1;
        #10ns
        rst = 1'b0;
        #10000000;
        $finish();

	end

endmodule

