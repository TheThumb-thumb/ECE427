module oht_top
import le_types::*;
import params::*;
(
    input logic clk,
    input logic rst,

    input logic [es_sources-1:0] ES_in, // 0-31 latch 32-63 jitter
    input logic deque,                  // tells us aes is reading? Does that matter?
    input logic debug_mode,
    input logic [15:0] spi_reg_lsb,

    output logic [cond_width-1:0] cond_out,
    output logic full,
    output logic empty,

    output logic [latch_sources-1:0][calib_bits-1:0] arr_n, 
    output logic [latch_sources-1:0][calib_bits-1:0] arr_p,
    output logic [jitter_sources-1:0] j_disable_arr,
    output logic [es_sources-1:0] rd_good_arr

);

logic [es_sources-1:0] fail_arr;
logic [es_sources-1:0] valid_arr;
logic [latch_sources-1:0] es_out_latch;
logic [jitter_sources-1:0] es_out_jitter;
// logic [es_sources-1:0] rd_good_arr;
logic [latch_sources-1:0] mask_in;

// disregard A outputs unless debug needs them?
logic CENYA, WENYA, PENYA;
logic [$clog2(sram_addr)-1:0] AYA;
logic [sram_word-1:0] DYA, QIA, QA;

// outputs of port B only regard when flag is high
logic CENYB, WENYB, PENYB;
logic [$clog2(sram_addr)-1:0] AYB;
logic [sram_word-1:0] DYB, QIB, QB;

// these are test input vectors I believe, will useful once debug is implemented for this but for now it is set to 0
logic [$clog2(sram_addr)-1:0] TAA, TAB;
logic [sram_word-1:0] TDA, TQA, TDB, TQB;

// we are never writing in port B so DB can be whatever
logic [sram_word-1:0] DB;

sram_dp_reg_t rd_reg, rd_reg1, rd_reg_next, rd_reg_out, wr_reg, wr_reg1, wr_reg_next, wr_reg_out;
logic [$clog2(sram_addr)-1:0] cnt, read_cnt;

logic latch_jitter_flag, latch_jitter_flag_rd;
logic read_cnt_flag;

logic enque, shifter_rdy;
logic [5:0] num_good_bits_debug;
logic [latch_sources-1:0] buff_in;

assign rd_good_arr = ~fail_arr & valid_arr;
assign es_out_jitter = ES_in[63:32];
assign es_out_latch = ES_in[31:0];

// we have a valid array that specifies which bits that are read out should actually be considered in the sram read buffer
// we have a fail arr that says that we should definitely not be considering the outputs of these sources at all anymore
// we have two different logic arrays for latch and jitter that have the output of each es that we need to write into sram
// sram writes latch bits into even addresses and odd addresses hold jitter values
// we need a mechanism to mark which addresses have been read from so that it does not read from that address again until it has been written to again --> this will actually never happen
// create a buffer that isolates bits from the 32 bit sram out values from the given fail_arr and valid_arr so that it writes to a buffer that fills up till 384 bits are present for aes deque to get

assign TAA = '0;
assign TDA = '0;
assign TQA = '0;
assign TAB = '0;
assign TDB = '0;
assign TQB = '0;

assign mask_in = latch_jitter_flag_rd ? rd_good_arr[63:32] : rd_good_arr[latch_sources-1:0];

always_ff @(posedge clk) begin
    if (rst) begin
        rd_reg_out <= '0;
        wr_reg_out <= '0;
        wr_reg1 <= '0;
        rd_reg1 <= '0;
        rd_reg <= '0;
        wr_reg <= '0;
    end else begin
        rd_reg <= rd_reg_next;
        wr_reg <= wr_reg_next;
        wr_reg1 <= wr_reg;
        rd_reg1 <= rd_reg;
        rd_reg_out <= rd_reg1;
        wr_reg_out <= wr_reg1;
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        cnt <= '0;
        latch_jitter_flag <= '0;
    end else if (full) begin
        // do nothing
    end else begin
        if (cnt == 2046 && valid_arr[31:0] != '0) begin
            cnt <= 1'b1;
            latch_jitter_flag <= ~latch_jitter_flag; // if high then odd address -> jitter
        end else if (cnt == 2047 && valid_arr[63:32] != '0) begin
            cnt <= '0;
            latch_jitter_flag <= ~latch_jitter_flag; // if low then even addresses -> latch
        end else if (valid_arr != '0) begin
            cnt <= cnt + 2;
        end else begin
            // do nothing
        end
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        read_cnt_flag <= '0;
    end else if (cnt > 31) begin // so once cnt hits 31 this goes high and we start reading
        read_cnt_flag <= 1'b1;
    end else begin

    end
end

always_ff @(posedge clk) begin

    if (rst) begin
        read_cnt <= '0;
        latch_jitter_flag_rd <= '0;
    end else if (full) begin
        // do nothing
    end else if (read_cnt_flag && valid_arr[31:0] != '0) begin
        if (read_cnt == 2046) begin
            read_cnt <= 1'b1;
            latch_jitter_flag_rd <= ~latch_jitter_flag_rd; // if high then odd address -> jitter
        end else if (read_cnt == 2047 && valid_arr[63:32] != '0) begin
            read_cnt <= '0;
            latch_jitter_flag_rd <= ~latch_jitter_flag_rd; // if low then even addresses -> latch
        end else begin
            read_cnt <= read_cnt + 2;
        end
    end else begin
        // DO NOTHING
    end

end

// for input comb logic
always_comb begin
    wr_reg_next = wr_reg;
    if (rst) begin
        wr_reg_next = '0;
        rd_reg_next = '0;
    end
    wr_reg_next.addr = cnt;
    rd_reg_next.addr = read_cnt;
    rd_reg_next.data = '0;
    if (latch_jitter_flag) begin
        wr_reg_next.data = es_out_jitter;
    end else begin
        wr_reg_next.data = es_out_latch;
    end
    if (valid_arr != '0) begin
        wr_reg_next.flag = 1'b1;
        if (read_cnt_flag) begin
            rd_reg_next.flag = 1'b1;
        end else begin
            rd_reg_next.flag = 1'b0;
        end
    end else begin
        wr_reg_next.flag = 1'b0;
        rd_reg_next.flag = 1'b0;
    end
end

genvar i;
generate
    for (i = 0; i < 32; i++) begin : gen_latch
        OHT latch_inst (
            .adc_in(ES_in[i]),
            .clk(clk),
            .rst(rst),
            .debug_mode(debug_mode),
            .spi_reg_lsb(spi_reg_lsb),
            .full(full),

            .perm_fail(fail_arr[i]),
            .valid(valid_arr[i]),
            .calibration_arr_n(arr_n[i]),
            .calibration_arr_p(arr_p[i])
        );
    end
    for (i = 0; i < 32; i++) begin : gen_jitter
        OHT_J jitter_inst (
            .adc_in(ES_in[32+i]),
            .clk(clk),
            .rst(rst),
            .debug_mode(debug_mode),

            .perm_fail(fail_arr[32+i]),
            .valid(valid_arr[32+i]),
            .j_disable(j_disable_arr[i])
        );
    end

endgenerate

streaming_bit_compactor shifter (
    .clk(clk),
    .rst(rst),
    .data_in(QB),
    .mask_in(mask_in),
    .valid_in(rd_reg_out.flag),
    .data_out(buff_in),
    .valid_out(shifter_rdy),
    .num_good_bits_debug(num_good_bits_debug)
);

que_fiao sram_aes_buff (
    .clk(clk),
    .rst(rst),
    
    .wdata(buff_in),
    .rdata(cond_out),
    
    .enque(shifter_rdy),
    .deque(deque),

    .full(full),
    .empty(empty)
);

// PORTA Write ONLY
// PORTB Read ONLY

oht_dp_sram_not_tcc rng_storage(
    // outputs:
    // A
    .CENYA(CENYA),
    .WENYA(WENYA),
    .AYA(AYA),
    .DYA(DYA),
    .QA(QA),
    .QIA(QIA),
    .PENYA(PENYA),
    // B
    .CENYB(CENYB),
    .WENYB(WENYB),
    .AYB(AYB),
    .DYB(DYB),
    .QB(QB),
    .QIB(QIB),
    .PENYB(PENYB),
    // inputs:
    // A
    .CLKA(clk),
    .CENA(1'b0),
    .WENA(1'b0),
    .AA(wr_reg_next.addr),    // need in types
    .DA(wr_reg_next.data),    // need in types
    .EMAA(3'b000),
    .TENA(1'b1),
    .BENA(1'b1),
    .TCENA(1'b0),
    .TWENA(1'b0),
    .TAA(TAA),  
    .TDA(TDA),
    .TQA(TQA),
    .PENA(1'b0),
    .TPENA(1'b0),
    // B
    .CLKB(clk),
    .CENB(1'b0),
    .WENB(1'b1),
    .AB(rd_reg_next.addr),    // need in types
    .DB(rd_reg_next.data),    // '0
    .EMAB(3'b000),
    .TENB(1'b1),
    .BENB(1'b1),
    .TCENB(1'b0),
    .TWENB(1'b0),
    .TAB(TAB),
    .TDB(TDB),
    .TQB(TQB),
    .PENB(1'b0),
    .TPENB(1'b0),

    .RETN(~rst),
    .PGEN(1'b0)
);

endmodule