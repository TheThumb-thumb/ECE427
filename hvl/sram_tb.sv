import le_types::*;
import params::*;
module sram_tb;

logic clk, rst;
initial clk = 1'b0;
always #1ns clk = ~clk;

// inputs:
logic CLKA, CENA, WENA, CLKB, CENB, WENB, TENA, BENA, TCENA, TWENA, TENB,
BENB, TCENB, TWENB, RETN, PGEN, PENA, PENB, TPENA, TPENB;
logic [10:0] AA, AB, TAA, TAB, AB_reg;
logic [31:0] DA, DB, TDA, TQA, TDB, TQB;
logic [2:0] EMAA, EMBB;

// outputs:
logic CENYA, WENYA, CENYB, WENYB, PENYA, PENYB;
logic [10:0] AYA, AYB;
logic [31:0] DYA, DYB, QA, QB, QIA, QIB;

// PORTA Write ONLY
// PORTB Read ONLY

logic [10:0] counterA, counterB;

always_ff @( posedge clk ) begin : read
    if (rst) begin
        AB_reg <= '0;
        counterA <= '0;
        counterB <= '0;
    end else begin
        AB_reg <= 11'h7ED;
        counterA <= counterA + 1;
        if (counterA >= 32) begin
            counterB <= counterB + 1;
        end
    end
end

assign WENA = '0;
assign WENB = '1;
assign AA = counterA;
assign AB = counterB;
assign DA = 32'hECEB0000 + counterA;
assign DB = 'x;

assign TAA = '0;
assign TDA = '0;
assign TQA = '0;

oht_dp_sram_not_tcc dut (
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
    .WENA(WENA),
    .AA(AA),
    .DA(DA),
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
    .WENB(WENB),
    .AB(AB),
    .DB(DB),
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

initial begin
    $fsdbDumpfile("sram_dump.fsdb");
    $fsdbDumpvars(0, "+all");
    rst = 1'b1;
    #10000ns
    rst = 1'b0;
    #100000ns
    $finish();
end

endmodule : sram_tb