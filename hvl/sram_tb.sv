import le_types::*;
import params::*;
module sram_tb;

logic clk, rst;
initial clk = 1'b0;
always #1ns clk = ~clk;

// inputs:
logic CLKA, CENA, WENA, CLKB, CENB, WENB, TENA, BENA, TCENA, TWENA, TENB,
BENB, TCENB, TWENB, RETN, PGEN, PENA, PENB, TPENA, TPENB;
logic [10:0] AA, AB, TAA, TAB;
logic [31:0] DA, DB, TDA, TQA, TDB, TQB;
logic [2:0] EMAA, EMBB;
assign TAA = '0;
assign TDA = '0;
assign TQA = '0;
// outputs:
logic CENYA, WENYA, CENYB, WENYB, PENYA, PENYB;
logic [10:0] AYA, AYB,;
logic [31:0] DYA, DYB, QA, QB, QIA, QIB;



oht_dp_sram dut (
    .CENYA(1'b0), 
    .WENYA(WENYA), 
    .AYA(AYA), 
    .DYA(DYA), 
    .CENYB(1'b0),
    .WENYB(WENYB),
    .AYB(AYB),
    .DYB(),
    .QA(QA), 
    .QB(QB), 
    .QIA(QIA),
    .QIB(QIB),
    .PENYA(PENYA),
    .PENYB(PENYB),
    .CLKA(clk),
    .CENA(1'b0),
    .WENA(WENA),
    .AA(AA),
    .DA(DA),
    .CLKB(clk),
    .CENB(1'b0),
    .WENB(WENB),
    .AB(AB),
    .DB(DB),
    .EMAA(3'b000),
    .EMAB(3'b000),
    .TENA(1'b1),
    .BENA(1'b1),
    .TCENA(1'b0),
    .TWENA(1'b0),
    .TAA(TAA),
    .TDA(TDA),
    .TQA(TQA),
    .TENB(1'b1),
    .BENB(1'b1),
    .TCENB(1'b0),
    .TWENB(1'b0),
    .TAB(TAB),
    .TDB(TDB),
    .TQB(TQB),
    .RETN(RETN),
    .PGEN(PGEN),
    .PENA(1'b0),
    .PENB(1'b0),
    .TPENA(1'b0),
    .TPENB(1'b0)

);

// CENYA,
// WENYA,
// AYA,
// DYA, 
// CENYB, 
// WENYB, 
// AYB, 
// DYB, 
// QA, 
// QB, 
// QIA, 
// QIB,
// PENYA, 
// PENYB, 
// CLKA, 
// CENA, 
// WENA, 
// AA, 
// DA, 
// CLKB, 
// CENB, 
// WENB, 
// AB, 
// DB, 
// EMAA, 
// EMAB, 
// TENA,
// BENA, 
// TCENA, 
// TWENA, 
// TAA, 
// TDA, 
// TQA, 
// TENB, 
// BENB, 
// TCENB, 
// TWENB, 
// TAB, 
// TDB, 
// TQB, 
// RETN,
// PGEN, 
// PENA, 
// PENB, 
// TPENA, 
// TPENB


endmodule : sram_tb