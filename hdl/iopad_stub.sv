module BUFX2MA10TR (
    input   wire    A,
    output  wire    Y
);

assign Y = A;

endmodule

module BUFX16MA10TR (
    input   wire    A,
    output  wire    Y
);

assign Y = A;

endmodule

module BUFZX2MA10TR (
    input   wire    A,
    input   wire    OE,
    output  wire    Y
);

assign Y = OE ? A : 1'bz;

endmodule

module BUFZX16MA10TR (
    input   wire    A,
    input   wire    OE,
    output  wire    Y
);

assign Y = OE ? A : 1'bz;

endmodule