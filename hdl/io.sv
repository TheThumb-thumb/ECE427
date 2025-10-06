module io_in (
    input   wire    chipout,
    output  wire    chipin
);

BUFZX2MA10TR in_buf ( .A(chipout), .OE(1'b1), .Y(chipin) );

endmodule

module io_out (
    output  wire    chipout,
    input   wire    chipin
);

logic buffered_chipin [2];

BUFZX2MA10TR buffered_chipin_i_0 ( .A(chipin), .OE(1'b1), .Y(buffered_chipin[0]));
BUFZX2MA10TR buffered_chipin_i_1 ( .A(buffered_chipin[0]), .OE(1'b1), .Y(buffered_chipin[1]));

logic [3:0] inter_wire_o_out;

BUFZX2MA10TR inter_wire_o_out_i_0 ( .A(buffered_chipin[1]), .OE(1'b1), .Y(inter_wire_o_out[0]));
BUFZX2MA10TR inter_wire_o_out_i_1 ( .A(buffered_chipin[1]), .OE(1'b1), .Y(inter_wire_o_out[1]));
BUFZX2MA10TR inter_wire_o_out_i_2 ( .A(buffered_chipin[1]), .OE(1'b1), .Y(inter_wire_o_out[2]));
BUFZX2MA10TR inter_wire_o_out_i_3 ( .A(buffered_chipin[1]), .OE(1'b1), .Y(inter_wire_o_out[3]));

BUFZX16MA10TR out_buf_0 ( .A(inter_wire_o_out[0]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_1 ( .A(inter_wire_o_out[0]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_2 ( .A(inter_wire_o_out[0]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_3 ( .A(inter_wire_o_out[0]), .OE(1'b1), .Y(chipout) );

BUFZX16MA10TR out_buf_4 ( .A(inter_wire_o_out[1]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_5 ( .A(inter_wire_o_out[1]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_6 ( .A(inter_wire_o_out[1]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_7 ( .A(inter_wire_o_out[1]), .OE(1'b1), .Y(chipout) );

BUFZX16MA10TR out_buf_8 ( .A(inter_wire_o_out[2]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_9 ( .A(inter_wire_o_out[2]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_a ( .A(inter_wire_o_out[2]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_b ( .A(inter_wire_o_out[2]), .OE(1'b1), .Y(chipout) );

BUFZX16MA10TR out_buf_c ( .A(inter_wire_o_out[3]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_d ( .A(inter_wire_o_out[3]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_e ( .A(inter_wire_o_out[3]), .OE(1'b1), .Y(chipout) );
BUFZX16MA10TR out_buf_f ( .A(inter_wire_o_out[3]), .OE(1'b1), .Y(chipout) );

endmodule

module io_tri (
    inout   wire    chipout,
    output  logic   i,
    input   logic   o,
    input   logic   t
);

io_in in_buf ( .chipout(chipout), .chipin(i) );


logic buffered_o [2];
logic buffered_t [2];

BUFZX2MA10TR buffered_o_i_0 ( .A(o),  .OE(1'b1), .Y(buffered_o[0]));
BUFZX2MA10TR buffered_t_i_0 ( .A(~t), .OE(1'b1), .Y(buffered_t[0]));

BUFZX2MA10TR buffered_o_i_1 ( .A(buffered_o[0]), .OE(1'b1), .Y(buffered_o[1]));
BUFZX2MA10TR buffered_t_i_1 ( .A(buffered_t[0]), .OE(1'b1), .Y(buffered_t[1]));

logic [3:0] inter_wire_o_out;
logic [3:0] inter_wire_o_tri;

BUFZX2MA10TR inter_wire_o_out_i_0 ( .A(buffered_o[1]), .OE(1'b1), .Y(inter_wire_o_out[0]));
BUFZX2MA10TR inter_wire_o_out_i_1 ( .A(buffered_o[1]), .OE(1'b1), .Y(inter_wire_o_out[1]));
BUFZX2MA10TR inter_wire_o_out_i_2 ( .A(buffered_o[1]), .OE(1'b1), .Y(inter_wire_o_out[2]));
BUFZX2MA10TR inter_wire_o_out_i_3 ( .A(buffered_o[1]), .OE(1'b1), .Y(inter_wire_o_out[3]));

BUFZX2MA10TR inter_wire_o_tri_i_0 ( .A(buffered_t[1]), .OE(1'b1), .Y(inter_wire_o_tri[0]));
BUFZX2MA10TR inter_wire_o_tri_i_1 ( .A(buffered_t[1]), .OE(1'b1), .Y(inter_wire_o_tri[1]));
BUFZX2MA10TR inter_wire_o_tri_i_2 ( .A(buffered_t[1]), .OE(1'b1), .Y(inter_wire_o_tri[2]));
BUFZX2MA10TR inter_wire_o_tri_i_3 ( .A(buffered_t[1]), .OE(1'b1), .Y(inter_wire_o_tri[3]));

BUFZX16MA10TR out_buf_0 ( .A(inter_wire_o_out[0]), .OE(inter_wire_o_tri[0]), .Y(chipout) );
BUFZX16MA10TR out_buf_1 ( .A(inter_wire_o_out[0]), .OE(inter_wire_o_tri[0]), .Y(chipout) );
BUFZX16MA10TR out_buf_2 ( .A(inter_wire_o_out[0]), .OE(inter_wire_o_tri[0]), .Y(chipout) );
BUFZX16MA10TR out_buf_3 ( .A(inter_wire_o_out[0]), .OE(inter_wire_o_tri[0]), .Y(chipout) );

BUFZX16MA10TR out_buf_4 ( .A(inter_wire_o_out[1]), .OE(inter_wire_o_tri[1]), .Y(chipout) );
BUFZX16MA10TR out_buf_5 ( .A(inter_wire_o_out[1]), .OE(inter_wire_o_tri[1]), .Y(chipout) );
BUFZX16MA10TR out_buf_6 ( .A(inter_wire_o_out[1]), .OE(inter_wire_o_tri[1]), .Y(chipout) );
BUFZX16MA10TR out_buf_7 ( .A(inter_wire_o_out[1]), .OE(inter_wire_o_tri[1]), .Y(chipout) );

BUFZX16MA10TR out_buf_8 ( .A(inter_wire_o_out[2]), .OE(inter_wire_o_tri[2]), .Y(chipout) );
BUFZX16MA10TR out_buf_9 ( .A(inter_wire_o_out[2]), .OE(inter_wire_o_tri[2]), .Y(chipout) );
BUFZX16MA10TR out_buf_a ( .A(inter_wire_o_out[2]), .OE(inter_wire_o_tri[2]), .Y(chipout) );
BUFZX16MA10TR out_buf_b ( .A(inter_wire_o_out[2]), .OE(inter_wire_o_tri[2]), .Y(chipout) );

BUFZX16MA10TR out_buf_c ( .A(inter_wire_o_out[3]), .OE(inter_wire_o_tri[3]), .Y(chipout) );
BUFZX16MA10TR out_buf_d ( .A(inter_wire_o_out[3]), .OE(inter_wire_o_tri[3]), .Y(chipout) );
BUFZX16MA10TR out_buf_e ( .A(inter_wire_o_out[3]), .OE(inter_wire_o_tri[3]), .Y(chipout) );
BUFZX16MA10TR out_buf_f ( .A(inter_wire_o_out[3]), .OE(inter_wire_o_tri[3]), .Y(chipout) );

endmodule