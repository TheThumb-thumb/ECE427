module oht_top
import le_types::*;
import params::*;
localparam cond_width = 384;
localparam calib_bits = 8;
localparam es_sources = 64;
localparam latch_sources = 32;
(
    input logic clk,
    input logic rst,

    input logic adc_clk,
    input logic [es_sources-1:0] ES_in, // 0-31 latch 32-63 jitter
    input logic deque,                  // tells us aes is reading? Does that matter?
    input logic debug_mode,
    input logic [7:0] spi_reg_lsb,

    output logic [es_sources-1:0] ES_valid,
    output logic [cond_width-1:0] cond_out,
    output logic full,
    output logic empty,
    output logic [latch_sources-1:0][calib_bits-1:0] arr_n,
    output logic [latch_sources-1:0][calib_bits-1:0] arr_p

);

logic [] fail_arr 

OHT latch_0 (
    .adc_in(ES_in[0]),
    .clk(clk),
    .rst(rst),
    .debug_mode(debug_mode),
    .spi_reg_lsb(spi_reg_lsb),
    .full(full),

    .perm_fail(),
    .valid(),
    .calibration_arr_n(arr_n[0]),
    .calibration_arr_p(arr_p[0])
);

OHT latch_1 (
    
);

OHT latch_2 (
    
);

OHT latch_3 (
    
);

OHT latch_4 (
    
);

OHT latch_5 (
    
);

OHT latch_6 (
    
);

OHT latch_7 (
    
);

OHT latch_8 (
    
);

OHT latch_9 (
    
);

OHT latch_10 (
    
);

OHT latch_11 (
    
);

OHT latch_12 (
    
);

OHT latch_13 (
    
);

OHT latch_14 (
    
);

OHT latch_15 (
    
);

OHT latch_16 (
    
);

OHT latch_17 (
    
);

OHT latch_18 (
    
);

OHT latch_19 (
    
);

OHT latch_20 (
    
);

OHT latch_21 (
    
);

OHT latch_22 (
    
);

OHT latch_23 (
    
);

OHT latch_24 (
    
);

OHT latch_25 (
    
);

OHT latch_26 (
    
);

OHT latch_27 (
    
);

OHT latch_28 (
    
);

OHT latch_29 (
    
);

OHT latch_30 (
    
);

OHT latch_31 (
    
);

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//***************************************************************************************************************************************************************************************************//
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

OHT_J jitter_0 (

);

OHT_J jitter_1 (
    
);

OHT_J jitter_2 (
    
);

OHT_J jitter_3 (
    
);

OHT_J jitter_4 (
    
);

OHT_J jitter_5 (
    
);

OHT_J jitter_6 (
    
);

OHT_J jitter_7 (
    
);

OHT_J jitter_8 (
    
);

OHT_J jitter_9 (
    
);

OHT_J jitter_10 (
    
);

OHT_J jitter_11 (
    
);

OHT_J jitter_12 (
    
);

OHT_J jitter_13 (
    
);

OHT_J jitter_14 (
    
);

OHT_J jitter_15 (
    
);

OHT_J jitter_16 (
    
);

OHT_J jitter_17 (
    
);

OHT_J jitter_18 (
    
);

OHT_J jitter_19 (
    
);

OHT_J jitter_20 (
    
);

OHT_J jitter_21 (
    
);

OHT_J jitter_22 (
    
);

OHT_J jitter_23 (
    
);

OHT_J jitter_24 (
    
);

OHT_J jitter_25 (
    
);

OHT_J jitter_26 (
    
);

OHT_J jitter_27 (
    
);

OHT_J jitter_28 (
    
);

OHT_J jitter_29 (
    
);

OHT_J jitter_30 (
    
);

OHT_J jitter_31 (
    
);


endmodule