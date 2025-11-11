import le_types::*;
import params::*;
module top_io (
    // System CLK and RST pins:
    input logic ic_clk_io,                             // input clock pin
    input logic rst_n_io,                              // input reset pin

    // Rand request and output pins:
    input logic rand_req_io,                           // input valid request pin
    input rand_req_t rand_req_type_io,                 // 3 input pins for types of random #s requested
    output logic [OUTPUT_WIDTH-1:0] rand_byte_io,      // 16 output pins from buffer with random #s requested
    output logic rand_valid_io,                        // output pin for rand #s valid
    output logic slow_clk_io,                          // output clk

    // SPI Pins
    input logic ss_n_io,                                // Slave Select (active low)
    input logic debug_clk_io,                           // Debug clock from FPGA
    input logic mosi_io,                                // Master Out Slave In
    output logic miso_io,                               // Master In Slave Out
    output logic spi_data_ready_io,                     // This will be useful for SPI communication

    // Debug pins
    input logic debug_io,
    input logic output_to_input_direct_io,
    input logic input_pin_1_io,
    output logic output_pin_2_io,
    output logic output_pin_1_io,

    //Pins that connect to manual layout components (Entropy sources, temp sensor)
    // Temperature sensor I/O
    input logic temp_debug_io,
    output logic [3:0] EN_out1,
    output logic [3:0] EN_out2,
    input  logic [TEMP_WIDTH-1:0] temp_counter_0,
    input  logic [TEMP_WIDTH-1:0] temp_counter_1,
    input  logic [TEMP_WIDTH-1:0] temp_counter_2,
    input  logic [TEMP_WIDTH-1:0] temp_counter_3,

    //Entropy Sources I/O
    input logic [es_sources-1:0] entropy_source_array,      // lower 0-31 are latch, 32-63 are jitter
    output logic [latch_sources-1:0][calib_bits-1:0] arr_n,
    output logic [latch_sources-1:0][calib_bits-1:0] arr_p,
    output logic [jitter_sources-1:0] jitter_disable_arr, 

    output logic [63:0] analog_clk,

    input logic vdd_A,
    input logic vdd_B,

    output logic [31:0] jitter_vdd_A,
    output logic [31:0] jitter_vdd_B


);

// TOTAL PIN COUNT: 38 pins

// POWER PINS:
// 2 VDD pins, 2 VSS pins = 4 pins

// IN:
// clk, rst, rand_req, 3 pins rand_req_type, slave select, debug clk, mosi, debug,
// output_to_input_direct, input_pin1 = 12 pins input

// OUT:
// 16 pins output, rand_valid, slow_clk, miso, spi_data_ready, output_pin2, output_pin1
// = 22 pins output

// logics for I/O Module
logic ic_clk;                             // input clock pin
logic rst_n, rst_n_reg;
// Rand request and output pins:
logic rand_req, rand_req_reg;                                // input valid request pin
rand_req_t rand_req_type, rand_req_type_reg;                 // 3 input pins for types of random #s requested
logic [OUTPUT_WIDTH-1:0] rand_byte, rand_byte_reg;           // 16 output pins from buffer with random #s requested
logic rand_valid, rand_valid_reg;                            // output pin for rand #s valid
logic slow_clk, slow_clk_reg;                                // output clk

// SPI Pins
logic ss_n, ss_n_reg;                                        // Slave Select (active low)
logic debug_clk;                                             // Debug clock from FPGA
logic mosi, mosi_reg;                                        // Master Out Slave In
logic miso, miso_reg;                                        // Master In Slave Out
logic spi_data_ready, spi_data_ready_reg; //This will be useful for SPI communication

// Debug pins
logic debug, debug_reg;   
logic output_to_input_direct, output_to_input_direct_reg;
logic input_pin_1, input_pin_1_reg;
logic output_pin_2, output_pin_2_reg;
logic output_pin_1, output_pin_1_reg;

logic [3:0] temp_sens_in; // 0 -> bottom right 1 -> bottom left 2 -> top left 3 -> top right
logic temp_debug_reg, temp_debug;
logic clk;

logic [TEMP_WIDTH-1:0] temp_threshold_array_0;
logic [TEMP_WIDTH-1:0] temp_threshold_array_1;
logic [TEMP_WIDTH-1:0] temp_threshold_array_2;
logic [TEMP_WIDTH-1:0] temp_threshold_array_3;

// for analog clk
logic latch_jitter_clk;

assign clk = debug ? debug_clk : ic_clk;

assign jitter_vdd_A = {32{vdd_A}};
assign jitter_vdd_B = {32{vdd_B}};



always_ff @(posedge clk) begin
    rst_n_reg <= rst_n;
    rand_req_reg <= rand_req;
    rand_req_type_reg <= rand_req_type;
    rand_byte_reg <= rand_byte;
    rand_valid_reg <= rand_valid;
    ss_n_reg <= ss_n;
    mosi_reg <= mosi;
    miso_reg <= miso;
    spi_data_ready_reg <= spi_data_ready;
    output_pin_2_reg <= output_pin_2;
    output_pin_1_reg <= output_pin_1;
    debug_reg <= debug;
    output_to_input_direct_reg <= output_to_input_direct;
    input_pin_1_reg <= input_pin_1;
    slow_clk_reg <= slow_clk;
    temp_debug_reg <= temp_debug;
end

ro_temp_control_v1 temp0 (
    .EN_IN(~temp_debug_io),               // to turn on or turn off temp sensor
    .CLK(clk),                 // normal clock of system
    .TEMP_IN(temp_counter_0),             // one comes from ring oscillator
    .TEMP_CMP(temp_threshold_array_0),            // one comes from spi
    .EN_OUT1(EN_out1[0]),             // feeds into temperature sensor
    .EN_OUT2(EN_out2[0]),             // feeds into temperature sensor
    .TEMP_CMP_OUT_REG(temp_sens_in[0])     // one hot out for top_io
);

ro_temp_control_v1 temp1 (
    .EN_IN(~temp_debug_io),               // to turn on or turn off temp sensor
    .CLK(clk),                 // normal clock of system
    .TEMP_IN(temp_counter_1),             // one comes from ring oscillator
    .TEMP_CMP(temp_threshold_array_1),            // one comes from spi
    .EN_OUT1(EN_out1[1]),             // feeds into temperature sensor
    .EN_OUT2(EN_out2[1]),             // feeds into temperature sensor
    .TEMP_CMP_OUT_REG(temp_sens_in[1])     // one hot out for top_io
);

ro_temp_control_v1 temp2 (
    .EN_IN(~temp_debug_io),               // to turn on or turn off temp sensor
    .CLK(clk),                 // normal clock of system
    .TEMP_IN(temp_counter_2),             // one comes from ring oscillator
    .TEMP_CMP(temp_threshold_array_2),            // one comes from spi
    .EN_OUT1(EN_out1[2]),             // feeds into temperature sensor
    .EN_OUT2(EN_out2[2]),             // feeds into temperature sensor
    .TEMP_CMP_OUT_REG(temp_sens_in[2])     // one hot out for top_io
);

ro_temp_control_v1 temp3 (
    .EN_IN(~temp_debug_io),               // to turn on or turn off temp sensor
    .CLK(clk),                 // normal clock of system
    .TEMP_IN(temp_counter_3),             // one comes from ring oscillator
    .TEMP_CMP(temp_threshold_array_3),            // one comes from spi
    .EN_OUT1(EN_out1[3]),             // feeds into temperature sensor
    .EN_OUT2(EN_out2[3]),             // feeds into temperature sensor
    .TEMP_CMP_OUT_REG(temp_sens_in[3])     // one hot out for top_io
);

// INPUT BUFFERS
io_in in_temp_debug (
    .chipout(temp_debug_io),
    .chipin(temp_debug)
);
io_in in_ic_clk (
    .chipout(ic_clk_io),
    .chipin(ic_clk)
);
io_in in_rst_n (
    .chipout(rst_n_io),
    .chipin(rst_n)
);
io_in in_rand_req (
    .chipout(rand_req_io),
    .chipin(rand_req)
);
io_in in_rand_req_type_0 (
    .chipout(rand_req_type_io[0]),
    .chipin(rand_req_type[0])
);
io_in in_rand_req_type_1 (
    .chipout(rand_req_type_io[1]),
    .chipin(rand_req_type[1])
);
io_in in_rand_req_type_2 (
    .chipout(rand_req_type_io[2]),
    .chipin(rand_req_type[2])
);
io_in in_ss_n (
    .chipout(ss_n_io),
    .chipin(ss_n)
);
io_in in_debug_clk (
    .chipout(debug_clk_io),
    .chipin(debug_clk)
);
io_in in_mosi (
    .chipout(mosi_io),
    .chipin(mosi)
);
io_in in_debug (
    .chipout(debug_io),
    .chipin(debug)
);
io_in in_output_to_intput_direct (
    .chipout(output_to_input_direct_io),
    .chipin(output_to_input_direct)
);
io_in in_input_pin_1 (
    .chipout(input_pin_1_io),
    .chipin(input_pin_1)
);

// OUTPUT BUFFERS:
genvar i;
generate
    for(i = 0; i < OUTPUT_WIDTH; ++i) begin
        io_out out_rand_byte (
            .chipout(rand_byte_io[i]),
            .chipin(rand_byte_reg[i])
        );
    end
endgenerate

io_out out_rand_valid (
    .chipout(rand_valid_io),
    .chipin(rand_valid_reg)
);
io_out out_slow_clk (
    .chipout(slow_clk_io),
    .chipin(slow_clk_reg)
);
io_out out_miso(
    .chipout(miso_io),
    .chipin(miso_reg)
);
io_out out_output_pin_2 (
    .chipout(output_pin_2_io),
    .chipin(output_pin_2_reg)
);
io_out out_output_pin_1 (
    .chipout(output_pin_1_io),
    .chipin(output_pin_1_reg)
);
io_out out_spi_data_ready (
    .chipout(spi_data_ready_io),
    .chipin(spi_data_ready_reg)
);

top mixed_IC (
    .ic_clk(ic_clk),
    .rst_n(rst_n_reg),

    .rand_req(rand_req_reg),
    .rand_req_type(rand_req_type_reg),
    .rand_byte(rand_byte),
    .rand_valid(rand_valid),
    .slow_clk(slow_clk),

    .ss_n(ss_n_reg),
    .debug_clk(debug_clk),
    .mosi(mosi_reg),
    .miso(miso),
    .spi_data_ready(spi_data_ready),

    .debug(debug_reg),
    .output_to_input_direct(output_to_input_direct_reg),

    .output_pin_2(output_pin_2),
    .output_pin_1(output_pin_1),
    .input_pin_1(input_pin_1_reg),

    .temp_sens_in(temp_sens_in),
    .io_temp_debug(temp_debug_reg),
    .temp_threshold_array_0(temp_threshold_array_0),
    .temp_threshold_array_1(temp_threshold_array_1),
    .temp_threshold_array_2(temp_threshold_array_2),
    .temp_threshold_array_3(temp_threshold_array_3),
    .temp_counter_0(temp_counter_0),
    .temp_counter_1(temp_counter_1),
    .temp_counter_2(temp_counter_2),
    .temp_counter_3(temp_counter_3),
    
    .entropy_source_array(entropy_source_array),
    .arr_n(arr_n),
    .arr_p(arr_p),
    .jitter_disable_arr(jitter_disable_arr),
    .analog_clk(latch_jitter_clk)
);

assign analog_clk = {64{latch_jitter_clk}};


endmodule
