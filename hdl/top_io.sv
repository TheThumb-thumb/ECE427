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
    input logic ss_n_io,       // Slave Select (active low)
    input logic debug_clk_io,  // Debug clock from FPGA
    input logic mosi_io,       // Master Out Slave In
    output logic miso_io,      // Master In Slave Out
    output logic spi_data_ready_io, //This will be useful for SPI communication

    // Debug pins
    input logic debug_io,
    input logic output_to_input_direct_io,
    input logic input_pin_1_io,
    output logic output_pin_2_io,
    output logic output_pin_1_io,

    input logic[3:0] temp_sens_in, // 0 -> bottom right 1 -> bottom left 2 -> top left 3 -> top right
    input logic     io_temp_debug,

    // Temp pins for verification (pretent to be entropy sources and temp sensor since no mixed signal)
    input logic [es_sources-1:0] entropy_source_array,
    output logic [latch_sources-1:0][calib_bits-1:0] arr_n, 
    output logic [latch_sources-1:0][calib_bits-1:0] arr_p,
    output logic [jitter_sources-1:0] jitter_disable_arr,
    output logic [13:0] temp_threshold_array [4]
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
logic rst_n;                              // input reset pin
logic rst_n_reg;
// Rand request and output pins:
logic rand_req;                           // input valid request pin
rand_req_t rand_req_type;                 // 3 input pins for types of random #s requested
logic [OUTPUT_WIDTH-1:0] rand_byte;      // 16 output pins from buffer with random #s requested
logic rand_valid;                        // output pin for rand #s valid
logic slow_clk;                          // output clk

// SPI Pins
logic ss_n;       // Slave Select (active low)
logic debug_clk;  // Debug clock from FPGA
logic mosi;       // Master Out Slave In
logic miso;      // Master In Slave Out
logic spi_data_ready; //This will be useful for SPI communication

// Debug pins
logic debug;   
logic output_to_input_direct;
logic input_pin_1;
logic output_pin_2;
logic output_pin_1;

always_ff @(posedge ic_clk) begin

    rst_n_reg <= rst_n;

end

// INPUT BUFFERS
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
            .chipin(rand_byte[i])
        );
    end
endgenerate

io_out out_rand_valid (
    .chipout(rand_valid_io),
    .chipin(rand_valid)
);
io_out out_slow_clk (
    .chipout(slow_clk_io),
    .chipin(slow_clk)
);
io_out out_miso(
    .chipout(miso_io),
    .chipin(miso)
);
io_out out_output_pin_2 (
    .chipout(output_pin_2_io),
    .chipin(output_pin_2)
);
io_out out_output_pin_1 (
    .chipout(output_pin_1_io),
    .chipin(output_pin_1)
);

top mixed_IC (
    .ic_clk(ic_clk),
    .rst_n(rst_n_reg),

    .rand_req(rand_req),
    .rand_req_type(rand_req_type),
    .rand_byte(rand_byte),
    .rand_valid(rand_valid),
    .slow_clk(slow_clk),

    .ss_n(ss_n),
    .debug_clk(debug_clk),
    .mosi(mosi),
    .miso(miso),
    .spi_data_ready(spi_data_ready),

    .debug(debug),
    .output_to_input_direct(output_to_input_direct),

    .output_pin_2(output_pin_2),
    .output_pin_1(output_pin_1),
    .input_pin_1(input_pin_1),

    .temp_sens_in(temp_sens_in),
    .io_temp_debug(io_temp_debug),
    
    .entropy_source_array(entropy_source_array),
    .arr_n(arr_n),
    .arr_p(arr_p),
    .jitter_disable_arr(jitter_disable_arr),
    .temp_threshold_array(temp_threshold_array)
);

endmodule
