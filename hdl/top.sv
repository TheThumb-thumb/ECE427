//======================================================================
// Top-Level Module
//
// Description:
// This module serves as the top-level wrapper, instantiating and
// connecting the main control block and the data path multiplexers.
//
//======================================================================
import le_types::*;
import params::*;
module top (
    // PHYSICAL PINS

    //CLK+RST
    input logic ic_clk,    // Clock from clock gen IC
    input logic rst_n,    // Reset (active low)

    //CPU I/O
    input logic rand_req,                       // Request pin (active high)
    input rand_req_t rand_req_type,             // Request type (see types.sv for scheme) 
    output logic [OUTPUT_WIDTH-1:0] rand_byte,  // Byte-sliced output
    output logic rand_valid,                    // Output valid signal (active high)
    
    // SPI Pins
    input logic ss_n,       // Slave Select (active low)
    input logic debug_clk,  // Debug clock from FPGA
    input logic mosi,       // Master Out Slave In
    output logic miso,      // Master In Slave Out
    output logic spi_data_ready, //This will be useful for SPI communication

    input logic debug,      // Debug pin (active high)
    input logic output_to_input_direct, // Used when we want to bypass a module internally

    // Serial I/O for debug
    output logic output_pin_2,
    output logic output_pin_1,
    input logic input_pin_1,

    // //Temp pins for verification (no output buffer or entropy)
    input logic [es_sources-1:0] entropy_source_array,
    // output logic [256:0] temp_seed_out,
    // output logic [127:0] temp_drbg_out,
    // output logic temp_out_valid
    output logic [latch_sources-1:0][calib_bits-1:0] arr_n, 
    output logic [latch_sources-1:0][calib_bits-1:0] arr_p,
    output logic [jitter_sources-1:0] jitter_disable_arr

);

    logic empty;
    logic [es_sources-1:0] rd_good_arr;

    //------------------------------------------------------------------
    // Wire/Reg Instantiations
    //------------------------------------------------------------------

    //Connections between OHT and Conditioner
    logic oht_cond_valid, oht_cond_ready;
    logic [DATA_WIDTH-1:0] message;
    logic [(DATA_WIDTH/2)-1:0] key;

    //Connections between Conditioner and DRBG
    logic cond_drbg_valid, cond_drbg_ready, cond_triv_ready, cond_triv_valid;
    logic [DATA_WIDTH-1:0] seed;

    //Connections between Conditioner and Output Buffer
    logic cond_output_valid, cond_output_ready;

    //Connections between DRBG and Output Buffer
    logic drbg_output_valid, drbg_output_ready;
    logic drbg_instantiate, drbg_reseed, drbg_generate; 
    logic [15:0] drbg_num_blocks;
    logic drbg_random_valid;
    logic [127:0] drbg_random_block;

    // Wires to connect control to other modules (from control)
    logic        clk;
    logic        latch_entropy_mux_out; // Serial debug output from selected latch entropy source
    logic        jitter_entropy_mux_out; // Serial debug output from selected latch entropy source
    logic [15:0] entropy_calibration; // Entropy calibration value for debug
    logic        latch_oht_mux_out; // Serial debug output from selected latch OHT
    logic        jitter_oht_mux_out; // Serial debug output from selected jitter OHT
    logic        latch_oht_mux_in; // Serial debug input to selected latch OHT
    logic        jitter_oht_mux_in; // Serial debug input to selected jitter OHT
    logic        CTD_debug_input; // Serial debug input to conditioner/trivium/DRBG
    logic [13:0] temp_counter_0, temp_counter_1, temp_counter_2, temp_counter_3; // Counters for temp sensors, verify w Anthony
    logic [13:0] temp_threshold_0, temp_threshold_1, temp_threshold_2, temp_threshold_3; // Thresholds for temp sensors
    logic        temp_sense_0_good, temp_sense_1_good, temp_sense_2_good, temp_sense_3_good; // Single bit boolean good/bad for temp sensor
    logic [15:0] lower_latch_entropy_good, upper_latch_entropy_good, lower_jitter_entropy_good, upper_jitter_entropy_good;
    logic [21:0] curr_state; // Contains all the info for 

    // MUX port declarations
    logic [31:0] latch_entropy_sources_out, 
    latch_oht_default_in, 
    jitter_entropy_sources_out,
    jitter_oht_default_in,
    latch_oht_default_out,
    latch_sram_default_in,
    jitter_oht_default_out,
    jitter_sram_default_in;

    //------------------------------------------------------------------
    // Module Instantiations
    //------------------------------------------------------------------

    // Instantiate the control module
    control u_control (
        .ic_clk(ic_clk),
        .debug_clk(debug_clk),
        .rst_n(rst_n),
        .mosi(mosi),
        .ss_n(ss_n),
        .debug(debug),

        .miso(miso),
        .output_pin_2(output_pin_2),
        .output_pin_1(output_pin_1),
        .input_pin_1(input_pin_1),
        .output_to_input_direct(output_to_input_direct),
        .spi_data_ready(spi_data_ready),

        .clk(clk), // This is the new system clock (muxed between ic_clk and debug_clk pins)
        
        .latch_entropy_mux_out(latch_entropy_mux_out), // Serial output from selected latch entropy source
        .jitter_entropy_mux_out(jitter_entropy_mux_out), // Serial debug output from selected latch entropy source
                
        .entropy_calibration(entropy_calibration), // Entropy calibration value for debug

        .latch_oht_mux_in(latch_oht_mux_in),  // Serial debug input to selected latch OHT
        .jitter_oht_mux_in(jitter_oht_mux_in),  // Serial debug input to selected jitter OHT
        
        .CTD_debug_input(CTD_debug_input), // Input to MUX into the conditioner, trivium, DRBG

        .temp_counter_0(temp_counter_0),  // Counters for temp sensors
        .temp_counter_1(temp_counter_1),
        .temp_counter_2(temp_counter_2),
        .temp_counter_3(temp_counter_3),

        .temp_threshold_0(temp_threshold_0),  // Thresholds for temp sensors
        .temp_threshold_1(temp_threshold_1),
        .temp_threshold_2(temp_threshold_2),
        .temp_threshold_3(temp_threshold_3),

        .temp_sense_0_good(temp_sense_0_good), // Single bit boolean good/bad for temp sensor
        .temp_sense_1_good(temp_sense_1_good),
        .temp_sense_2_good(temp_sense_2_good),
        .temp_sense_3_good(temp_sense_3_good),

        .lower_latch_entropy_good(lower_latch_entropy_good),
        .upper_latch_entropy_good(upper_latch_entropy_good),
        .lower_jitter_entropy_good(lower_jitter_entropy_good),
        .upper_jitter_entropy_good(upper_jitter_entropy_good),

        .curr_state(curr_state)
    );

    // Mux between Latch Entropy Sources and Latch OHT. This 
    logic [5:0] output_select_latch_entropy_oht;
    logic [5:0] input_select_latch_entropy_oht;
    always_comb begin
        if (curr_state[20:19] == 3'd1) output_select_latch_entropy_oht = {1'b1, curr_state[20:19]};
        else if (curr_state[13:12] == 3'd1) output_select_latch_entropy_oht = {1'b1, curr_state[11:7]};
        else output_select_latch_entropy_oht = 6'b0; // Default value when neither condition is true

        if (curr_state[6:5] == 3'd1) input_select_latch_entropy_oht = {1'b1, curr_state[4:0]};
        else input_select_latch_entropy_oht = 6'b0;

    end
    entropy_oht_mux latch_entropy_oht_mux (
        .debug               (debug),
        .entropy_sources_out (latch_entropy_sources_out),
        .oht_mux_in          (latch_oht_mux_in),        // Serial input to selected latch OHT for debug
        .output_select       (output_select_latch_entropy_oht),          // Select signals for the LATCH module
        .input_select        (input_select_latch_entropy_oht),           // Select signals for the LATCH module
        .entropy_mux_out     (latch_entropy_mux_out),           // Serial output from selected latch entropy source for debug
        .oht_in              (latch_oht_default_in)              // Input pins to Latch OHT (32 bits)
    );


    logic [5:0] output_select_jitter_entropy_oht;
    logic [5:0] input_select_jitter_entropy_oht;
    always_comb begin
        if (curr_state[20:19] == 3'd2) output_select_jitter_entropy_oht = {1'b1, curr_state[18:14]};

        else if (curr_state[13:12]== 3'd2) output_select_jitter_entropy_oht = {1'b1, curr_state[11:7]};
 
        else output_select_jitter_entropy_oht = 6'b0; // Default value when neither condition is true

        if (curr_state[6:5]==3'd2) input_select_jitter_entropy_oht = {1'b1, curr_state[4:0]};
        else input_select_jitter_entropy_oht = 6'b0;

    end
    // Mux between Jitter Entropy Sources and Jitter OHT
    entropy_oht_mux jitter_entropy_oht_mux (
        .debug               (debug),
        .entropy_sources_out (jitter_entropy_sources_out),
        .oht_mux_in          (jitter_oht_mux_in),
        .output_select       (output_select_jitter_entropy_oht),          // Select signals for the JITTER module
        .input_select        (input_select_jitter_entropy_oht),           // Select signals for the JITTER module
        .entropy_mux_out     (jitter_entropy_mux_out),
        .oht_in              (jitter_oht_default_in)             // Input pins to Jitter OHT
    );

    // Instantiate the OHT
    oht_top oht_inst_0 (
        .clk(clk),
        .rst(~rst_n),

        .ES_in(entropy_source_array),
        .deque(oht_cond_ready),
        .debug_mode(debug),
        .spi_reg_lsb(curr_state[15:0]),

        .cond_out({key,message}),
        .full(oht_cond_valid),
        .empty(empty),

        .arr_n(arr_n),
        .arr_p(arr_p),
        .j_disable_arr(jitter_disable_arr),
        .rd_good_arr(rd_good_arr)
    );

    logic [1:0] CTD_serial_sel;
    logic conditioner_debug;
    logic trivium_debug;
    logic drbg_debug;
    logic parallelizer_data_valid_out;
    logic [383:0] debug_parallel_out;


    // Instantiate the Conditioner
    conditioner #(
        .DATA_WIDTH(256)
    ) conditioner_0  (
        //System signals
        .clk(clk),
        .rst_n(rst_n),

        //Handshake signals
        .oht_valid_i(oht_cond_valid),
        .oht_ready_o(oht_cond_ready),

        .drbg_ready_i(cond_drbg_ready || cond_triv_ready),
        .drbg_valid_o(cond_drbg_valid),

        .rdseed_ready_i(cond_output_ready),
        .rdseed_valid_o(cond_output_valid),

        //Data ports
        .key_i(key),
        .message_i(message),
        .seed_o(seed),

        //Debug control signals and data ports
        .debug(debug), // Change this toc onditioner_debug??
        .serial_input(CTD_debug_input),
        .debug_register(curr_state[7:0])
    );

    logic triv_gen;
    logic [7:0] triv_out;
    //Instantiate Trivium:
    trivium_top tri_state ( // NEEDS trivium_debug
        .clk(clk),
        .rst(~rst_n),

        .cond_in(seed),
        .cond_valid(cond_drbg_valid),

        .seed_req(cond_triv_ready),
        .triv_ready(triv_gen),
        .rrand_out(triv_out)
    );

    // //Instantiate the DRBG w/ wrapper
    // ctr_drbg_wrapper #( // needs drbg_debug
    //     .KEY_BITS (128),
    //     .DATA_WIDTH (256),
    //     .RESEED_INTERVAL (511)
    // ) u_drbg_rappin (
    //     .clk                 (clk),
    //     .rst_n               (rst_n),

    //     // conditioner handshake
    //     .drbg_ready_o        (cond_drbg_ready),        // -> conditioner
    //     .drbg_valid_i        (cond_drbg_valid),        // <- conditioner
    //     .seed_i              (seed),                   // <- conditioner 

    //     // commands froM control
    //     .instantiate_i       (drbg_instantiate),
    //     .reseed_i            (drbg_reseed),
    //     .generate_i          (drbg_generate),
    //     .num_blocks_i        (16'd511),

    //     // random output blocks streamin out
    //     .random_valid_o      (drbg_random_valid),
    //     .random_block_o      (drbg_random_block)
    //     // .busy_o(),       // drbg not idle
    //     // .buffer_ready() // from output buffer
    // );
    

    ctr_drbg_wrapper #(
        .KEY_BITS (128),
        .SEED_WIDTH (256),
        .RESEED_INTERVAL (511)
    ) u_drbg_rappin(
        .clk                 (clk),
        .rst_n               (rst_n),

        // conditioner handshake
        .drbg_ready_o        (cond_drbg_ready),        // -> conditioner
        .drbg_valid_i        (cond_drbg_valid),        // <- conditioner
        .seed_i              (seed),                   // <- conditioner 


      // Streaming output to buffer ready/valid   
      .out_valid_o(drbg_random_valid), // drive buffer valid
      .out_ready_i(drbg_output_ready), // buffer ready
      .out_data_o(drbg_random_block), //128b data into buffer

      // unconnected shit
      .busy_o(),        
      .blocks_since_reseed_o()
    );

    // Instantiate the output buffer
    output_buffer #(
        .OUTPUT_WIDTH(OUTPUT_WIDTH),
        .DATA_LENGTH(256),
        .RDSEED_QUEUE_LENGTH(8)
    ) output_buffer_inst (
        .clk(clk),
        .rst_n(rst_n),

        .seed_valid_i(cond_output_valid),
        .seed_port_i(seed),
        .seed_ready_o(cond_output_ready),

        .rand_valid_i(drbg_random_valid),
        .rand_port_i(drbg_random_block),
        .rand_ready_o(drbg_output_ready),

        .rand_req(rand_req),
        .rand_req_type(rand_req_type),
        .rand_byte(rand_byte),
        .rand_valid(rand_valid)
    );


endmodule