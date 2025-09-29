// //======================================================================
// // Top-Level Module
// //
// // Description:
// // This module serves as the top-level wrapper, instantiating and
// // connecting the main control block and the data path multiplexers.
// //
// // Instantiates:
// // - control (includes spi and registers)
// // - entropy_oht_mux
// // - oht_sram_mux
// //======================================================================
// module top (
//     // PHYSICAL PINS

    
//     input logic ic_clk,     // Clock from clock gen IC
//     input logic rst_n,    // Reset (active low)

//     //CPU I/O
//     input rd_seed; // Request random seed
//     input rd_int;  // Request random int
//     output rand;

//     // SPI Pins
//     input logic ss_n,     // Slave Select (active low)
//     input logic debug_clk, // Debug clock from FPGA
//     input logic mosi,     // Master Out Slave In
//     output logic miso,      // Master In Slave Out

//     input logic debug,      // Debug pin (active high)
//     // Serial I/O for debug
//     output logic output_pin_2,
//     output logic output_pin_1,
//     input logic input_pin_1,

// );

    
//     //------------------------------------------------------------------
//     // Module Instantiations
//     //------------------------------------------------------------------

//     // Control logic block
//     // Generates select signals for the data path multiplexers.

//     // Wires to connect control to other modules
//     logic        clk;
//     logic        latch_entropy_mux_out; // Serial debug output from selected latch entropy source
//     logic        jitter_entropy_mux_out; // Serial debug output from selected latch entropy source
//     logic [15:0] entropy_calibration; // Entropy calibration value for debug
//     logic        latch_oht_mux_out; // Serial debug output from selected latch OHT
//     logic        jitter_oht_mux_out; // Serial debug output from selected jitter OHT
//     logic        latch_oht_mux_in; // Serial debug input to selected latch OHT
//     logic        jitter_oht_mux_in; // Serial debug input to selected jitter OHT
//     logic [8:0]  calibration_step; // Calibration step size to use
//     logic        latch_sram_mux_out; // Serial debug output from selected latch SRAM address
//     logic        jitter_sram_mux_out; // Serial debug output from selected jitter SRAM address
//     logic        latch_sram_mux_in; // Serial debug input to selected latch SRAM address
//     logic        jitter_sram_mux_in; // Serial debug input to selected jitter SRAM address
//     logic        conditioner_mux_output;  // Serial debug output from selected conditioner
//     logic        conditioner_mux_input; // Serial debug input to selected conditioner
//     logic        DRBG_mux_output; // Serial debug output from selected DRBG
//     logic        DRBG_mux_input;  // Serial debug input to selected DRBG
//     logic [13:0] temp_counter_0, temp_counter_1, temp_counter_2, temp_counter_3; // Counters for temp sensors, verify w Anthony
//     logic [13:0] temp_threshold_0, temp_threshold_1, temp_threshold_2, temp_threshold_3; // Thresholds for temp sensors
//     logic        temp_sense_0_good, temp_sense_1_good, temp_sense_2_good, temp_sense_3_good; // Single bit boolean good/bad for temp sensor
//     logic [24:0] curr_state; // Contains all the info for 

//     // Instantiate the control module
//     control u_control (
//         .ic_clk(ic_clk),
//         .debug_clk(debug_clk),
//         .rst_n(rst_n),
//         .mosi(mosi),
//         .ss_n(ss_n),
//         .debug(debug),
//         .input_pin_1(input_pin_1),
//         .miso(miso),
//         .output_pin_2(output_pin_2),
//         .output_pin_1(output_pin_1),
//         .clk(clk), // This is the new system clock (muxed between ic_clk and debug_clk pins)
//         .latch_entropy_mux_out(latch_entropy_mux_out), // Serial output from selected latch entropy source
//         .jitter_entropy_mux_out(jitter_entropy_mux_out), // Serial debug output from selected latch entropy source
//         .entropy_calibration(entropy_calibration), // Entropy calibration value for debug
//         .latch_oht_mux_out(latch_oht_mux_out),  // Serial debug output from selected latch OHT
//         .jitter_oht_mux_out(jitter_oht_mux_out), // Serial debug output from selected jitter OHT
//         .latch_oht_mux_in(latch_oht_mux_in),  // Serial debug input to selected latch OHT
//         .jitter_oht_mux_in(jitter_oht_mux_in),  // Serial debug input to selected jitter OHT
//         .calibration_step(calibration_step),  // Calibration step size to use
//         .latch_sram_mux_out(latch_sram_mux_out), // Serial debug output from selected latch SRAM address
//         .jitter_sram_mux_out(jitter_sram_mux_out),  // Serial debug output from selected jitter SRAM address
//         .latch_sram_mux_in(latch_sram_mux_in), // Serial debug input to selected latch SRAM address
//         .jitter_sram_mux_in(jitter_sram_mux_in),  // Serial debug input to selected jitter SRAM address
//         .conditioner_mux_output(conditioner_mux_output),  // Serial debug output from selected conditioner
//         .conditioner_mux_input(conditioner_mux_input), // Serial debug input to selected conditioner
//         .DRBG_mux_output(DRBG_mux_output),  // Serial debug output from selected DRBG
//         .DRBG_mux_input(DRBG_mux_input), // Serial debug input to selected DRBG
//         .temp_counter_0(temp_counter_0),  // Counters for temp sensors
//         .temp_counter_1(temp_counter_1),
//         .temp_counter_2(temp_counter_2),
//         .temp_counter_3(temp_counter_3),
//         .temp_threshold_0(temp_threshold_0),  // Thresholds for temp sensors
//         .temp_threshold_1(temp_threshold_1),
//         .temp_threshold_2(temp_threshold_2),
//         .temp_threshold_3(temp_threshold_3),
//         .temp_sense_0_good(temp_sense_0_good), // Single bit boolean good/bad for temp sensor
//         .temp_sense_1_good(temp_sense_1_good),
//         .temp_sense_2_good(temp_sense_2_good),
//         .temp_sense_3_good(temp_sense_3_good),
//         .curr_state(curr_state)
//     );

//     // Mux between Latch Entropy Sources and Latch OHT
//     logic [5:0] output_select_latch_entropy_oht;
//     logic [5:0] input_select_latch_entropy_oht;
//     always_comb begin
//         if (curr_state[23:21] == 3'd1) output_select_latch_entropy_oht = {1'b1, curr_state[20:16]};

//         else if (curr_state[15:13] == 3'd1) output_select_latch_entropy_oht = {1'b1, curr_state[12:8]};
 
//         else output_select_latch_entropy_oht = 6'b0; // Default value when neither condition is true

//         if (curr_state[7:5]==3'd1) input_select_latch_entropy_oht = {1'b1, curr_state[4:0]}
//         else input_select_latch_entropy_oht=6'b0;

//     end
//     entropy_oht_mux latch_entropy_oht_mux (
//         .debug               (debug),
//         .entropy_sources_out (latch_entropy_sources_out),
//         .oht_mux_in          (latch_oht_mux_in),        // Serial input to selected latch OHT for debug
//         .output_select       (output_select_latch_entropy_oht),          // Select signals for the LATCH module
//         .input_select        (input_select_latch_entropy_oht),           // Select signals for the LATCH module
//         .entropy_mux_out     (latch_entropy_mux_out),           // Serial output from selected latch entropy source for debug
//         .oht_in              (latch_oht_default_in)              // Input pins to Latch OHT (32 bits)
//     );


//     logic [5:0] output_select_jitter_entropy_oht;
//     logic [5:0] input_select_jitter_entropy_oht;
//     always_comb begin
//         if (curr_state[23:21] == 3'd2) output_select_jitter_entropy_oht = {1'b1, curr_state[20:16]};

//         else if (curr_state[15:13] == 3'd2) output_select_jitter_entropy_oht = {1'b1, curr_state[12:8]};
 
//         else output_select_jitter_entropy_oht = 6'b0; // Default value when neither condition is true

//         if (curr_state[7:5]==3'd2) input_select_jitter_entropy_oht = {1'b1, curr_state[4:0]}
//         else input_select_jitter_entropy_oht=6'b0;

//     end
//     // Mux between Jitter Entropy Sources and Jitter OHT
//     entropy_oht_mux jitter_entropy_oht_mux (
//         .debug               (debug),
//         .entropy_sources_out (jitter_entropy_sources_out),
//         .oht_mux_in          (jitter_oht_mux_in),
//         .output_select       (output_select_jitter_entropy_oht),          // Select signals for the JITTER module
//         .input_select        (input_select_jitter_entropy_oht),           // Select signals for the JITTER module
//         .entropy_mux_out     (jitter_entropy_mux_out),
//         .oht_in              (jitter_oht_default_in)             // Input pins to Jitter OHT
//     );


//     logic [5:0] output_select_latch_oht_sram;
//     logic [5:0] input_select_latch_oht_sram;
//     always_comb begin
//         if (curr_state[23:21] == 3'd3) output_select_latch_oht_sram = {1'b1, curr_state[20:16]};

//         else if (curr_state[15:13] == 3'd3) output_select_latch_oht_sram = {1'b1, curr_state[12:8]};
 
//         else output_select_latch_oht_sram = 6'b0; // Default value when neither condition is true

//         if (curr_state[7:5]==3'd3) input_select_latch_oht_sram = {1'b1, curr_state[4:0]}
//         else input_select_latch_oht_sram=6'b0;
//     end
    
//     // Mux between latch OHTs and SRAM
//     oht_sram_mux latch_oht_sram_mux (
//         .debug          (debug),
//         .oht_outputs    (latch_oht_default_out),
//         .sram_mux_in    (latch_sram_mux_in),
//         .output_select  (output_select_latch_oht_sram), //Cell select plus extra high bit for module select
//         .input_select   (input_select_latch_oht_sram), //Cell select plus extra high bit for module select
//         .oht_mux_out    (latch_oht_mux_out),
//         .sram_in        (latch_sram_default_in) // Latch SRAM input
//     );

//     logic [5:0] output_select_jitter_oht_sram;
//     logic [5:0] input_select_jitter_oht_sram;
//     always_comb begin
//         if (curr_state[23:21] == 3'd4) output_select_jitter_oht_sram = {1'b1, curr_state[20:16]};

//         else if (curr_state[15:13] == 3'd4) output_select_jitter_oht_sram = {1'b1, curr_state[12:8]};
 
//         else output_select_jitter_oht_sram = 6'b0; // Default value when neither condition is true

//         if (curr_state[7:5]==3'd4) input_select_jitter_oht_sram = {1'b1, curr_state[4:0]}
//         else input_select_jitter_oht_sram=6'b0;
//     end

//     // Mux between jitter OHTs and SRAM
//     oht_sram_mux jitter_oht_sram_mux (
//         .debug          (debug),
//         .oht_outputs    (jitter_oht_default_out),
//         .sram_mux_in    (jitter_sram_mux_in),
//         .output_select  (output_select_jitter_oht_sram), //Cell select plus extra high bit for module select
//         .input_select   (input_select_jitter_oht_sram), //Cell select plus extra high bit for module select
//         .oht_mux_out    (jitter_oht_mux_out),
//         .sram_in        (jitter_sram_default_in) // Jitter SRAM input
//     );

// endmodule