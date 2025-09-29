module control (
    // PHYSICAL PINS (will be pass through in top.sv)
    input logic ic_clk,     // Clock from clock gen IC
    input logic debug_clk, // Debug clock from FPGA
    input logic rst_n,    // Reset (active low)
    input logic mosi,     // Master Out Slave In
    input logic ss_n,     // Slave Select (active low)
    input logic debug,      // Debug pin

    output logic miso,      // Master In Slave Out
    output logic output_pin_2,
    output logic output_pin_1,
    input logic input_pin_1,

    //  ------------- NEED THE IO WITH CPU -----------------

    // INTERNAL CLOCK CONNECTION  
    output logic clk, // This is muxed between ic_clk and debug_clk

    // ENTROPY SOURCE CONNECTIONS
    input logic latch_entropy_mux_out, // Direct connection to latch entropy output. Index of entropy source detemined by cell select bits
    input logic jitter_entropy_mux_out, // Direct connection to jitter entropy output. Index of entropy source detemined by cell select bits

    output logic [15:0] entropy_calibration, //Upper 8 are CAL_N, lower 8 are CAL_P

    // OHT CONNECTIONS
    input logic latch_oht_mux_out, // Latch OHT MUX output
    input logic jitter_oht_mux_out, // Jitter OHT MUX output

    output logic latch_oht_mux_in, // Latch OHT Mux input
    output logic jitter_oht_mux_in, // Jitter OHT Mux input

    output logic [8:0] calibration_step, // This is the % per LSB value


    // SRAM CONNECTIONS
    input logic latch_sram_mux_out, // Latch SRAM output
    input logic jitter_sram_mux_out, // Jitter SRAM output
    
    output logic latch_sram_mux_in, // Input to Latch SRAM
    output logic jitter_sram_mux_in, // Input to Jitter SRAM

    // AES CBC MAC CONNECTIONS
    input conditioner_mux_output, // Output of the conditioner MUX
    output conditioner_mux_input, // Input to MUX into the conditioner

    // DRBG CONNECTIONS
    input DRBG_mux_output, // Output of DRBG
    output DRBG_mux_input, // Input to DRBG

    // TEMPERATURE SENSOR CONNECTIONS (this might change depending on Anthony's counter implementation)
    input logic [13:0] temp_counter_0, // Temp sensor 0 counter 
    input logic [13:0] temp_counter_1, // Temp sensor 1 counter 
    input logic [13:0] temp_counter_2, // Temp sensor 2 counter 
    input logic [13:0] temp_counter_3, // Temp sensor 3 counter 
   
    output logic [13:0] temp_threshold_0, // Temp sensor 0 threshold 
    output logic [13:0] temp_threshold_1, // Temp sensor 1 threshold
    output logic [13:0] temp_threshold_2, // Temp sensor 2 threshold
    output logic [13:0] temp_threshold_3,  // Temp sensor 3 threshold

    input logic temp_sense_0_good,
    input logic temp_sense_1_good,
    input logic temp_sense_2_good,
    input logic temp_sense_3_good,

    output logic [23:0] curr_state,
    output logic        spi_data_ready


);

    logic [24:0] next_state; // Internally track next state

    // ------------------ Registers ------------------

    // State constants
    localparam [23:0] DEFAULT_STATE = 24'b 0000_0001_0000_0000_0000_0000; // Output pin 2 is clk, output pin 1 is VCC. Maybe idk yet
    localparam [23:0] HALT_STATE    = 24'd1; // We just don't want to output anything


    logic [23:0] debug_state; //0x02

    logic [7:0]  internal_calibration_step;
    logic [15:0] internal_entropy_calibration;

    logic [13:0] internal_temp_threshold_0;// Temp sensor 0 threshold, 0x05
    logic [13:0] internal_temp_threshold_1;// Temp sensor 1 threshold, 0x06
    logic [13:0] internal_temp_threshold_2;// Temp sensor 2 threshold, 0x07
    logic [13:0] internal_temp_threshold_3;// Temp sensor 3 threshold, 0x08

    logic [13:0] internal_temp_counter_0; // Temp sensor 0 counter, 0x09
    logic [13:0] internal_temp_counter_1; // Temp sensor 1 counter, 0x0A
    logic [13:0] internal_temp_counter_2; // Temp sensor 2 counter, 0x0B
    logic [13:0] internal_temp_counter_3; // Temp sensor 3 counter, 0x0C
    
    // Temp counters are read-only, so update them asynchronously
    always_comb begin
        internal_temp_counter_0 = temp_counter_0;
        internal_temp_counter_1 = temp_counter_1;
        internal_temp_counter_2 = temp_counter_2;
        internal_temp_counter_3 = temp_counter_3;
    end

    // SPI stuff
    logic [24:0] data_to_send;
    logic send_trigger;
    logic [24:0] spi_data;
    logic send_trigger;

    // Instantiate SPI module
    spi spi_inst (
        .sclk(debug_clk),
        .rst_n(rst_n),
        .data_to_send(data_to_send),
        .send_trigger(send_trigger),

        .mosi(mosi),
        .ss_n(ss_n),
        .miso(miso),

        .data(spi_data),
        .data_ready(spi_data_ready)
    );

    // ---------------------------------------------------------


    // SPI Data Processing - Combinational Logic
    always_comb begin : spi_data_processing
        // Default to no action unless data is ready
        send_trigger = 1'b0;
        data_to_send = 25'h0;

        if (spi_data_ready) begin
            // Bit 25: 1=Register Operation (Read/Write), 0=Mux Select Operation
            if (spi_data[24]) begin 
                // Bit 24: 1=Read Operation, 0=Write Operation
                if (spi_data[23]) begin // Read operation 
                    send_trigger = 1'b1; // Flag to send data back
                    case (spi_data[22:19]) // Register Address
                        4'h0: data_to_send = {1'b0, DEFAULT_STATE}; // Default state
                        4'h1: data_to_send = {1'b0, HALT_STATE};    // Halt state
                        4'h2: data_to_send = {1'b0, debug_state};   // Debug State
                        4'h3: data_to_send = {15'h0, internal_calibration_step}; // Calibration step size
                        4'h4: data_to_send = {8'h0, internal_entropy_calibration}; // Calibration bits for latch
                        4'h5: data_to_send = {10'h0, internal_temp_threshold_0}; // Temp threshold 0
                        4'h6: data_to_send = {10'h0, internal_temp_threshold_1}; // Temp threshold 1
                        4'h7: data_to_send = {10'h0, internal_temp_threshold_2}; // Temp threshold 2
                        4'h8: data_to_send = {10'h0, internal_temp_threshold_3}; // Temp threshold 3
                        4'h9: data_to_send = {10'h0, internal_temp_counter_0}; // Temp sensor 0 counter (read-only)
                        4'hA: data_to_send = {10'h0, internal_temp_counter_1}; // Temp sensor 1 counter (read-only)
                        4'hB: data_to_send = {10'h0, internal_temp_counter_2}; // Temp sensor 2 counter (read-only)
                        4'hC: data_to_send = {10'h0, internal_temp_counter_3}; // Temp sensor 3 counter (read-only)
                        default: data_to_send = 25'hDED_BEF; // Invalid Address
                    endcase
                end
                
                else begin // Write operation
                    case (spi_data[22:19]) // Register Address                // This is a synchronous write since it affects the main FSM, but we treat it as an immediate update
                // The main state machine will select debug_state on the next clock edge if 'debug' is high.
                        4'h3: internal_calibration_step = spi_data[8:0];  // Calibration step size, 0x03
                        4'h4: internal_entropy_calibration = spi_data[15:0]; // Calibration bits for latch, 0x04
                        4'h5: internal_temp_threshold_0 = spi_data[13:0]; // Temp sensor 0 threshold, 0x05
                        4'h6: internal_temp_threshold_1 = spi_data[13:0]; // Temp sensor 1 threshold, 0x06
                        4'h7: internal_temp_threshold_2 = spi_data[13:0]; // Temp sensor 2 threshold, 0x07
                        4'h8: internal_temp_threshold_3 = spi_data[13:0]; // Temp sensor 3 threshold, 0x08 
                        // Other registers (0, 1, 2, 9, A, B, C) are read-only or set by other logic
                        default: begin end // Ignore write to invalid/read-only address
                    endcase
                end
            end
            
            else begin // Mux Select Operation (Set Debug State)
                debug_state = spi_data[23:0]; 
            end
        end
    end
   
    // Clock Mux and State Update
    assign clk = debug ? debug_clk : ic_clk;
    always_ff @(posedge clk or negedge rst_n) begin : state_register
        if (!rst_n) begin
            curr_state <= DEFAULT_STATE;
        end else begin
            curr_state <= next_state;
        end
    end


    // --- Output Pin Muxes ---

    // Output Pin 2 Mux (Combinational)
    always_comb begin : output_pin_2_mux
        output_pin_2 = 1'b0; // Default value (Low)

        case (curr_state[23:21]) // Module Select (M)
            3'd0: begin // M=0: Fixed Signals & Status
                case (curr_state[20:16]) // Cell Select (C)
                    5'd0: output_pin_2 = 1'b1;
                    5'd1: output_pin_2 = clk;
                    5'd2: output_pin_2 = conditioner_mux_output;
                    5'd3: output_pin_2 = DRBG_mux_output;
                    5'd4: output_pin_2 = DRBG_mux_output; // Duplicate mapping, kept as-is
                    5'd5: output_pin_2 = temp_sense_0_good;
                    5'd6: output_pin_2 = temp_sense_1_good;
                    5'd7: output_pin_2 = temp_sense_2_good;
                    5'd8: output_pin_2 = temp_sense_3_good;
                    default: output_pin_2 = 1'b0; 
                endcase
            end
            3'd1: output_pin_2 = latch_entropy_mux_out;   // M=1: Latch Entropy MUX Output
            3'd2: output_pin_2 = jitter_entropy_mux_out;  // M=2: Jitter Entropy MUX Output
            3'd3: output_pin_2 = latch_oht_mux_out;       // M=3: Latch OHT MUX Output
            3'd4: output_pin_2 = jitter_oht_mux_out;      // M=4: Jitter OHT MUX Output
            3'd5: output_pin_2 = latch_sram_mux_out;      // M=5: Latch SRAM Output
            3'd6: output_pin_2 = jitter_sram_mux_out;     // M=6: Jitter SRAM Output
            default: output_pin_2 = 1'b0;
        endcase
    end

    // Output Pin 1 Mux (Combinational)
    always_comb begin : output_pin_1_mux
        output_pin_1 = 1'b0; // Default value (Low)

        case (curr_state[15:13]) // Module Select (M)
            3'd0: begin // M=0: Fixed Signals & Status
                case (curr_state[12:8]) // Cell Select (C)
                    5'd0: output_pin_1 = 1'b1;
                    5'd1: output_pin_1 = clk;
                    5'd2: output_pin_1 = conditioner_mux_output;
                    5'd3: output_pin_1 = DRBG_mux_output;
                    5'd4: output_pin_1 = DRBG_mux_output; // Duplicate mapping, kept as-is
                    5'd5: output_pin_1 = temp_sense_0_good;
                    5'd6: output_pin_1 = temp_sense_1_good;
                    5'd7: output_pin_1 = temp_sense_2_good;
                    5'd8: output_pin_1 = temp_sense_3_good;
                    default: output_pin_1 = 1'b0; 
                endcase
            end
            3'd1: output_pin_1 = latch_entropy_mux_out;  // M=1: Latch Entropy MUX Output
            3'd2: output_pin_1 = jitter_entropy_mux_out; // M=2: Jitter Entropy MUX Output
            3'd3: output_pin_1 = latch_oht_mux_out;      // M=3: Latch OHT MUX Output
            3'd4: output_pin_1 = jitter_oht_mux_out;     // M=4: Jitter OHT MUX Output
            3'd5: output_pin_1 = latch_sram_mux_out;     // M=5: Latch OHT SRAM Output
            3'd6: output_pin_1 = jitter_sram_mux_out;    // M=6: Jitter OHT SRAM Output
            default: output_pin_1 = 1'b0;
        endcase
    end
    

    always_comb begin: input_mux
        case (curr_state[7:5])
            // 3'b000: begin
            //     case (curr_state[4:0])
            //         5'd0, 5'd1, 5'd2: begin
            //             case (spi_data)
            //                 5'b00001: input_pin_1 = output_pin_1;
            //                 5'b00010: input_pin_1 = output_pin_2;
            //                 default: ; // no assignment
            //             endcase
            //         end
            //         default: ; // do nothing
            //     endcase
            // end

            3'b001: latch_oht_mux_in = input_pin_1;
            3'b010: jitter_oht_mux_in = input_pin_1;
            3'b011: latch_sram_mux_in = input_pin_1;
            3'b100: jitter_sram_mux_in = input_pin_1;
            // 3'b101: begin
            //     case (curr_state[4:0])
            //         5'b00000: conditioner_mux_input = input_pin_1;
            //         5'b00001: DRBG_mux_input = input_pin_1;
            //         default: ; // do nothing
            //     endcase
            // end

            default: ; // do nothing
        endcase
    end

endmodule
