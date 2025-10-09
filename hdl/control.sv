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
    input logic output_to_input_direct, // If this pin is high, connect output 1 to input 1 internally.
    output logic spi_data_ready,

    // INTERNAL CLOCK CONNECTION  
    output logic clk, // This is muxed between ic_clk and debug_clk
    
    // ENTROPY SOURCE CONNECTIONS
    input logic latch_entropy_mux_out, // Direct connection to latch entropy output. Index of entropy source detemined by cell select bits
    input logic jitter_entropy_mux_out, // Direct connection to jitter entropy output. Index of entropy source detemined by cell select bits

    output logic [15:0] entropy_calibration, //Upper 8 are CAL_N, lower 8 are CAL_P

    // OHT CONNECTIONS
    output logic latch_oht_mux_in, // Latch OHT Mux input
    output logic jitter_oht_mux_in, // Jitter OHT Mux input

    // AES CBC MAC, TRIVIUM, DRBG CONNECTIONS
    output logic CTD_debug_input, // Input to MUX into the conditioner, trivium, DRBG

    // TEMPERATURE SENSOR CONNECTIONS (this might change depending on Anthony's counter implementation)
    input logic [13:0] temp_counter_0, // Temp sensor 0 counter 
    input logic [13:0] temp_counter_1, // Temp sensor 1 counter 
    input logic [13:0] temp_counter_2, // Temp sensor 2 counter 
    input logic [13:0] temp_counter_3, // Temp sensor 3 counter 
   
    output logic [13:0] temp_threshold_0, // Temp sensor 0 threshold 
    output logic [13:0] temp_threshold_1, // Temp sensor 1 threshold
    output logic [13:0] temp_threshold_2, // Temp sensor 2 threshold
    output logic [13:0] temp_threshold_3,  // Temp sensor 3 threshold

    input logic temp_sense_0_good, // States of temp sensors (good/bad)
    input logic temp_sense_1_good,
    input logic temp_sense_2_good,
    input logic temp_sense_3_good,

    input logic [15:0] lower_latch_entropy_good, // States of entropy sources (good/bad)
    input logic [15:0] upper_latch_entropy_good,
    input logic [15:0] lower_jitter_entropy_good,
    input logic [15:0] upper_jitter_entropy_good,

    output logic [21:0] curr_state
);

    logic [21:0] next_state; // Internally track next state

    // ------------------ Registers ------------------

    // State constants
    localparam [21:0] DEFAULT_STATE = 22'b 00_0000_0000_0000_0000_0000; // Output pin 2 is clk, output pin 1 is VCC. Maybe idk yet
    localparam [21:0] HALT_STATE    = 22'hED_BEF; // We just don't want to output anything

    logic [21:0] debug_state; //0x02

    logic [15:0] internal_entropy_calibration;

    logic [13:0] internal_temp_threshold_0;// Temp sensor 0 threshold, 0x05
    logic [13:0] internal_temp_threshold_1;// Temp sensor 1 threshold, 0x06
    logic [13:0] internal_temp_threshold_2;// Temp sensor 2 threshold, 0x07
    logic [13:0] internal_temp_threshold_3;// Temp sensor 3 threshold, 0x08

    logic [13:0] internal_temp_counter_0; // Temp sensor 0 counter, 0x09
    logic [13:0] internal_temp_counter_1; // Temp sensor 1 counter, 0x0A
    logic [13:0] internal_temp_counter_2; // Temp sensor 2 counter, 0x0B
    logic [13:0] internal_temp_counter_3; // Temp sensor 3 counter, 0x0C

    logic [15:0] internal_lower_latch_entropy_good;
    logic [15:0] internal_upper_latch_entropy_good;
    logic [15:0] internal_lower_jitter_entropy_good;
    logic [15:0] internal_upper_jitter_entropy_good;
    

    // This signal is muxed between input_pin_1 and output_pin_2
    logic input_bypass_mux_out;

    // Debug state
    logic write_debug_state;
    logic [21:0] new_debug_state_value;

    // SPI stuff
    logic [21:0] data_to_send;
    logic send_trigger;
    logic [21:0] spi_data;

    // Instantiate SPI module
    spi spi_inst (
        .sclk(clk),
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

    always_ff @(posedge clk) begin : internal_register_update
        internal_temp_counter_0 <= temp_counter_0; // Update internal temp counter
        internal_temp_counter_1 <= temp_counter_1; // Update internal temp counter
        internal_temp_counter_2 <= temp_counter_2; // Update internal temp counter
        internal_temp_counter_3 <= temp_counter_3; // Update internal temp counter

        internal_lower_latch_entropy_good <= lower_latch_entropy_good; // Update entropy source status
        internal_upper_latch_entropy_good <= upper_latch_entropy_good; // Update entropy source status
        internal_lower_jitter_entropy_good <= lower_jitter_entropy_good; // Update entropy source status
        internal_upper_jitter_entropy_good <= upper_jitter_entropy_good; // Update entropy source status
    end 

    // Broadcast values from registers
    always_comb begin
        entropy_calibration = internal_entropy_calibration;

        temp_threshold_0 = internal_temp_threshold_0;
        temp_threshold_1 = internal_temp_threshold_1;
        temp_threshold_2 = internal_temp_threshold_2;
        temp_threshold_3 = internal_temp_threshold_3;

    end

    // Clock Mux
    assign clk = debug ? debug_clk : ic_clk;

    // State comb
    always_comb begin : state_logic
        if (!temp_sense_0_good || !temp_sense_1_good || !temp_sense_2_good || !temp_sense_3_good)
            next_state = HALT_STATE;
        else if (debug && write_debug_state)
            next_state = new_debug_state_value;
        else
            next_state = curr_state;
    end
    
    always_ff @(posedge clk) begin  //Mostly everything
        if (!rst_n) begin
            curr_state <= DEFAULT_STATE;
            internal_entropy_calibration <= 16'b1100_0000_1100_0000;
            internal_temp_threshold_0 <= 14'b0;
            internal_temp_threshold_1 <= 14'b0;
            internal_temp_threshold_2 <= 14'b0;
            internal_temp_threshold_3 <= 14'b0;
            data_to_send <= 21'h0;
            write_debug_state <= 1'b0;
            new_debug_state_value <= 21'b0;
            send_trigger <= 1'b0;

        end
        else begin
            curr_state <= next_state;
            send_trigger <= 1'b0;

            if (spi_data_ready && debug) begin
                // Bit 21: 1=Register Operation (Read/Write), 0=Mux Select Operation
                if (spi_data[21]) begin 
                    write_debug_state <= 1'b0;
                    // Bit 20: 1=Read Operation, 0=Write Operation
                    if (spi_data[20]) begin // Read operation 
                        case (spi_data[19:16]) // Register Address
                            4'h0: data_to_send <= {1'b0, DEFAULT_STATE}; // Default state
                            4'h1: data_to_send <= {1'b0, HALT_STATE};    // Halt state
                            4'h2: data_to_send <= {1'b0, debug_state};   // Debug State

                            4'h3: data_to_send <= {9'h0, internal_lower_latch_entropy_good}; // Entropy Status Latch [0:15]
                            4'h4: data_to_send <= {9'h0, internal_upper_latch_entropy_good}; // Entropy Status Latch [16:31]
                            4'h5: data_to_send <= {9'h0, internal_lower_jitter_entropy_good}; // Entropy Status Jitter [0:15]
                            4'h6: data_to_send <= {9'h0, internal_upper_jitter_entropy_good}; // Entropy Status Latch [16:31]

                            4'h7: data_to_send <= {8'h0, internal_entropy_calibration}; // Calibration bits for latch

                            4'h8: data_to_send <= {10'h0, internal_temp_threshold_0}; // Temp threshold 0
                            4'h9: data_to_send <= {10'h0, internal_temp_threshold_1}; // Temp threshold 1
                            4'hA: data_to_send <= {10'h0, internal_temp_threshold_2}; // Temp threshold 2
                            4'hB: data_to_send <= {10'h0, internal_temp_threshold_3}; // Temp threshold 3

                            4'hC: data_to_send <= {10'h0, internal_temp_counter_0}; // Temp sensor 0 counter (read-only)
                            4'hD: data_to_send <= {10'h0, internal_temp_counter_1}; // Temp sensor 1 counter (read-only)
                            4'hE: data_to_send <= {10'h0, internal_temp_counter_2}; // Temp sensor 2 counter (read-only)
                            4'hF: data_to_send <= {10'h0, internal_temp_counter_3}; // Temp sensor 3 counter (read-only)
            
                            default: data_to_send <= 22'hED_BEF; // Invalid Address
                        endcase
                        send_trigger <= 1'b1;
                    end
                      
                    else begin // Write operation
                        case (spi_data[19:16]) // Register Address                // This is a synchronous write since it affects the main FSM, but we treat it as an immediate update
                    // The main state machine will select debug_state on the next clock edge if 'debug' is high.
                            4'h7: internal_entropy_calibration <= spi_data[15:0]; // Calibration bits for latch, 0x04
                            4'h8: internal_temp_threshold_0 <= spi_data[13:0]; // Temp sensor 0 threshold, 0x05
                            4'h9: internal_temp_threshold_1 <= spi_data[13:0]; // Temp sensor 1 threshold, 0x06
                            4'hA: internal_temp_threshold_2 <= spi_data[13:0]; // Temp sensor 2 threshold, 0x07
                            4'hB: internal_temp_threshold_3 <= spi_data[13:0]; // Temp sensor 3 threshold, 0x08 
                            // Other registers (0,1,2,3,4,5,6,C,D,E,F) are read-only or set by other logic
                            default: begin end // Ignore write to invalid/read-only address
                        endcase
                    end
                end
                
                else begin // Mux Select Operation (Set Debug State)
                    write_debug_state <= 1'b1;
                    new_debug_state_value <= spi_data[21:0];
                end
            end
        end
    end
   



    // --- Output Pin Muxes ---

    // Output Pin 2 Mux (Combinational)
    always_comb begin : output_pin_2_mux

        if (debug) begin
            output_pin_2 = 1'b0; // Default value (Low)

            case (curr_state[20:19]) // Module Select (M)
                2'b00: begin // M=0: Fixed Signals & Status
                    case (curr_state[18:14]) // Cell Select (C)
                        5'd0: output_pin_2 = 1'b1;
                        5'd1: output_pin_2 = clk;
                        5'd2: output_pin_2 = temp_sense_0_good;
                        5'd3: output_pin_2 = temp_sense_1_good;
                        5'd4: output_pin_2 = temp_sense_2_good;
                        5'd5: output_pin_2 = temp_sense_3_good;
                        default: output_pin_2 = 1'b0; 
                    endcase
                end
                2'b01: output_pin_2 = latch_entropy_mux_out;   // M=1: Latch Entropy MUX Output
                2'b10: output_pin_2 = jitter_entropy_mux_out;  // M=2: Jitter Entropy MUX Output
                default: output_pin_2 = 1'b0;
            endcase
        end
        else output_pin_2 = 1'b0;
    end

    // Output Pin 1 Mux (Combinational)
    always_comb begin : output_pin_1_mux
        if (debug) begin
            output_pin_1 = 1'b0; // Default value (Low)

            case (curr_state[13:12]) // Module Select (M)
                2'b00: begin // M=0: Fixed Signals & Status
                    case (curr_state[11:7]) // Cell Select (C)
                        5'd0: output_pin_1 = 1'b1;
                        5'd1: output_pin_1 = clk;
                        5'd2: output_pin_1 = temp_sense_0_good;
                        5'd3: output_pin_1 = temp_sense_1_good;
                        5'd4: output_pin_1 = temp_sense_2_good;
                        5'd5: output_pin_1 = temp_sense_3_good;
                        default: output_pin_1 = 1'b0; 
                    endcase
                end
                2'b01: output_pin_1 = latch_entropy_mux_out;  // M=1: Latch Entropy MUX Output
                2'b10: output_pin_1 = jitter_entropy_mux_out; // M=2: Jitter Entropy MUX Output
                default: output_pin_1 = 1'b0;
            endcase
        end
        else output_pin_1 = 1'b0;
    end

    // This selects whether we are bypassing a module i.e. use another module's output as input to one further down the datapath
    // input_bypass_mux_out will be muxed to the module select mux
    always_comb begin: input_bypass_mux
        if (output_to_input_direct)
            input_bypass_mux_out = output_pin_2;
        else
            input_bypass_mux_out = input_pin_1;
    end
    
    // 
    always_comb begin: input_mux
        // This is the input wires to the latch cell select mux
        latch_oht_mux_in = 1'b0;
        
        // This is the input wires to the jitter cell select mux
        jitter_oht_mux_in = 1'b0;

        // This is the input to the buffer for conditioner, DRBG, Trivium
        CTD_debug_input = 1'b0;

        if (debug) begin
            case (curr_state[6:5])

                2'b01: latch_oht_mux_in = input_bypass_mux_out;
                2'b10: jitter_oht_mux_in = input_bypass_mux_out;
                2'b11: begin
                    case (curr_state[4:0])
                        5'b00000: CTD_debug_input = input_bypass_mux_out;
                        default: ; // do nothing
                    endcase
                end

                default: ; // do nothing
            endcase
        end
    end

endmodule
