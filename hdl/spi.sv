module spi 
(
    // System Interface
    input  logic sclk,
    input  logic rst_n,
    input  logic [24:0] data_to_send, // Data to load for the *next* transmission
    input  logic send_trigger,           // Pulse to load data_to_send

    // SPI Bus Interface
    input  logic mosi,                   // Master Out, Slave In
    input  logic ss_n,                   // Slave Select (active low)
    output logic miso,                   // Master In, Slave Out
    
    // Data Output Interface
    output logic [24:0] data, // Data received from the master
    output logic data_ready              // Pulsed high for one clock when data is ready
);


    // State machine definition
    typedef enum logic [1:0] {
        IDLE,
        TRANSMIT
    } spi_state_t;

    // Internal registers and signals
    spi_state_t curr_state, next_state;
    logic [4:0] bit_cnt; // Need to count to 25 (5 bits)
    logic [24:0]    rx_shifter; // Shift register for received data
    logic [24:0]    tx_shifter; // Shift register for data to transmit

    // FSM state transition logic (sequential)
    // This process updates the current state on the rising edge of the SPI clock.
    always_ff @(posedge sclk or negedge rst_n) begin
        if (!rst_n)
            curr_state <= IDLE;
        else
            curr_state <= next_state;
    end

    // FSM next-state logic (combinational)
    // This process determines the next state based on the current state and inputs.
    always_comb begin
        next_state = curr_state; // Default to stay in the current state
        case (curr_state)
            IDLE: begin
                // When the master selects this slave, begin transmission
                if (!ss_n) begin
                    next_state = TRANSMIT;
                end
                miso = 1'b0;
            end
            TRANSMIT: begin
                // The transaction ends when all bits are transferred OR
                // if the master deselects the slave prematurely.
                miso = tx_shifter[24];
                if (bit_cnt == 5'd24 || ss_n) begin
                    next_state = IDLE;
                end
            end
        endcase
    end

    // Data path and output logic (sequential)
    always_ff @(posedge sclk or negedge rst_n) begin
        if (!rst_n) begin
            bit_cnt <= '0;
            rx_shifter <= '0;
            tx_shifter <= '0;
            data <= '0;
            data_ready <= 1'b0;
        end else begin
            // By default, data_ready is a single-cycle pulse
            data_ready <= 1'b0;

            case (curr_state)
                IDLE: begin
                    // If triggered, load the data that will be sent on the next transaction
                    if (send_trigger) begin
                        tx_shifter <= data_to_send;
                    end
                    // When a new transaction starts, reset the bit counter
                    if (next_state == TRANSMIT) begin
                        bit_cnt <= '0;
                    end
                end

                TRANSMIT: begin
                    if (!ss_n) begin
                        bit_cnt <= bit_cnt + 1;
                        // Shift in data from the master on MOSI
                        rx_shifter <= {rx_shifter[23:0], mosi};
                        // Shift out data to the master on MISO
                        tx_shifter <= {tx_shifter[23:0], 1'b0};
                    end

                    // If the transaction is finishing on this clock cycle...
                    if (bit_cnt == 5'd24) begin
                        data_ready <= 1'b1; // Pulse data_ready
                        // Latch the final received word (including the last incoming bit)
                        data <= {rx_shifter[23:0], mosi}; 
                    end
                end
            endcase
        end
    end

endmodule