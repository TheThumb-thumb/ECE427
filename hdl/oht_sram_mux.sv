// This is between OHT and SRAM so we can see the OHT outputs and test SRAM data input
// This will be used twice. Once for the Latch OHT and SRAM and once for the jitter OHT and SRAM

module oht_sram_mux (
    input  logic        debug,

    input  logic [31:0] oht_outputs,   // Coming from entropy sources, normal input
    input  logic        sram_mux_in,   // Serial debug input to test SRAM

    input  logic [23:0]  curr_state,       // Extract select signals from this which entropy source to route to output/input pin

    input  logic [5:0]  output_select,       
    input  logic [5:0]  input_select,

    output logic        oht_mux_out,   // Serial debug output (direct from an entropy source)
    output logic [31:0] sram_in        // Normal input to the SRAM
);

    // This block describes the complete behavior for the outputs
    always_comb begin
        // 1. Default assignments (normal operation)
        sram_in = oht_outputs;
        oht_mux_out = 1'b0;

        // 2. Debug logic overrides the defaults
        if (debug) begin
            // If the debug output is enabled, connect one oht_output bit to the mux output
            if (output_select[5]) begin
                oht_mux_out = oht_outputs[output_select[4:0]];
            end

            // If the debug input is enabled, override one bit of the sram_in bus
            if (input_select[5]) begin
                sram_in[input_select[4:0]] = sram_mux_in;
            end
        end
    end

endmodule