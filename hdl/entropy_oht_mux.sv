// This is between entropy sources and OHT so we can see the entropy outputs and test OHT data input
// This will be used twice. Once for the Latch entropy sources and once for the jitter entropy sources


module entropy_oht_mux (
    input  logic        debug,

    input  logic [31:0] entropy_sources_out, // Coming from entropy sources
    input  logic        oht_mux_in,          // Serial debug input to test OHT

    input  logic [5:0]  output_select,       // Selects which entropy source to route to output pin
    input  logic [5:0]  input_select,        // Selects which OHT to receive input

    output logic        entropy_mux_out,     // Serial debug output (direct from entropy source)
    output logic [31:0] oht_in               // Input to the OHT
);

    always_comb begin
        // 1. Default assignments for normal operation
        oht_in = entropy_sources_out;

        // 2. Debug logic overrides the defaults if debug is active
        if (debug) begin
            // Handle the debug output path
            if (output_select[5]) begin
                entropy_mux_out = entropy_sources_out[output_select[4:0]];
            end

            // Handle the debug input path (overrides one bit of oht_in)
            if (input_select[5]) begin
                oht_in[input_select[4:0]] = oht_mux_in;
            end
        end
    end

endmodule