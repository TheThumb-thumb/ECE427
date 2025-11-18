module ro_temp_control_v1 (
    input  wire        EN_IN,               // to turn on or turn off temp sensor
    input  wire        rst_n,               // Active low reset
    input  wire        CLK,                 // normal clock of system
    input  wire [13:0] TEMP_IN,             // one comes from ring oscillator
    input  wire [13:0] TEMP_CMP,            // one comes from spi
    output reg         EN_OUT1,             // feeds into temperature sensor
    output reg         EN_OUT2,             // feeds into temperature sensor
    output reg         TEMP_CMP_OUT_REG     // one hot out for top_io
);

    reg [12:0] counter;                      // need to change cutoff and counter based on frequency

    always @(posedge CLK) begin
        if (!EN_IN || !rst_n) begin
            counter <= 13'd0;
            EN_OUT1 <= 1'b0;
            EN_OUT2 <= 1'b1;
            TEMP_CMP_OUT_REG <= 1'b0;
        end else begin
            if (counter == 13'd8191) begin
                counter <= 13'd0;

                EN_OUT1 <= 1'b0;
                EN_OUT2 <= 1'b1;

                TEMP_CMP_OUT_REG <= (TEMP_IN < TEMP_CMP);
            end else begin
                counter <= counter + 1'b1;

                EN_OUT1 <= 1'b1;
                EN_OUT2 <= 1'b0;
            end
        end
    end

endmodule