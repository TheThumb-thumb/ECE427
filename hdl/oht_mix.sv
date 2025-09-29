//systemVerilog HDL for "strongARM", "OHT" "systemVerilog"

localparam IV_WIDTH = 80;
    localparam SETUP_TIME = 1151; // Cycles needed for trivium to cycle through internal state 4 times = 4 x 288 = 1152
    localparam ADC_FIF0_DEPTH = 80;
    localparam ENTROPY_SAMPLE = 1024;   
    localparam ENTROPY_CUTOFF = 588;
    localparam SAMPLE_SIZE = 256;   
    localparam C_INTER = 22;
    localparam C_PERM = 32;
    localparam OUTREG_MAX_WIDTH = 64;


module OHT
(

    input logic adc_in, // data value from entropy source
    input logic adc_en, // read data from entropy source when high -> apparently will be a multiple of the clock freq so base it on clock divider
    input logic clk,
    input logic rst,
    input logic deque, // Should only deque if good_entropy_out is high because that means we have 1024 samples stored and they are within 45-55% range
    input logic debug_mode,
    input logic [7:0] spi_reg_lsb,

    output logic inter_fail,
    output logic perm_fail,
    output logic [255:0] checked_noise,
    output logic good_entropy_out,
    output logic full,
    output logic empty,

    // outputs for controlling entropy source calibration
    output logic [7:0] calibration_arr_n,   // controls the number of 1s
    output logic [7:0] calibration_arr_p,    // controls the number of 0s
    output logic calib_flag,
    output logic calibration_pass

);

logic [$clog2(256)-1:0] noise_counter;
logic [$clog2(1024)-1:0] entropy_counter;
logic [255:0] buff_reg;
logic [1:0] enque_counter;
logic enque, rep_fail, adaptive_fail;
//logic calibration_pass;
logic [7:0] calibration_arr_n_curr, calibration_arr_n_next, calibration_arr_p_curr, calibration_arr_p_next, lsb_reg, lsb_reg_next;

logic enq_flag, enq_flag_next;
//logic calib_flag
logic calib_flag_next;

assign perm_fail = rep_fail && adaptive_fail;

assign enque = enq_flag && !enq_flag_next;

que fifo (

    .clk(clk),
    .rst(rst),
    .inter_fail(inter_fail),
    .perm_fail(perm_fail),

    .wdata(buff_reg),
    .rdata(checked_noise),

    .enque(enque),
    .deque(deque),

    .full(full),
    .empty(empty)

);

always_ff @(posedge clk) begin
    if (rst) begin
        calib_flag <= '0;
        calib_flag_next <= '0;
    end else if (enque && enque_counter == 2'b11 && calib_flag == 0) begin
        calib_flag_next <= '1;
    end else begin
        calib_flag <= calib_flag_next;
        calib_flag_next <= '0;
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        enq_flag <= '0;
        enq_flag_next <= '0;
    end else if (!full && (noise_counter == 255) && !inter_fail && !perm_fail)begin
        enq_flag_next <= '1;
    end else begin
        // do nothing
        enq_flag <= enq_flag_next;
        enq_flag_next <= '0;
    end

end

always_ff @(posedge clk) begin
    if (rst || inter_fail || perm_fail) begin
        enque_counter <= '0;
    end else if (enque) begin
        enque_counter <= enque_counter + 1;
    end else begin
    end
end

always_ff @(posedge adc_en) begin
    if (rst) begin
        entropy_counter <= '0;
    end else if(inter_fail || rep_fail || adaptive_fail || entropy_counter == 1023) begin
        entropy_counter <= '0;
    end else if (adc_in == 1'b1) begin
        entropy_counter <= entropy_counter + 1;
    end else begin

    end
end

always_ff @(posedge adc_en) begin

    if (rst) begin
        buff_reg <= 'x;
        noise_counter <= '0;
    end else begin
        noise_counter <= noise_counter + 1;
        buff_reg <= {buff_reg[254:0], adc_in};
    end
end

always_comb begin

    inter_fail = '0;
    rep_fail = '0;
    calibration_pass = '0;
    if (noise_counter[5:0] == 31) begin
        calibration_pass = '1;
        if (buff_reg[21:0] == '1 || buff_reg[21:0] == '0) begin
            inter_fail = '1;
            calibration_pass = 1'b0;
        end
        if (buff_reg[31:0] == '1 || buff_reg[31:0] == '0) begin
            rep_fail = '1;
            calibration_pass = 1'b0;
        end
    end else begin
        calibration_pass = '1;
    end
end


assign calibration_arr_n = calibration_arr_n_curr;
assign calibration_arr_p = calibration_arr_p_curr;

always_ff @(posedge adc_en) begin

    if (rst) begin
        calibration_arr_n_curr <= 8'b11100100;
        calibration_arr_p_curr <= 8'b11000000;
    end else begin
        calibration_arr_n_curr <= calibration_arr_n_next;
        calibration_arr_p_curr <= calibration_arr_p_next;
    end

end

always_ff @(posedge adc_en) begin

    if (rst) begin
        lsb_reg <= 8'h03;
    end else if (debug_mode) begin
        lsb_reg <= spi_reg_lsb;
    end else begin
        lsb_reg <= lsb_reg_next;
    end
end

always_comb begin

    good_entropy_out = '0;
    adaptive_fail = '0;
    calibration_arr_n_next = calibration_arr_n_curr;
    calibration_arr_p_next = calibration_arr_p_curr;
    lsb_reg_next = lsb_reg;
    if ((calibration_arr_n_curr == '0 || calibration_arr_p_curr == '0) && inter_fail) begin
        adaptive_fail = '1;
    end
else if (inter_fail) begin
        if (buff_reg[C_INTER-1:0] == '1) begin
            calibration_arr_p_next = calibration_arr_p_curr - 2'b11;
        end
        if (buff_reg[C_INTER-1:0] == '0) begin
            calibration_arr_n_next = calibration_arr_n_curr - 2'b11;
        end
   end
 else if (calibration_pass && calib_flag) begin

            if (entropy_counter < 128 && entropy_counter >= 0) begin                // 0-12.5
                if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = calibration_arr_p_curr + lsb_reg;
                    lsb_reg_next = 8'h03;
                end else if (calibration_arr_n_curr != '0) begin
                    calibration_arr_n_next = calibration_arr_n_curr - lsb_reg;
                    lsb_reg_next = 8'h03;
                end
            end else if (entropy_counter < 255 && entropy_counter >= 128) begin     // 12.5-25
                if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = calibration_arr_p_curr + lsb_reg;
                    lsb_reg_next = 8'h02;
                end else if (calibration_arr_n_curr != '0) begin
                    calibration_arr_n_next = calibration_arr_n_curr - lsb_reg;
                    lsb_reg_next = 8'h02;
                end
            end else if (entropy_counter < 460 && entropy_counter >= 256) begin     // 25-45
                if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = calibration_arr_p_curr + lsb_reg;
                    lsb_reg_next = 8'h01;
                end else if (calibration_arr_n_curr != '0) begin
                    calibration_arr_n_next = calibration_arr_n_curr - lsb_reg;
                    lsb_reg_next = 8'h01;
                end
            end else if (entropy_counter < 563 && entropy_counter >= 461) begin     // 45-55
                good_entropy_out = '1;
            end else if (entropy_counter < 767 && entropy_counter >= 564) begin     // 55-75
                if (calibration_arr_p_curr != '0) begin
                    calibration_arr_p_next = calibration_arr_p_curr - lsb_reg;
                    lsb_reg_next = 8'h01;
                end else if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = calibration_arr_n_curr + lsb_reg;
                    lsb_reg_next = 8'h01;
                end
            end else if (entropy_counter < 895 && entropy_counter >= 768) begin     // 75-87.5
                if (calibration_arr_p_curr != '0) begin
                    calibration_arr_p_next = calibration_arr_p_curr - lsb_reg;
                    lsb_reg_next = 8'h02;
                end else if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = calibration_arr_n_curr + lsb_reg;
                    lsb_reg_next = 8'h02;
                end
            end else if (entropy_counter <= 1023 && entropy_counter >= 896)         // 87.5-100
                if (calibration_arr_p_curr != '0) begin
                    calibration_arr_p_next = calibration_arr_p_curr - lsb_reg;
                    lsb_reg_next = 8'h03;
                end else if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = calibration_arr_n_curr + lsb_reg;
                    lsb_reg_next = 8'h03;
                end

        end
    end
endmodule

