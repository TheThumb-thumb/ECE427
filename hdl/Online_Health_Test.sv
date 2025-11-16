module OHT
import le_types::*;
import params::*;
(

    input logic adc_in, // data value from entropy source
    input logic clk,
    input logic rst,
    input logic debug_mode,
    input logic [11:0] spi_reg_lsb,
    input logic full,

    output logic perm_fail,
    output logic valid,
    // outputs for controlling entropy source calibration
    output logic [5:0] calibration_arr_n,   // controls the number of 0s
    output logic [5:0] calibration_arr_p    // controls the number of 1s

);

logic [$clog2(ENTROPY_SAMPLE)-1:0] entropy_counter, sample_cnt;
logic [C_PERM-1:0] buff_reg;
logic rep_fail, adaptive_fail, calibration_pass;
logic [5:0] calibration_arr_n_curr, calibration_arr_p_curr, calibration_arr_n_next, calibration_arr_p_next;
logic good_entropy_out_flag, good_entropy_out;
logic inter_fail;
logic window;
logic flag, calib_flag;

always_ff @( posedge clk ) begin
    if (rst) begin
        flag <= '0;
    end else if (sample_cnt[5]) begin
        flag <= 1'b1;
    end else begin
        // do nothing
    end
end

assign perm_fail = rep_fail && adaptive_fail;

always_comb begin

    inter_fail = '0;
    rep_fail = '0;
    calibration_pass = '0;
    if (flag) begin
        calibration_pass = '1;
        if (buff_reg[C_INTER-1:0] == '1 || buff_reg[C_INTER-1:0] == '0) begin
            inter_fail = '1;
            calibration_pass = 1'b0;
        end
        if (buff_reg[C_PERM-2:0] == '1 || buff_reg[C_PERM-2:0] == '0) begin
            rep_fail = '1;
            calibration_pass = 1'b0;
        end
    end else begin
        calibration_pass = '1;
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        valid <= '0;
    end else if (good_entropy_out_flag) begin
        valid <= '1;
    end else begin
        // do nothing
    end
end

always_ff @( posedge clk ) begin
    if (rst) begin
        window <= '0;
    end else if (sample_cnt == 1023) begin
        window <= 1'b1;
    end else if (calib_flag) begin
        window <= '0;
    end else begin
        window <= '0;
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        sample_cnt <= '0;
    end else if (inter_fail || perm_fail) begin
        sample_cnt <= '0;
    end else if (!full) begin
        sample_cnt <= sample_cnt + 1;
    end else begin
        // do nothing
    end
end

always_ff @(posedge clk) begin
    if (rst) begin
        entropy_counter <= '0;
    end else if(inter_fail || rep_fail || adaptive_fail || entropy_counter == 1023 || window) begin
        entropy_counter <= '0;
    end else if (adc_in == 1'b1 && !full) begin
        entropy_counter <= entropy_counter + 1;
    end else begin

    end
end

always_ff @(posedge clk) begin

    if (rst) begin
        buff_reg <= '0;
    end else if (!full) begin
        buff_reg <= {buff_reg[C_PERM-2:0], adc_in};
    end else begin
        // do nothing
    end
end

assign calibration_arr_n = calibration_arr_n_curr;
assign calibration_arr_p = calibration_arr_p_curr;

always_ff @(posedge clk) begin

    if (rst) begin
        calibration_arr_n_curr <= 6'b000000; // checkout 0111111
        calibration_arr_p_curr <= 6'b000000; // all 1s
    end else if (debug_mode) begin
        calibration_arr_n_curr <= spi_reg_lsb[11:6];
        calibration_arr_p_curr <= spi_reg_lsb[5:0];
    end else begin
        calibration_arr_n_curr <= calibration_arr_n_next;
        calibration_arr_p_curr <= calibration_arr_p_next;
    end

end

always_ff @(posedge clk) begin

    if (rst) begin
        good_entropy_out_flag <= '0;
    end else if (window) begin
        good_entropy_out_flag <= good_entropy_out;
    end else begin
        // do nothing
    end

end

always_comb begin

    calib_flag = 1'b0;
    good_entropy_out = '0;
    adaptive_fail = '0;
    calibration_arr_n_next = calibration_arr_n_curr;
    calibration_arr_p_next = calibration_arr_p_curr;
    if (inter_fail && !full && calibration_arr_n_curr == '1 && calibration_arr_p_curr == '1) begin
        adaptive_fail = '1;
    end else if (inter_fail && !full) begin
        if (buff_reg[C_INTER-1:0] == '1) begin
            calibration_arr_n_next = (calibration_arr_n_curr + 8'h03 > 6'b111111) ? '1 : calibration_arr_n_curr + 8'h03;
            calib_flag = 1'b0;
        end
        if (buff_reg[C_INTER-1:0] == '0) begin
            calibration_arr_p_next = (calibration_arr_p_curr + 8'h03 > 6'b111111) ? '1 : calibration_arr_p_curr + 8'h03;
            calib_flag = 1'b0;
        end
    end else if ((calibration_pass && window) || (inter_fail && !full && !good_entropy_out_flag)) begin

            if (entropy_counter < 128 && entropy_counter >= 0) begin                // 0-12.5
                calib_flag = 1'b1;
                if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = (calibration_arr_p_curr + 8'h03 > 6'b111111) ? '1 : calibration_arr_p_curr + 8'h03;
                end 
                // else if (calibration_arr_n_curr != '1) begin
                //     calibration_arr_n_next = (calibration_arr_n_curr - 8'h03 < 0) ? '0 : calibration_arr_n_curr - 8'h03;
                // end
                
            end else if (entropy_counter < 255 && entropy_counter >= 128) begin     // 12.5-25
                calib_flag = 1'b1;
                if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = (calibration_arr_p_curr + 8'h02 > 6'b111111) ? '1 : calibration_arr_p_curr + 8'h02;
                end 
                // else if (calibration_arr_n_curr != '1) begin
                //     calibration_arr_n_next = (calibration_arr_n_curr - 8'h02 < 0) ? '0 : calibration_arr_n_curr - 8'h02;
                // end

            end else if (entropy_counter < 460 && entropy_counter >= 255) begin     // 25-45
                calib_flag = 1'b1;
                if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = (calibration_arr_p_curr + 8'h01 > 6'b111111) ? '1 : calibration_arr_p_curr + 8'h01;
                end 
                // else if (calibration_arr_n_curr != '1) begin
                //     calibration_arr_n_next = (calibration_arr_n_curr - 8'h01 < 0) ? '0 : calibration_arr_n_curr - 8'h01;
                // end

            end else if (entropy_counter < 563 && entropy_counter >= 460) begin     // 45-55
                good_entropy_out = '1;
                calib_flag = 1'b0;
            end else if (entropy_counter < 767 && entropy_counter >= 563) begin     // 55-75
                calib_flag = 1'b1;
                if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = (calibration_arr_n_curr + 8'h01 > 6'b111111) ? '1 : calibration_arr_n_curr + 8'h01;
                end 
                // else if (calibration_arr_p_curr != '1) begin
                //     calibration_arr_p_next = (calibration_arr_p_curr - 8'h01 < 0) ? '0 : calibration_arr_p_curr - 8'h01;
                // end

            end else if (entropy_counter < 895 && entropy_counter >= 767) begin     // 75-87.5
                calib_flag = 1'b1;
                if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = (calibration_arr_n_curr + 8'h02 > 6'b111111) ? '1 : calibration_arr_n_curr + 8'h02;
                end 
                // else if (calibration_arr_p_curr != '1) begin
                //     calibration_arr_p_next = (calibration_arr_p_curr - 8'h02 < 0) ? '0 : calibration_arr_p_curr - 8'h02;
                // end

            end else if (entropy_counter <= 1023 && entropy_counter >= 895)  begin       // 87.5-100
                calib_flag = 1'b1;
                if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = (calibration_arr_n_curr + 8'h03 > 6'b111111) ? '1 : calibration_arr_n_curr + 8'h03;
                end 
                // else if (calibration_arr_p_curr != '1) begin
                //     calibration_arr_p_next = (calibration_arr_p_curr - 8'h03 < 0) ? '0 : calibration_arr_p_curr - 8'h03;
                // end
             end 
    end
    else begin
        // do nothing
    end
end

endmodule
