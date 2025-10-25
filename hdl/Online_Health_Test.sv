module OHT
import le_types::*;
import params::*;
(

    input logic adc_in, // data value from entropy source
    input logic clk,
    input logic rst,
    input logic debug_mode,
    input logic [15:0] spi_reg_lsb,
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
logic [5:0] calibration_arr_n_curr, calibration_arr_n_next, calibration_arr_p_curr, calibration_arr_p_next;
logic good_entropy_out;
logic inter_fail;
logic window;
logic flag;


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
    end else if (good_entropy_out) begin
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
    end else begin
        window <= window;
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
    end else if(inter_fail || rep_fail || adaptive_fail || entropy_counter == 1023) begin
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

// IN DEBUG:
// if 

assign calibration_arr_n = calibration_arr_n_curr;
assign calibration_arr_p = calibration_arr_p_curr;

always_ff @(posedge clk) begin

    if (rst) begin
        calibration_arr_n_curr <= 6'b000000;
        calibration_arr_p_curr <= 6'b000000;
    end else if (debug_mode) begin
        calibration_arr_n_curr <= spi_reg_lsb[15:8];
        calibration_arr_p_curr <= spi_reg_lsb[7:0];
    end else begin
        calibration_arr_n_curr <= calibration_arr_n_next;
        calibration_arr_p_curr <= calibration_arr_p_next;
    end

end

always_comb begin

    good_entropy_out = '0;
    adaptive_fail = '0;
    calibration_arr_n_next = calibration_arr_n_curr;
    calibration_arr_p_next = calibration_arr_p_curr;
    if ((calibration_arr_n_curr == '0 || calibration_arr_p_curr == '0) && inter_fail && !full) begin
        adaptive_fail = '1;
    end else if (inter_fail && !full) begin
        if (buff_reg[C_INTER-1:0] == '1) begin
            calibration_arr_p_next = calibration_arr_p_curr - 2'b11;
        end
        if (buff_reg[C_INTER-1:0] == '0) begin
            calibration_arr_n_next = calibration_arr_n_curr - 2'b11;
        end
    end else if ((calibration_pass && window) || inter_fail && !full) begin

            if (entropy_counter < 128 && entropy_counter >= 0) begin                // 0-12.5
                if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = calibration_arr_p_curr + 8'h03;
                end else if (calibration_arr_n_curr != '0) begin
                    calibration_arr_n_next = calibration_arr_n_curr - 8'h03;
                end
            end else if (entropy_counter < 255 && entropy_counter >= 128) begin     // 12.5-25
                if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = calibration_arr_p_curr + 8'h02;
                end else if (calibration_arr_n_curr != '0) begin
                    calibration_arr_n_next = calibration_arr_n_curr - 8'h02;
                end
            end else if (entropy_counter < 460 && entropy_counter >= 256) begin     // 25-45
                if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = calibration_arr_p_curr + 8'h01;
                end else if (calibration_arr_n_curr != '0) begin
                    calibration_arr_n_next = calibration_arr_n_curr - 8'h01;
                end
            end else if (entropy_counter < 563 && entropy_counter >= 461) begin     // 45-55
                good_entropy_out = '1;
            end else if (entropy_counter < 767 && entropy_counter >= 564) begin     // 55-75
                if (calibration_arr_p_curr != '0) begin
                    calibration_arr_p_next = calibration_arr_p_curr - 8'h01;
                end else if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = calibration_arr_n_curr + 8'h01;
                end
            end else if (entropy_counter < 895 && entropy_counter >= 768) begin     // 75-87.5
                if (calibration_arr_p_curr != '0) begin
                    calibration_arr_p_next = calibration_arr_p_curr - 8'h02;
                end else if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = calibration_arr_n_curr + 8'h02;
                end
            end else if (entropy_counter <= 1023 && entropy_counter >= 896)         // 87.5-100
                if (calibration_arr_p_curr != '0) begin
                    calibration_arr_p_next = calibration_arr_p_curr - 8'h03;
                end else if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = calibration_arr_n_curr + 8'h03;
                end

    end else begin
        // do nothing
    end
end

endmodule
