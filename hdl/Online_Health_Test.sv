module OHT
import le_types::*;
import params::*;
(

    input logic adc_in, // data value from entropy source
    input logic adc_en, // read data from entropy source when high -> apparently will be a multiple of the clock freq so base it on clock divider
    input logic clk,
    input logic rst,
    input logic deque,
    // input logic debug_mode,
    // input logic 

    output logic inter_fail,
    output logic perm_fail,
    output logic [SAMPLE_SIZE-1:0] checked_noise,
    output logic good_entropy_out,
    output logic full,
    output logic empty,

    // outputs for controlling entropy source calibration
    output logic [7:0] calibration_arr_n,   // controls the number of 1s
    output logic [7:0] calibration_arr_p    // controls the number of 0s

);

logic [$clog2(C_PERM)-1:0] counter, counter_next;
logic [$clog2(SAMPLE_SIZE)-1:0] noise_counter, noise_counter_next;
logic [$clog2(ENTROPY_SAMPLE)-1:0] entropy_counter, entropy_counter_next;
logic [SAMPLE_SIZE-1:0] buff_reg, buff_next;
logic [1:0] enque_counter, enque_counter_next;
logic enque, rep_fail, adaptive_fail, calibration_pass;
logic [7:0] calibration_arr_n_curr, calibration_arr_n_next, calibration_arr_p_curr, calibration_arr_p_next;

// logic bypass_buff_flag;
// logic bypass_off;
// logic flag;
assign perm_fail = rep_fail && adaptive_fail;

assign enque = !full && (noise_counter == 255) && !inter_fail && !perm_fail;

que fifo (

    .clk(clk),
    .rst(rst),
    .inter_fail(inter_fail),
    .perm_fail(perm_fail),

    .wdata(buff_next),
    .rdata(checked_noise),

    .enque(enque),
    .deque(deque),

    .full(full),
    .empty(empty)

);

// always_ff @(posedge clk) begin

    // bypass_buff_flag <= '0;
    // bypass_off <= '0;

    // if (rst) begin
    //     bypass_buff_flag <= '0;
    //     bypass_off <= '0;
    // end else if (adc_en) begin

    // end

// end

always_ff @(posedge adc_en) begin
    // enque_counter_next <= enque_counter;
    if (rst) begin
        enque_counter <= '0;
    end else if (enque) begin
        enque_counter <= enque_counter + 1;
    end else begin
        // enque_counter <= enque_counter_next;
    end
end

always_ff @(posedge adc_en) begin
    // enque_counter_next <= enque_counter;
    if (rst) begin
        entropy_counter <= '0;
    end else if(inter_fail || rep_fail || adaptive_fail) begin
        entropy_counter <= '0;
    end else if (adc_in == 1'b1) begin
        entropy_counter <= entropy_counter + 1;
    end else begin
        // enque_counter <= enque_counter_next;
    end
end

always_ff @(posedge clk) begin

    buff_next <= buff_reg;
    counter_next <= counter;
    noise_counter_next <= noise_counter;
    // entropy_counter_next <= entropy_counter;

    if (rst) begin
        buff_reg <= 'x;
        counter <='0;
        noise_counter <= '0;
        // entropy_counter <= '0;
        // flag <= '0;
        // enque_counter <= '0;
    end
    else if (adc_en) begin
        buff_next <= {buff_reg[SAMPLE_SIZE-2:0], adc_in};
        counter_next <= counter + 1;
        noise_counter_next <= noise_counter + 1;
        // if (inter_fail || rep_fail || adaptive_fail) begin
        //     entropy_counter_next <= '0;
        // end
        // else if (adc_in == 1'b1) begin
        //     entropy_counter_next <= entropy_counter + 1;
        // end
    end
    else begin

        counter <= counter_next;
        noise_counter <=  noise_counter_next;
        // entropy_counter <= entropy_counter_next;
        buff_reg <= buff_next;

    end    

end


always_comb begin

    inter_fail = '0;
    rep_fail = '0;
    calibration_pass = '0;
    if (counter == 31) begin
        calibration_pass = '1;
        if (buff_reg[C_INTER-1:0] == '1 || buff_reg[C_INTER-1:0] == '0) begin
            inter_fail = '1;
            calibration_pass = 1'b0;
        end
        if (buff_reg[C_PERM-1:0] == '1 || buff_reg[C_PERM-1:0] == '0) begin
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
        calibration_arr_n_curr <= 8'b11000000;
        calibration_arr_p_curr <= 8'b11000000;
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

    if ((calibration_arr_n_curr == '0 || calibration_arr_p_curr == '0) && inter_fail) begin
        adaptive_fail = '1;
    end else if (inter_fail) begin
        if (buff_reg[C_INTER-1:0] == '1) begin
            calibration_arr_n_next = {1'b0, calibration_arr_n[7:1]};
        end
        if (buff_reg[C_INTER-1:0] == '0) begin
            calibration_arr_p_next = {1'b0, calibration_arr_p[7:1]};
        end
    end else if (calibration_pass && enque_counter == 2'b11) begin

            if (entropy_counter < 128 && entropy_counter >= 0) begin                // 0-12.5
                if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = calibration_arr_n_curr + 3;
                end else if (calibration_arr_p_curr != '0) begin
                    calibration_arr_p_next = calibration_arr_p_curr - 3;
                end
            end else if (entropy_counter < 255 && entropy_counter >= 128) begin     // 12.5-25
                if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = calibration_arr_n_curr + 2;
                end else if (calibration_arr_p_curr != '0) begin
                    calibration_arr_p_next = calibration_arr_p_curr - 2;
                end
            end else if (entropy_counter < 460 && entropy_counter >= 256) begin     // 25-45
                if (calibration_arr_n_curr != '1) begin
                    calibration_arr_n_next = calibration_arr_n_curr + 1;
                end else if (calibration_arr_p_curr != '0) begin
                    calibration_arr_p_next = calibration_arr_p_curr - 1;
                end
            end else if (entropy_counter < 563 && entropy_counter >= 461) begin     // 45-55
                good_entropy_out = '1;
            end else if (entropy_counter < 767 && entropy_counter >= 564) begin     // 55-75
                if (calibration_arr_n_curr != '0) begin
                    calibration_arr_n_next = calibration_arr_n_curr - 1;
                end else if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = calibration_arr_p_curr + 1;
                end
            end else if (entropy_counter < 895 && entropy_counter >= 768) begin     // 75-87.5
                if (calibration_arr_n_curr != '0) begin
                    calibration_arr_n_next = calibration_arr_n_curr - 2;
                end else if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = calibration_arr_p_curr + 2;
                end
            end else if (entropy_counter <= 1023 && entropy_counter >= 896)         // 87.5-100
                if (calibration_arr_n_curr != '0) begin
                    calibration_arr_n_next = calibration_arr_n_curr - 3;
                end else if (calibration_arr_p_curr != '1) begin
                    calibration_arr_p_next = calibration_arr_p_curr + 3;
                end

        end
    end

endmodule
