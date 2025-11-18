module OHT_J
import le_types::*;
import params::*;
(

    input logic adc_in, // data value from entropy source
    input logic clk,
    input logic rst,
    // input logic debug_mode,

    output logic perm_fail,
    output logic valid,
    output logic j_disable

);

logic [$clog2(ENTROPY_SAMPLE)-1:0] entropy_counter, sample_cnt;
logic [4:0] perm_cnt;
logic [1:0] inter_cnt;
logic inter_fail;
logic in_curr, in_prior;
logic flag, flag_nxt;
logic window;
logic good_entropy_out;

always_ff @( posedge clk ) begin
    if (!rst) begin
        window <= '0;
    end else if (sample_cnt == 1023) begin
        window <= 1'b1;
    end else begin
        window <= window;
    end
end

always_ff @(posedge clk) begin
    if (!rst) begin
        sample_cnt <= '0;
    end else if (inter_fail || perm_fail) begin
        sample_cnt <= '0;
    end else begin
        sample_cnt <= sample_cnt + 1;
    end
end

always_ff @(posedge clk) begin
    if (!rst) begin
        entropy_counter <= '0;
    end else if (perm_fail) begin
        entropy_counter <= '0;
    end else if(inter_fail || entropy_counter == 1023) begin
        entropy_counter <= '0;
    end else if (adc_in == 1'b1) begin
        entropy_counter <= entropy_counter + 1;
    end else begin

    end
end

always_ff @( posedge clk ) begin : perm_check
    if (!rst) begin
        flag <= '0;
        flag_nxt <= '0;
        in_curr <= '0;
        in_prior <= '0;
    end else begin
        flag_nxt <= '1; // flag_nxt gets current adc input
        flag <= flag_nxt; // flag has the old adc input
        in_curr <= adc_in;
        in_prior <= in_curr;
    end
end

always_ff @(posedge clk) begin
    if (!rst || inter_fail) begin
       perm_cnt <= '0;
    end else if (perm_fail) begin
        // do nothing
    end else if (in_curr == in_prior && flag) begin
        perm_cnt <= perm_cnt + 1;
    end else begin
        perm_cnt <= '0;
    end
end

always_ff @(posedge clk) begin
    if (!rst) begin
        inter_fail <= '0;
        inter_cnt <= '0;
    end else if (perm_fail) begin
        // do nothing
    end else if (perm_cnt == 20 && inter_cnt < 2'b11) begin
        inter_cnt <= inter_cnt + 1;
        inter_fail <= 1'b1;
    end else begin
        inter_fail <= '0;
    end
end

always_ff @(posedge clk) begin
    if (!rst) begin
        valid <= '0;
    end else if (good_entropy_out) begin
        valid <= '1;
    end else begin
        // do nothing
    end
end

assign perm_fail = (inter_cnt == 2'b11 && perm_cnt == 30) ? 1'b1 : 1'b0;
logic disable_flag;

always_ff @(posedge clk) begin
    if (!rst) begin
        disable_flag <= '0;
    end else begin
        disable_flag <= '1;
    end
end

assign j_disable = !(perm_fail || inter_fail) && disable_flag;

always_comb begin

    good_entropy_out = '0;
    if (!perm_fail && !inter_fail && window) begin
        if (entropy_counter < 128 && entropy_counter >= 0) begin                // 0-12.5
            good_entropy_out = '0;
        end else if (entropy_counter < 255 && entropy_counter >= 128) begin     // 12.5-25
            good_entropy_out = '0;
        end else if (entropy_counter < 460 && entropy_counter >= 255) begin     // 25-45
            good_entropy_out = '0;
        end else if (entropy_counter < 563 && entropy_counter >= 460) begin     // 45-55
            good_entropy_out = '1;
        end else if (entropy_counter < 767 && entropy_counter >= 563) begin     // 55-75
            good_entropy_out = '0;
        end else if (entropy_counter < 895 && entropy_counter >= 767) begin     // 75-87.5
            good_entropy_out = '0;
        end else if (entropy_counter <= 1023 && entropy_counter >= 895) begin   // 87.5-100
            good_entropy_out = '0;
        end         
    end
end

endmodule
