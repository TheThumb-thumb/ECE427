// module binary_gcd
// import params::*;
// import le_types::*;
// (
//     input logic clk,
//     input logic rst,
//     input logic start,
//     input logic [KEY_WIDTH-1:0] u,
//     input logic [KEY_WIDTH-1:0] v,
//     output logic [KEY_WIDTH-1:0] gcd_out,
//     output logic done
// );

//     logic [KEY_WIDTH-1:0] a_reg, b_reg;
//     logic [KEY_WIDTH-1:0] k_reg; // To store the common factor of 2

//     gcd_state_t curr_state, next_state;

//     // State machine for control flow
//     always_ff @(posedge clk) begin
//         if (rst) begin
//             curr_state <= IDLE;
//         end else begin
//             curr_state <= next_state;
//         end
//     end

//     // Next curr_state logic
//     always_comb begin
//         next_state = curr_state;
//         done = 1'b0; // Default to not done

//         case (curr_state)
//             IDLE: begin
//                 if (start) begin
//                     next_state = INIT_K;
//                 end
//             end
//             INIT_K: begin
//                 if ((a_reg == 0) || (b_reg == 0)) begin // Handle cases where one input is zero
//                     next_state = DONE;
//                 end else if (((a_reg | b_reg) & 1) == 0) begin // Both even
//                     next_state = INIT_K; // Stay in INIT_K to continue shifting
//                 end else begin // At least one is odd
//                     next_state = NORMALIZE_A;
//                 end
//             end
//             NORMALIZE_A: begin
//                 if ((a_reg & 1) == 0) begin // a is even
//                     next_state = NORMALIZE_A; // Continue normalizing a
//                 end else begin // a is odd
//                     next_state = COMPUTE;
//                 end
//             end
//             NORMALIZE_B: begin
//                 if ((b_reg & 1) == 0) begin // b is even
//                     next_state = NORMALIZE_B; // Continue normalizing b
//                 end else begin // b is odd
//                     next_state = COMPUTE;
//                 end
//             end
//             COMPUTE: begin
//                 if (b_reg == 0) begin
//                     next_state = DONE;
//                 end else if (a_reg > b_reg) begin
//                     next_state = NORMALIZE_B; // After subtraction, b might become even
//                 end else begin // b_reg > a_reg
//                     next_state = NORMALIZE_A; // After subtraction, a might become even
//                 end
//             end
//             DONE: begin
//                 done = 1'b1;
//                 if (!start) begin // Reset when start goes low
//                     next_state = IDLE;
//                 end
//             end
//         endcase
//     end

//     always_ff @(posedge clk) begin
//         if (rst) begin
//             a_reg <= 0;
//             b_reg <= 0;
//             k_reg <= 0;
//             gcd_out <= 0;
//         end else begin
//             case (curr_state)
//                 IDLE: begin
//                     if (start) begin
//                         a_reg <= a_in;
//                         b_reg <= b_in;
//                         k_reg <= 0;
//                     end
//                 end
//                 INIT_K: begin
//                     if ((a_reg == 0) || (b_reg == 0)) begin
//                         gcd_out <= (a_reg == 0) ? b_reg : a_reg;
//                     end else if (((a_reg | b_reg) & 1) == 0) begin // Both even
//                         a_reg <= a_reg >> 1;
//                         b_reg <= b_reg >> 1;
//                         k_reg <= k_reg + 1;
//                     end
//                 end
//                 NORMALIZE_A: begin
//                     if ((a_reg & 1) == 0) begin // a is even
//                         a_reg <= a_reg >> 1;
//                     end
//                 end
//                 NORMALIZE_B: begin
//                     if ((b_reg & 1) == 0) begin // b is even
//                         b_reg <= b_reg >> 1;
//                     end
//                 end
//                 COMPUTE: begin
//                     if (a_reg > b_reg) begin
//                         a_reg <= a_reg - b_reg;
//                     end else begin // b_reg > a_reg
//                         b_reg <= b_reg - a_reg;
//                     end
//                 end
//                 DONE: begin
//                     gcd_out <= a_reg << k_reg; // Final result
//                 end
//             endcase
//         end
//     end

// endmodule

module binary_gcd
import params::*;
import le_types::*;
(
    input logic clk,
    input logic rst,
    input logic start,
    input logic [KEY_WIDTH-1:0] u,
    input logic [KEY_WIDTH-1:0] v,
    output logic [KEY_WIDTH-1:0] gcd_out,
    output logic done
);

    logic [KEY_WIDTH-1:0] a_reg, b_reg;
    logic [KEY_WIDTH-1:0] k_reg; // To store the common factor of 2

    gcd_state_t curr_state, next_state;

    logic a_zero, b_zero, same;

    // State machine for control flow
    always_ff @(posedge clk) begin
        if (rst) begin
            curr_state <= IDLE;
        end else begin
            curr_state <= next_state;
        end
    end

    // Next curr_state logic
    always_comb begin
        next_state = curr_state;
        done = 1'b0; // Default to not done
        a_zero = '0;
        b_zero = '0;
        same = '0;

        case (curr_state)
            IDLE: begin
                a_zero = '0;
                b_zero = '0;
                same = '0;
                if (start) begin
                    next_state = INIT_K;
                end
            end
            INIT_K: begin
                if (a_reg == 0) begin   // Handle cases where one input is zero or the same
                    a_zero = 1'b1;
                    next_state = DONE;
                end else if (b_reg == 0) begin 
                    b_zero = 1'b1;
                    next_state = DONE;
                end else if (a_reg == b_reg) begin
                    same = 1'b1;
                    next_state = DONE;
                end else if (((a_reg | b_reg) & 1) == 0) begin // Both even
                    next_state = INIT_K; // Stay in INIT_K to continue shifting
                end else begin // At least one is odd
                    next_state = NORMALIZE_A;
                end
            end
            NORMALIZE_A: begin
                if ((a_reg & 1) == 0) begin // a is even
                    next_state = NORMALIZE_A; // Continue normalizing a
                end else begin // a is odd
                    next_state = COMPUTE;
                end
            end
            NORMALIZE_B: begin
                if ((b_reg & 1) == 0) begin // b is even
                    next_state = NORMALIZE_B; // Continue normalizing b
                end else begin // b is odd
                    next_state = COMPUTE;
                end
            end
            COMPUTE: begin
                if (b_reg == 0) begin
                    next_state = DONE;
                end else if (a_reg > b_reg) begin
                    next_state = NORMALIZE_B; // After subtraction, b might become even
                end else begin // b_reg > a_reg
                    next_state = NORMALIZE_A; // After subtraction, a might become even
                end
            end
            DONE: begin
                done = 1'b1;
                if (!start) begin // Reset when start goes low
                    next_state = IDLE;
                end
            end
        endcase
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            a_reg <= 0;
            b_reg <= 0;
            k_reg <= 0;
            gcd_out <= 0;
        end else begin
            case (curr_state)
                IDLE: begin
                    if (start) begin
                        a_reg <= a_in;
                        b_reg <= b_in;
                        k_reg <= 0;
                    end
                end
                INIT_K: begin
                    if ((a_reg == 0) || (b_reg == 0)) begin
                        gcd_out <= (a_reg == 0) ? b_reg : a_reg;
                    end else if (((a_reg | b_reg) & 1) == 0) begin // Both even
                        a_reg <= a_reg >> 1;
                        b_reg <= b_reg >> 1;
                        k_reg <= k_reg + 1;
                    end
                end
                NORMALIZE_A: begin
                    if ((a_reg & 1) == 0) begin // a is even
                        a_reg <= a_reg >> 1;
                    end
                end
                NORMALIZE_B: begin
                    if ((b_reg & 1) == 0) begin // b is even
                        b_reg <= b_reg >> 1;
                    end
                end
                COMPUTE: begin
                    if (a_reg > b_reg) begin
                        a_reg <= a_reg - b_reg;
                    end else begin // b_reg > a_reg
                        b_reg <= b_reg - a_reg;
                    end
                end
                DONE: begin
                    if (a_zero) begin
                        gcd_out <= b_reg << k_reg;
                    end else if (b_zero) begin
                        gcd_out <= a_reg << k_reg;
                    end else if (same) begin
                        gcd_out <= b_reg << k_reg;
                    end else begin
                        gcd_out <= a_reg << k_reg; // Final result
                    end
                end
            endcase
        end
    end

endmodule
