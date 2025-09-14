`timescale 1ns/1ps

module ctr_tb;
localparam int DATA_WIDTH      = 256;
localparam int KEY_BITS        = 128;
localparam int MAX_BTW_RESEEDS = 8;

logic                     clk, rst_n;

logic                     instantiate_i;
logic                     reseed_i;
logic                     generate_i;
logic [15:0] num_blocks_i;

logic [DATA_WIDTH-1:0] entropy_i;
logic [DATA_WIDTH-1:0] nonce_i;
logic [DATA_WIDTH-1:0] personalization_i;
logic [DATA_WIDTH-1:0] additional_input_i;

logic [KEY_BITS-1:0] k_df_i;

logic                     busy_o;
logic                     done_o;
logic                     random_valid_o;
logic [KEY_BITS-1:0] random_block_o;


initial begin
clk = 0;
forever #5 clk = ~clk; // 100 MHz
end

initial begin
rst_n = 0;
instantiate_i = 0;
reseed_i      = 0;
generate_i    = 0;
num_blocks_i  = 0;

entropy_i         = '0;
nonce_i           = '0;
personalization_i = '0;
additional_input_i = '0;
k_df_i            = '0;

repeat (5) @(posedge clk);
rst_n = 1;
end


aes_ctr_drbg #(
.DATA_WIDTH      (DATA_WIDTH),
.KEY_BITS        (KEY_BITS),
.MAX_BTW_RESEEDS (MAX_BTW_RESEEDS)
) dut (
.clk                 (clk),
.rst_n               (rst_n),

.instantiate_i       (instantiate_i),
.reseed_i            (reseed_i),
.generate_i          (generate_i),
.num_blocks_i        (num_blocks_i),

.entropy_i           (entropy_i),
.nonce_i             (nonce_i),
.personalization_i   (personalization_i),
.additional_input_i  (additional_input_i),

.k_df_i              (k_df_i),

.busy_o              (busy_o),
.done_o              (done_o),
.random_valid_o      (random_valid_o),
.random_block_o      (random_block_o)
);


task automatic pulse(input logic ref_signal, output logic sig);
begin
    sig = 1'b1;
    @(posedge clk);
    sig = 1'b0;
end
endtask


initial begin
$dumpfile("ctr_tb.vcd");
$dumpvars(0, ctr_tb);
end

endmodule
