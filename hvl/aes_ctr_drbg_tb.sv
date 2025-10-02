`timescale 1ns/1ps

// -----------------------------------------------------------------------------
// Testbench: aes_ctr_drbg_tb.sv
//   +NUM=<nblocks>                           (default 8)
//   +ENTROPY=<64hex> +NONCE=<64hex> +PERS=<64hex>  (each 256-bit hex)
//   +KDF=<32hex>                             (128-bit hex)
//   +ADDL=<64hex>                            (256-bit hex, optional; default 0)
//   Example:
//     +NUM=16 +KDF=000102...1f +ENTROPY=... +NONCE=... +PERS=... +ADDL=...
// Output : writes "drbg_out.hex" (one 128-bit hex per line, MSB first)
// -----------------------------------------------------------------------------
module ctr_tb;

  localparam int DATA_WIDTH = 256;
  localparam int KEY_BITS   = 128;

  // io
  logic                   clk, rst_n;
  logic                   instantiate_i, reseed_i, generate_i;
  logic [15:0]            num_blocks_i;
  logic [DATA_WIDTH-1:0]  entropy_i, nonce_i, personalization_i, additional_input_i;
  logic [KEY_BITS-1:0]    k_df_i;
  logic                   busy_o, done_o, random_valid_o;
  logic [KEY_BITS-1:0]    random_block_o;

  // clk & rst
  initial begin
    clk = 0;
    forever #5 clk = ~clk; // 100 MHz
  end

  initial begin
    rst_n = 0;
    instantiate_i = 0; reseed_i = 0; generate_i = 0;
    num_blocks_i  = 0;
    entropy_i = '0; nonce_i = '0; personalization_i = '0; additional_input_i = '0;
    k_df_i = '0;
    repeat (8) @(posedge clk);
    rst_n = 1;
  end

  // DUT
  aes_ctr_drbg #(
    .DATA_WIDTH(256),
    .KEY_BITS  (128)
  ) dut (
    .clk(clk), .rst_n(rst_n),
    .instantiate_i(instantiate_i),
    .reseed_i(reseed_i),
    .generate_i(generate_i),
    .num_blocks_i(num_blocks_i),
    .entropy_i(entropy_i),
    .nonce_i(nonce_i),
    .personalization_i(personalization_i),
    .additional_input_i(additional_input_i),
    .k_df_i(k_df_i),
    .busy_o(busy_o),
    .done_o(done_o),
    .random_valid_o(random_valid_o),
    .random_block_o(random_block_o)
  );

  // +args
  int unsigned NUM;
  initial begin
    if (!$value$plusargs("NUM=%d", NUM)) NUM = 8;
  end

  // grab big hex
  function automatic bit get_hex256(string name, output logic [255:0] v);
    string fmt; fmt = {name, "=%h"};
    if ($value$plusargs(fmt, v)) return 1;
    v = '0; return 0;
  endfunction
  function automatic bit get_hex128(string name, output logic [127:0] v);
    string fmt; fmt = {name, "=%h"};
    if ($value$plusargs(fmt, v)) return 1;
    v = '0; return 0;
  endfunction

  // plusargs
  initial begin
    void'(get_hex256("ENTROPY",        entropy_i));
    void'(get_hex256("NONCE",          nonce_i));
    void'(get_hex256("PERS",           personalization_i));
    void'(get_hex256("ADDL",           additional_input_i));
    void'(get_hex128("KDF",            k_df_i));
  end

  // outs file
  int fh;
  initial begin
    fh = $fopen("drbg_out.hex", "w");
    if (fh == 0) begin
      $fatal(1, "Failed to open drbg_out.hex");
    end
  end

  // get outs
  always @(posedge clk) begin
    if (random_valid_o) begin
      // Write MSB-first 128-bit word
      $fdisplay(fh, "%032h", random_block_o);
    end
  end

  // test1
  initial begin : main
    @(posedge rst_n);

    // instan
    instantiate_i <= 1'b1;
    num_blocks_i  <= NUM[15:0];
    @(posedge clk);
    instantiate_i <= 1'b0;

    // Wait instantiate done
    wait(done_o);
    @(posedge clk);

    // create n blocs
    generate_i <= 1'b1;
    @(posedge clk);
    generate_i <= 1'b0;

    // Wait until post-generate Update finish
    wait(done_o);
    @(posedge clk);

  
    // reseed_i <= 1'b1; @(posedge clk); reseed_i <= 1'b0;
    // wait(done_o); @(posedge clk);
    // generate_i <= 1'b1; @(posedge clk); generate_i <= 1'b0;
    // wait(done_o); @(posedge clk);

    // Wrap 
    #50;
    $fclose(fh);
    $display("[%0t] CTR_DRBG TB done, out in drbg_out.hex", $time);
    $finish;
  end


endmodule
