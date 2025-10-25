`timescale 1ns/1ps
import le_types::*;
import params::*;
module ctr_tb;


  // Clock / Reset

  logic clk, rst_n;
  localparam int CLK_PS = 10_000; // 10 ns period with 1ps timescale
  initial begin
    clk = 0;
    forever #(CLK_PS/2) clk = ~clk;
  end

  initial begin
    rst_n = 0;
    repeat (5) @(posedge clk);
    rst_n = 1;
  end


  // DUT I/O (NEW interface)

  // Commands
  logic         instantiate_i;
  logic         reseed_i;
  logic         generate_i;
  logic [15:0]  num_blocks_i;

  // Seed interface (from conditioner in real chip; here, TB drives it)
  logic [255:0] seed_material_i;
  logic         seed_valid_i;

  // Optional additional input for post-generate update
  logic [255:0] additional_input_i;

  // Outputs
  logic         busy_o;
  logic         done_o;
  logic         random_valid_o;
  logic [127:0] random_block_o;


  // DUT instantiation (MATCHES decoupled core ports)

  aes_ctr_drbg #(
    .KEY_BITS        (128),
    .BLOCK_BITS      (128),
    .SEED_BITS       (256),
    .RESEED_INTERVAL (511)   // change if you want Intel-style 511 blocks per seed
  ) dut (
    .clk               (clk),
    .rst_n             (rst_n),

    .instantiate_i     (instantiate_i),
    .reseed_i          (reseed_i),
    .generate_i        (generate_i),
    .num_blocks_i      (num_blocks_i),

    .seed_material_i   (seed_material_i),
    .seed_valid_i      (seed_valid_i),

    .additional_input_i(additional_input_i),

    .busy_o            (busy_o),   
    .done_o            (done_o),
    .random_valid_o    (random_valid_o),
    .random_block_o    (random_block_o)
  );


  // Helpers
task automatic pulse(ref logic sig);
  sig = 1'b1;
  @(posedge clk);
  sig = 1'b0;
endtask

task automatic wait_idle();
  // Core is idle when busy_o == 0
  @(posedge clk);
  while (busy_o) @(posedge clk);
endtask


task automatic do_instantiate(input logic [255:0] seed);
  begin
    wait_idle();
    seed_material_i = seed;

    // 1-cycle instantiate pulse
    instantiate_i   = 1'b1;

    // Hold seed_valid_i for 2 cycles to guarantee capture
    seed_valid_i    = 1'b1;
    @(posedge clk);
    instantiate_i   = 1'b0;
    @(posedge clk);
    seed_valid_i    = 1'b0;

    $display("%0t : INST sent (seed_valid held 2 cycles). busy=%0b", $time, busy_o);

    wait (done_o);
    @(posedge clk);
  end
endtask


task automatic do_reseed(input logic [255:0] seed);
  begin
    wait_idle();                         
    seed_material_i = seed;

    // 1-cycle reseed pulse, hold seed_valid 2 cycles to guarantee capture
    reseed_i     = 1'b1;
    seed_valid_i = 1'b1;
    @(posedge clk);
    reseed_i     = 1'b0;
    @(posedge clk);
    seed_valid_i = 1'b0;

    // Wait for the Update to finish cleanly
    wait (done_o); 
    @(posedge clk);            // extra settle cycle
  end
endtask

task automatic do_generate(input int unsigned nblocks);
  int unsigned seen = 0;
  begin
    wait_idle();

    // Make sure num_blocks_i is stable for 1 edge BEFORE the generate pulse
    num_blocks_i = nblocks[15:0];
    @(posedge clk);

    // 1-cycle request
    generate_i = 1'b1; @(posedge clk); generate_i = 1'b0;

    // Collect until post-gen update completes
    do begin
      @(posedge clk);
      if (random_valid_o) begin
        seen++;
        $display("%0t DRBG block[%0d] = %032h", $time, seen, random_block_o);
      end
    end while (!done_o);

    @(posedge clk);  // settle
    if (seen != nblocks)
      $warning("Requested %0d blocks; observed %0d.", nblocks, seen);
  end
endtask

string out_path = "drbg_blocks.txt";
int unsigned max_blocks_to_dump = 0; // 0 = no limit

initial begin
  string p; int unsigned m;
  if ($value$plusargs("OUT=%s", p)) out_path = p;
  if ($value$plusargs("MAX=%d", m)) max_blocks_to_dump = m;
end

int fh;
int unsigned dump_count = 0;

// Open the output file once
initial begin
  fh = $fopen(out_path, "w");
  if (!fh) begin
    $error("Could not open output file '%s'", out_path);
  end else begin
    $display("[DRBG-TB] Writing blocks to %s", out_path);
  end
end

// On each random_valid_o, print and dump the 128-bit block in MSB-first hex
always_ff @(posedge clk) begin
  if (random_valid_o) begin
    dump_count++;
    // Console print (timestamp + index + hex)
    $display("%0t DRBG[%0d] = %032h", $time, dump_count, random_block_o);
    // File dump: one 32-hex-char line per block
    if (fh) $fdisplay(fh, "%032h", random_block_o);
    // Optional cap
    if (max_blocks_to_dump != 0 && dump_count >= max_blocks_to_dump) begin
      $display("[DRBG-TB] Reached MAX=%0d blocks, stopping.", max_blocks_to_dump);
      $finish;
    end
  end
end

// Flush/close on finish
final begin
  if (fh) $fclose(fh);
  $display("[DRBG-TB] Total blocks dumped: %0d", dump_count);
end

// task automatic do_reseed(input logic [255:0] seed);
//   begin
//     wait_idle();                         
//     seed_material_i = seed;
//     reseed_i        = 1'b1;
//     seed_valid_i    = 1'b1;              // should be same cycle as reseed_i
//     @(posedge clk);
//     reseed_i        = 1'b0;
//     seed_valid_i    = 1'b0;

//     wait (done_o); @(posedge clk);
//   end
// endtask

// task automatic do_generate(input int unsigned nblocks);
//   int unsigned seen = 0;
//   begin
//     wait_idle();                        
//     num_blocks_i = nblocks[15:0];
//     // 1-cycle pulse
//     generate_i   = 1'b1; @(posedge clk); generate_i = 1'b0;

//     // Collect until post-generate Update completes
//     do begin
//       @(posedge clk);
//       if (random_valid_o) begin
//         seen++;
//         $display("%0t DRBG block[%0d] = %032h", $time, seen, random_block_o);
//       end
//     end while (!done_o);

//     if (seen != nblocks)
//       $warning("Requested %0d blocks but observed %0d.", nblocks, seen);

//     @(posedge clk);
//   end
// endtask

initial begin
  // Create the FSDB in the run directory (vcs/)
  $fsdbDumpfile("aes_ctr_drbg_tb.fsdb");
  $fsdbDumpvars(0, "+all");   // use your top TB module name here
  // Optional: $fsdbDumpon;
end


// timeout check (~1 ms @ 10 ns clk)
initial begin
  time limit = 1_000_000_000_000ps;  // 1 ms = 1e9 ps
  time start = $time;

  forever begin
    @(posedge clk);
    if ($time - start >= limit) begin
      $error("timeout: busy=%0b done=%0b rand_v=%0b t=%0t", busy_o, done_o, random_valid_o, $time);
      $finish;
    end
  end
end

// Tests
initial begin
  // defaults
  instantiate_i = 0;
  reseed_i = 0;
  generate_i = 0;
  num_blocks_i = '0;
  seed_material_i = '0;
  seed_valid_i = 0;
  additional_input_i = '0;

  // Waitin for reset
  wait(rst_n);

  // Instantiate with a known seed
  do_instantiate(256'h00010203_04050607_08090A0B_0C0D0E0F__10111213_14151617_18191A1B_1C1D1E1F);


  // hanging here, stuck after instantiate tb hangin

  // Generate 7 blocks
  do_generate(4000);

  // reseed with a new seed and gen 4 more blocks
  // do_reseed(256'hA5A5A5A5_A5A5A5A5_5A5A5A5A_5A5A5A5A__01234567_89ABCDEF_FEDCBA98_76543210);
  // do_generate(4);

  $display("DRBG TB: done.");
  $finish;
end

endmodule
