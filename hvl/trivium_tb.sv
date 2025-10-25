// import le_types::*;
// import params::*;
// module trivium_tb;

// logic clk, rst;
// initial clk = 1'b0;
// always #1ns clk = ~clk;
// initial rst = 1'b0;
    
//     logic [DATA_WIDTH-1:0] cond_in;
//     logic cond_valid, seed_req, triv_ready;
//     // stall, 
//     logic [7:0] rrand_out;
//     // logic rrand_out;

//     // assign cond_in = {$urandom(), $urandom(), $urandom(), $urandom(), $urandom()};
//     assign cond_in = 256'h2fd9a2acf377581d8ba1adbf131ab2c93aae165d;

//     // assign cond_in = 256' 
//     // 2fd9a2acf377581d8ba1    IV
//     // adbf131ab2c93aae165d    KEY
//     // adbf131ab2c93aae165d 2fd9a2acf377581d8ba1 64
//     assign cond_valid = '1;
//     // assign stall = 1'b0;

//     trivium_top dut (
//         .clk(clk),
//         .rst(rst),

//         .cond_in(cond_in),
//         .cond_valid(cond_valid),

//         .seed_req(seed_req),
//         .triv_valid(triv_ready),
//         .rrand_out(rrand_out)
//     );

// 	initial begin
// 		$fsdbDumpfile("trivium_dump.fsdb");
// 		$fsdbDumpvars(0, "+all");
// 		rst = 1'b1;
//         #10ns
// 		rst = 1'b0;
// 		#1000000ns
// 		$finish();
// 	end

//     initial begin
//         integer bytes_captured;
//         integer bytes_to_capture = 1000000; // Capture 1KB of data
//         integer outfile;
//         // --- Test Setup ---
//         // Open a text file for writing (will be overwritten on each run)
//         outfile = $fopen("rrand_output.txt", "w");
//         if (!outfile) begin
//             $display("ERROR: Failed to open output file!");
//             $finish;
//         end

//         // Setup waveform dumping for debugging
//         // $fsdbDumpfile("trivium_dump.fsdb");
//         // $fsdbDumpvars(0, "+all");

//         // --- Test Execution ---
//         // Wait for reset to complete
//         @(negedge rst);
//         $display("Reset deasserted. Starting to monitor for random data.");

//         // --- Output Capture ---
//         // Capture a specific number of random bytes
//         bytes_captured = 0;
//         while (bytes_captured < bytes_to_capture) begin
//             @(posedge clk);
//             // Only capture data when the DUT indicates it's ready
//             if (triv_ready) begin
//                 // Write one byte per line in hexadecimal format (e.g., "a5")
//                 $fwrite(outfile, "%02x\n", rrand_out);
//                 bytes_captured++;
//             end
//         end

//         // --- Test Cleanup ---
//         $display("Successfully captured %0d bytes into rrand_output.txt. Finishing simulation.", bytes_captured);
//         $finish; // End the simulation
//     end

//     // The 'final' block ensures that the output file is always closed
//     // when the simulation finishes, either normally or via $finish.
//     // final begin
//     //     if (outfile) begin
//     //         $fclose(outfile);
//     //     end
//     // end


// endmodule

// // // `timescale directive specifies the time unit and precision for the simulation
// // `timescale 1ns / 1ps

// // // Assuming these packages contain necessary type and parameter definitions
// // import le_types::*;
// // import params::*;

// // module trivium_tb;

// //     //================================================================
// //     // Signal Declarations
// //     //================================================================
// //     logic clk, rst;
// //     logic [DATA_WIDTH-1:0] cond_in;
// //     logic cond_valid, stall, seed_req, triv_ready;
// //     logic [7:0] rrand_out;
// //     integer outfile; // File handle for writing output

// //     //================================================================
// //     // Clock and Reset Generation
// //     //================================================================
// //     initial begin
// //         clk = 1'b0;
// //         forever #5ns clk = ~clk; // 100MHz clock
// //     end

// //     initial begin
// //         rst = 1'b1; // Assert reset initially
// //         #20ns;
// //         rst = 1'b0; // Deassert reset
// //     end

// //     //================================================================
// //     // DUT Input Stimulus
// //     //================================================================
// //     // For this test, inputs are held constant.
// //     // A more complex testbench might vary these over time.
// //     assign cond_in = {$urandom(), $urandom(), $urandom(), $urandom(), $urandom()};
// //     assign cond_valid = '1;
// //     assign stall = 1'b0;

// //     //================================================================
// //     // DUT Instantiation
// //     //================================================================
// //     trivium_top dut (
// //         .clk(clk),
// //         .rst(rst),

// //         .cond_in(cond_in),
// //         .cond_valid(cond_valid),
// //         .stall(stall),

// //         .seed_req(seed_req),
// //         .triv_ready(triv_ready),
// //         .rrand_out(rrand_out)
// //     );

// //     //================================================================
// //     // Main Test Sequence and Output Capture
// //     //================================================================
// //     initial begin
// //         integer bytes_captured;
// //         integer bytes_to_capture = 1024; // Capture 1KB of data

// //         // --- Test Setup ---
// //         // Open a text file for writing (will be overwritten on each run)
// //         outfile = $fopen("rrand_output.txt", "w");
// //         if (!outfile) begin
// //             $display("ERROR: Failed to open output file!");
// //             $finish;
// //         end

// //         // Setup waveform dumping for debugging
// //         $fsdbDumpfile("trivium_dump.fsdb");
// //         $fsdbDumpvars(0, trivium_tb, "+all");

// //         // --- Test Execution ---
// //         // Wait for reset to complete
// //         @(negedge rst);
// //         $display("Reset deasserted. Starting to monitor for random data.");

// //         // --- Output Capture ---
// //         // Capture a specific number of random bytes
// //         bytes_captured = 0;
// //         while (bytes_captured < bytes_to_capture) begin
// //             @(posedge clk);
// //             // Only capture data when the DUT indicates it's ready
// //             if (triv_ready) begin
// //                 // Write one byte per line in hexadecimal format (e.g., "a5")
// //                 $fwrite(outfile, "%02x\n", rrand_out);
// //                 bytes_captured++;
// //             end
// //         end

// //         // --- Test Cleanup ---
// //         $display("Successfully captured %0d bytes into rrand_output.txt. Finishing simulation.", bytes_captured);
// //         $finish; // End the simulation
// //     end

// //     // The 'final' block ensures that the output file is always closed
// //     // when the simulation finishes, either normally or via $finish.
// //     final begin
// //         if (outfile) begin
// //             $fclose(outfile);
// //         end
// //     end

// // endmodule































import le_types::*;
import params::*;
module trivium_tb;

logic clk, rst;
initial clk = 1'b0;
always #1ns clk = ~clk;
initial rst = 1'b0;
    
    logic [DATA_WIDTH-1:0] cond_in;
    logic cond_valid, seed_req, triv_ready;
    // stall, 
    logic [63:0] rrand_out;
    // logic rrand_out;

    // assign cond_in = {$urandom(), $urandom(), $urandom(), $urandom(), $urandom()};
    assign cond_in = 256'h2fd9a2acf377581d8ba1adbf131ab2c93aae165d;

    // assign cond_in = 256' 
    // 2fd9a2acf377581d8ba1    IV  H2FD
    // adbf131ab2c93aae165d      KEY
    // adbf131ab2c93aae165d 2fd9a2acf377581d8ba1 64
    assign cond_valid = '1;
    assign stall = 1'b0;

    trivium_top dut (
        .clk(clk),
        .rst(rst),

        .cond_in(cond_in),
        .cond_valid(cond_valid),
        .stall(stall),

        .seed_req(seed_req),
        .triv_valid(triv_ready),
        .rrand_out(rrand_out)
    );

	initial begin
		$fsdbDumpfile("trivium_dump.fsdb");
		$fsdbDumpvars(0, "+all");
		rst = 1'b1;
        #10ns
		rst = 1'b0;
		#1000000ns
		$finish();
	end

    initial begin
        integer bytes_captured;
        integer bytes_to_capture = 1000000; // Capture 1KB of data
        integer outfile;
        // --- Test Setup ---
        // Open a text file for writing (will be overwritten on each run)
        outfile = $fopen("rrand_output.txt", "w");
        if (!outfile) begin
            $display("ERROR: Failed to open output file!");
            $finish;
        end

        // Setup waveform dumping for debugging
        // $fsdbDumpfile("trivium_dump.fsdb");
        // $fsdbDumpvars(0, "+all");

        // --- Test Execution ---
        // Wait for reset to complete
        @(negedge rst);
        $display("Reset deasserted. Starting to monitor for random data.");

        // --- Output Capture ---
        // Capture a specific number of random bytes
        bytes_captured = 0;
        while (bytes_captured < bytes_to_capture) begin
            @(posedge clk);
            // Only capture data when the DUT indicates it's ready
            if (triv_ready) begin
                // Write one byte per line in hexadecimal format (e.g., "a5")
                $fwrite(outfile, "%016x\n", rrand_out);
                bytes_captured++;
            end
        end

        // --- Test Cleanup ---
        $display("Successfully captured %0d bytes into rrand_output.txt. Finishing simulation.", bytes_captured);
        $finish; // End the simulation
    end

    // The 'final' block ensures that the output file is always closed
    // when the simulation finishes, either normally or via $finish.
    // final begin
    //     if (outfile) begin
    //         $fclose(outfile);
    //     end
    // end


endmodule

// // `timescale directive specifies the time unit and precision for the simulation
// `timescale 1ns / 1ps

// // Assuming these packages contain necessary type and parameter definitions
// import le_types::*;
// import params::*;

// module trivium_tb;

//     //================================================================
//     // Signal Declarations
//     //================================================================
//     logic clk, rst;
//     logic [DATA_WIDTH-1:0] cond_in;
//     logic cond_valid, stall, seed_req, triv_ready;
//     logic [7:0] rrand_out;
//     integer outfile; // File handle for writing output

//     //================================================================
//     // Clock and Reset Generation
//     //================================================================
//     initial begin
//         clk = 1'b0;
//         forever #5ns clk = ~clk; // 100MHz clock
//     end

//     initial begin
//         rst = 1'b1; // Assert reset initially
//         #20ns;
//         rst = 1'b0; // Deassert reset
//     end

//     //================================================================
//     // DUT Input Stimulus
//     //================================================================
//     // For this test, inputs are held constant.
//     // A more complex testbench might vary these over time.
//     assign cond_in = {$urandom(), $urandom(), $urandom(), $urandom(), $urandom()};
//     assign cond_valid = '1;
//     assign stall = 1'b0;

//     //================================================================
//     // DUT Instantiation
//     //================================================================
//     trivium_top dut (
//         .clk(clk),
//         .rst(rst),

//         .cond_in(cond_in),
//         .cond_valid(cond_valid),
//         .stall(stall),

//         .seed_req(seed_req),
//         .triv_ready(triv_ready),
//         .rrand_out(rrand_out)
//     );

//     //================================================================
//     // Main Test Sequence and Output Capture
//     //================================================================
//     initial begin
//         integer bytes_captured;
//         integer bytes_to_capture = 1024; // Capture 1KB of data

//         // --- Test Setup ---
//         // Open a text file for writing (will be overwritten on each run)
//         outfile = $fopen("rrand_output.txt", "w");
//         if (!outfile) begin
//             $display("ERROR: Failed to open output file!");
//             $finish;
//         end

//         // Setup waveform dumping for debugging
//         $fsdbDumpfile("trivium_dump.fsdb");
//         $fsdbDumpvars(0, trivium_tb, "+all");

//         // --- Test Execution ---
//         // Wait for reset to complete
//         @(negedge rst);
//         $display("Reset deasserted. Starting to monitor for random data.");

//         // --- Output Capture ---
//         // Capture a specific number of random bytes
//         bytes_captured = 0;
//         while (bytes_captured < bytes_to_capture) begin
//             @(posedge clk);
//             // Only capture data when the DUT indicates it's ready
//             if (triv_ready) begin
//                 // Write one byte per line in hexadecimal format (e.g., "a5")
//                 $fwrite(outfile, "%02x\n", rrand_out);
//                 bytes_captured++;
//             end
//         end

//         // --- Test Cleanup ---
//         $display("Successfully captured %0d bytes into rrand_output.txt. Finishing simulation.", bytes_captured);
//         $finish; // End the simulation
//     end

//     // The 'final' block ensures that the output file is always closed
//     // when the simulation finishes, either normally or via $finish.
//     final begin
//         if (outfile) begin
//             $fclose(outfile);
//         end
//     end

// endmodule

