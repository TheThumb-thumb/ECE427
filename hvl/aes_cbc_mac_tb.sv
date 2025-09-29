import le_types::*;
import params::*;
module aes_cbc_mac_tb;

    //------------------------------------------------------------------
    // Clock and Reset Generation
    //------------------------------------------------------------------
    logic top_clk;
    logic top_reset;

    initial top_clk = 1'b0;
    always #1ns top_clk = ~top_clk; // 500 MHz clock

    initial begin
        $fsdbDumpfile("aes_dump.fsdb");
        $fsdbDumpvars(0, "+all");
        top_reset = 1'b0; // Assert reset
        #10ns
        top_reset = 1'b1; // De-assert reset
    end

    //------------------------------------------------------------------
    // DUT Interface Signals
    //------------------------------------------------------------------
    localparam DATA_WIDTH = 256;

    logic        start_i;
    logic        done_o;
    logic [(DATA_WIDTH/2)-1:0] key_i;
    logic [DATA_WIDTH-1:0] message_i;
    logic [DATA_WIDTH-1:0] mac_o;

    //------------------------------------------------------------------
    // DUT Instantiation
    //------------------------------------------------------------------
    aes_cbc_mac #(
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk(top_clk),
        .rst_n(top_reset),
        .start_i(start_i),
        .done_o(done_o),
        .key_i(key_i),
        .message_i(message_i),
        .mac_o(mac_o)
    );

    //------------------------------------------------------------------
    // CSV-based Test Logic
    //------------------------------------------------------------------

    // A struct to hold a single test vector (key, message, mac)
    typedef struct {
        logic [127:0] key;
        logic [255:0] message;
        logic [255:0] mac;
    } vector_t;

    // Queue to store all vectors loaded from the CSV file
    vector_t test_vectors[$];
    string csv_filepath = "/groups/ece427-group1/ECE427_root/LeSCOPE/rtl/bin/encryption_data.csv";


    initial begin
        int file_handle;
        string header_line;
        vector_t temp_vector;
		vector_t current_vector;
        int passed_count = 0;
        int failed_count = 0;
		int i = 0;
		start_i = 1'b0;

        // --- 1. Load Vectors from CSV File ---
        file_handle = $fopen(csv_filepath, "r");
        if (!file_handle) begin
            $fatal(1, "Failed to open CSV file: %s", csv_filepath);
        end

        void'($fgets(header_line, file_handle)); // Read and discard header

        while (!$feof(file_handle)) begin
            if ($fscanf(file_handle, "%h,%h,%h\n", temp_vector.key, temp_vector.message, temp_vector.mac) == 3) begin
                test_vectors.push_back(temp_vector);
            end
        end
        $fclose(file_handle);
        $display("Loaded %0d test vectors from %s.", test_vectors.size(), csv_filepath);

        // --- 2. Drive and Check Each Vector ---
        wait (top_reset === 1'b1); // Wait for reset to be de-asserted
        @(posedge top_clk);

        for (i = 0; i < test_vectors.size(); i++) begin
            current_vector = test_vectors[i];
            
            $display("--- Running Vector %0d ---", i);
            $display("  Driving Key: %h", current_vector.key);
            $display("  Driving Msg: %h", current_vector.message);

            // Drive inputs
            key_i = current_vector.key;
            message_i = current_vector.message;
            start_i = 1'b1;
            @(posedge top_clk);
            #1
            start_i = 1'b0;
            key_i = '0;
            message_i = '0;

            // Wait for DUT to finish
            wait (done_o == 1'b1);
            @(posedge top_clk);

            // Check the output
            assert (mac_o == current_vector.mac) else begin
                $fatal("Assertion failed! MAC mismatch on vector %0d.\n  Expected: %h\n  Actual  : %h", i, current_vector.mac, mac_o);
                failed_count++;
            end
            
            if (mac_o == current_vector.mac) begin
                 $display("Assertion succeeded! Vector %0d matches.", i);
                 passed_count++;
            end
        end

        // --- 3. Final Report and Finish ---
        $display("\n--- Testbench Finished ---");
        $display("Passed: %0d", passed_count);
        $display("Failed: %0d", failed_count);
        $display("--------------------------");

        #100ns;
        $finish();
    end

endmodule : aes_cbc_mac_tb

