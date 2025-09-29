import le_types::*;
import params::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

//parameters
localparam DATA_WIDTH = 256;

//Interface for AES_CBC_MAC Conditioner
interface aes_cbc_mac_interface (input bit clk);
    logic rst_n;

    logic start;
    logic done;

    logic [(DATA_WIDTH/2)-1:0] key;
    logic [DATA_WIDTH-1:0] message;
    logic [(DATA_WIDTH/2)-1:0] mac;
endinterface 

//Sequence Item for AES_CBC_MAC Conditioner 
class aes_cbc_mac_item extends uvm_sequence_item;
    `uvm_object_utils(aes_cbc_mac_item)

    rand logic [(DATA_WIDTH/2)-1:0] key;
    rand logic [DATA_WIDTH-1:0] message;
    logic [(DATA_WIDTH/2)-1:0] mac; 


    function new(string name = "aes_cbc_mac_item");
        super.new(name);
    endfunction

    virtual function string convert2str();
        return $sformatf("key=0x%0h, message=0x%0h, mac=0x%0h", key, message, mac);
    endfunction

endclass

//----------------------------------------------------------------------
// Sequence for AES_CBC_MAC Conditioner
//----------------------------------------------------------------------
class aes_cbc_mac_sequence extends uvm_sequence #(aes_cbc_mac_item);
    `uvm_object_utils(aes_cbc_mac_sequence)

    function new(string name = "aes_cbc_mac_sequence");
        super.new(name);
    endfunction

    virtual task body();
        `uvm_info(get_type_name(), "Starting sequence", UVM_MEDIUM)
        repeat (10) begin
            req = aes_cbc_mac_item::type_id::create("req");
            start_item(req);
            assert(req.randomize());
            finish_item(req);
        end
        `uvm_info(get_type_name(), "Finished sequence", UVM_MEDIUM)
    endtask
endclass

//----------------------------------------------------------------------
// Driver for AES_CBC_MAC Conditioner
// Reads stimulus vectors from a CSV file and drives them to the DUT.
//----------------------------------------------------------------------
class aes_cbc_mac_driver extends uvm_driver #(aes_cbc_mac_item);
    `uvm_component_utils(aes_cbc_mac_driver)

    //------------------------------------------------------------------
    // Class Properties
    //------------------------------------------------------------------
    virtual aes_cbc_mac_interface vif;

    // A struct to hold a single test vector (key, message, mac)
    // This should match the struct defined in the scoreboard for consistency.
    typedef struct {
        logic [127:0] key;
        logic [255:0] message;
        logic [127:0] mac; // Driver reads but doesn't use the mac
    } vector_t;

    // Queue to store all reference vectors loaded from the CSV file
    vector_t stimulus_vectors[$];
    
    string csv_filepath = "/groups/ece427-group1/ECE427_root/LeSCOPE/rtl/bin/aes_128_cbcmac_vectors.csv";

    //------------------------------------------------------------------
    // Methods
    //------------------------------------------------------------------
    function new(string name = "aes_cbc_mac_driver", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // Get the virtual interface from the config DB
        if (!uvm_config_db#(virtual aes_cbc_mac_interface)::get(this, "", "aes_vif", vif)) begin
            `uvm_fatal(get_type_name(), "Failed to get virtual interface in driver")
        end
        
        // Allow the filepath to be configured from the testcase
        if (!uvm_config_db#(string)::get(this, "", "csv_filepath", csv_filepath)) begin
            `uvm_info(get_type_name(), $sformatf("No filepath configured. Using default: %s", csv_filepath), UVM_MEDIUM)
        end
        
        load_vectors_from_csv();
    endfunction

    // This function loads all test vectors from the specified CSV file
    protected function void load_vectors_from_csv();
        int file_handle;
        string header_line;
        vector_t temp_vector;

        file_handle = $fopen(csv_filepath, "r");
        if (!file_handle) begin
            `uvm_fatal(get_type_name(), $sformatf("Failed to open CSV file: %s", csv_filepath))
        end

        // Read and discard the header line
        void'($fgets(header_line, file_handle));

        // Loop and read the data rows using formatted scan
        while (!$feof(file_handle)) begin
            if ($fscanf(file_handle, "%h,%h,%h\n", temp_vector.key, temp_vector.message, temp_vector.mac) == 3) begin
                stimulus_vectors.push_back(temp_vector);
            end
        end

        $fclose(file_handle);
        `uvm_info(get_type_name(), $sformatf("Loaded %0d stimulus vectors from %s.", stimulus_vectors.size(), csv_filepath), UVM_LOW)
    endfunction

    virtual task main_phase(uvm_phase phase);
        // Raise an objection to keep the phase from ending prematurely
        phase.raise_objection(this);

        // Reset the interface signals
        vif.start <= 0;
        vif.key <= '0;
        vif.message <= '0;
        @(posedge vif.clk);

        `uvm_info(get_type_name(), $sformatf("Starting to drive %0d vectors.", stimulus_vectors.size()), UVM_MEDIUM)

        // Drive each vector from the queue
        foreach (stimulus_vectors[i]) begin
            vector_t current_vector = stimulus_vectors[i];
            
            `uvm_info(get_type_name(), $sformatf("Driving vector %0d: KEY=%h, MSG=%h", i, current_vector.key, current_vector.message), UVM_HIGH)
            
            // Drive the inputs
            vif.start <= 1;
            vif.key <= current_vector.key;
            vif.message <= current_vector.message;
            @(posedge vif.clk);
            vif.start <= 0;

            // Wait for DUT to finish processing the current transaction
            wait (vif.done);
            @(posedge vif.clk);
        end
        
        `uvm_info(get_type_name(), "Finished driving all vectors.", UVM_MEDIUM)

        // Drop the objection to allow the simulation to end
        phase.drop_objection(this);
    endtask
endclass


//----------------------------------------------------------------------
// Monitor for AES_CBC_MAC Conditioner
//----------------------------------------------------------------------
class aes_cbc_mac_monitor extends uvm_monitor;
    `uvm_component_utils(aes_cbc_mac_monitor)

    virtual aes_cbc_mac_interface vif;
    uvm_analysis_port #(aes_cbc_mac_item) item_collected_port;

    function new(string name = "aes_cbc_mac_monitor", uvm_component parent = null);
        super.new(name, parent);
        item_collected_port = new("item_collected_port", this);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual aes_cbc_mac_interface)::get(this, "", "aes_vif", vif)) begin
            `uvm_fatal(get_type_name(), "Failed to get virtual interface in monitor")
        end
    endfunction

    virtual task main_phase(uvm_phase phase);
        forever begin
            aes_cbc_mac_item item = aes_cbc_mac_item::type_id::create("item");

            // Wait for a transaction to start
            @(posedge vif.clk);
            wait (vif.start);
            
            // Capture inputs
            item.key = vif.key;
            item.message = vif.message;
            
            // Wait for the transaction to complete
            wait (vif.done);

            // Capture output
            item.mac = vif.mac;

            `uvm_info(get_type_name(), $sformatf("Monitored transaction: %s", item.convert2str()), UVM_MEDIUM)
            item_collected_port.write(item);
        end
    endtask
endclass

//----------------------------------------------------------------------
// Agent containing Driver, Monitor, and Sequencer
//----------------------------------------------------------------------
class aes_cbc_mac_agent extends uvm_agent;
    `uvm_component_utils(aes_cbc_mac_agent)

    aes_cbc_mac_driver   m_driver;
    aes_cbc_mac_monitor  m_monitor;
    uvm_sequencer #(aes_cbc_mac_item) m_sequencer;

    function new(string name = "aes_cbc_mac_agent", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_sequencer = uvm_sequencer #(aes_cbc_mac_item)::type_id::create("m_sequencer", this);
        m_driver = aes_cbc_mac_driver::type_id::create("m_driver", this);
        m_monitor = aes_cbc_mac_monitor::type_id::create("m_monitor", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
    endfunction
endclass

//----------------------------------------------------------------------
// Scoreboard for AES_CBC_MAC Conditioner
// Reads expected vectors from a CSV file and compares.
//----------------------------------------------------------------------
class aes_cbc_mac_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(aes_cbc_mac_scoreboard)

    uvm_analysis_imp #(aes_cbc_mac_item, aes_cbc_mac_scoreboard) item_collected_export;

    int passed_count = 0;
    int failed_count = 0;
    
    // A struct to hold a single test vector (key, message, mac)
    typedef struct {
        logic [127:0] key;
        logic [255:0] message;
        logic [127:0] mac;
    } vector_t;

    // Queue to store all reference vectors loaded from the CSV file
    vector_t reference_vectors[$];
    string csv_filepath = "/groups/ece427-group1/ECE427_root/LeSCOPE/rtl/bin/aes_128_cbcmac_vectors.csv";

    function new(string name = "aes_cbc_mac_scoreboard", uvm_component parent = null);
        super.new(name, parent);
        item_collected_export = new("item_collected_export", this);
    endfunction

    // Build phase is used to configure the component and read the file
    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        
        // Allow the filepath to be configured from the testcase
        if (!uvm_config_db#(string)::get(this, "", "csv_filepath", csv_filepath)) begin
            `uvm_info(get_type_name(), $sformatf("No filepath configured. Using default: %s", csv_filepath), UVM_MEDIUM)
        end
        
        load_vectors_from_csv();
    endfunction

    // This function loads all test vectors from the specified CSV file
    protected function void load_vectors_from_csv();
        int file_handle;
        string header_line;
        vector_t temp_vector;

        file_handle = $fopen(csv_filepath, "r");
        if (!file_handle) begin
            `uvm_fatal(get_type_name(), $sformatf("Failed to open CSV file: %s", csv_filepath))
        end

        // Read and discard the header line: "Key (hex),Message (hex),MAC (hex)"
        void'($fgets(header_line, file_handle));

        // Loop and read the data rows using formatted scan
        while (!$feof(file_handle)) begin
            // $fscanf reads from the file stream, parsing hex values (%h) separated by commas
            if ($fscanf(file_handle, "%h,%h,%h\n", temp_vector.key, temp_vector.message, temp_vector.mac) == 3) begin
                reference_vectors.push_back(temp_vector);
            end
        end

        $fclose(file_handle);
        `uvm_info(get_type_name(), $sformatf("Loaded %0d reference vectors from %s.", reference_vectors.size(), csv_filepath), UVM_LOW)
    endfunction

    // The write function is called by the analysis port when a transaction is received
    virtual function void write(aes_cbc_mac_item item);
        vector_t expected_vector;
        logic [127:0] expected_mac;

        if (reference_vectors.size() == 0) begin
            `uvm_error(get_type_name(), "Received a transaction from DUT, but the reference vector queue is empty!")
            failed_count++;
            return;
        end

        // Get the next expected vector from the front of the queue
        expected_vector = reference_vectors.pop_front();
        expected_mac = expected_vector.mac;

        // Optional but recommended: Check that key and message match what was expected.
        // This ensures the stimulus and scoreboard are in sync.
        if (item.key !== expected_vector.key || item.message !== expected_vector.message) begin
            `uvm_warning(get_type_name(), $sformatf("Key/Message mismatch between DUT transaction and reference vector.\n  REF KEY: %h MSG: %h\n  DUT KEY: %h MSG: %h",
                                                    expected_vector.key, expected_vector.message, item.key, item.message))
        end

        // Compare the actual MAC from the DUT with the expected MAC from the file
        if (item.mac == expected_mac) begin
            `uvm_info(get_type_name(), $sformatf("SCOREBOARD PASS: MAC matches.\n  Actual  : 0x%0h\n  Expected: 0x%0h", item.mac, expected_mac), UVM_LOW)
            passed_count++;
        end else begin
            `uvm_error(get_type_name(), $sformatf("SCOREBOARD FAIL: MAC mismatch.\n  Actual  : 0x%0h\n  Expected: 0x%0h\n  Transaction: %s", item.mac, expected_mac, item.convert2str()))
            failed_count++;
        end
    endfunction
    
    // Report phase summarizes the results at the end of the simulation
    virtual function void report_phase(uvm_phase phase);
        super.report_phase(phase);
        `uvm_info(get_type_name(), $sformatf("--- Scoreboard Report ---"), UVM_NONE)
        `uvm_info(get_type_name(), $sformatf("Passed: %0d", passed_count), UVM_NONE)
        `uvm_info(get_type_name(), $sformatf("Failed: %0d", failed_count), UVM_NONE)
        `uvm_info(get_type_name(), $sformatf("-------------------------"), UVM_NONE)
    endfunction
endclass

//----------------------------------------------------------------------
// UVM Environment
//----------------------------------------------------------------------
class aes_cbc_mac_env extends uvm_env;
    `uvm_component_utils(aes_cbc_mac_env)
    
    aes_cbc_mac_agent m_agent;
    aes_cbc_mac_scoreboard m_scoreboard;

    function new(string name = "aes_cbc_mac_env", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_agent = aes_cbc_mac_agent::type_id::create("m_agent", this);
        m_scoreboard = aes_cbc_mac_scoreboard::type_id::create("m_scoreboard", this);
    endfunction

    virtual function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        m_agent.m_monitor.item_collected_port.connect(m_scoreboard.item_collected_export);
    endfunction
endclass

//----------------------------------------------------------------------
// Base Test
//----------------------------------------------------------------------
class aes_cbc_mac_base_test extends uvm_test;
    `uvm_component_utils(aes_cbc_mac_base_test)

    aes_cbc_mac_env m_env;
    virtual aes_cbc_mac_interface vif;

    function new(string name = "aes_cbc_mac_base_test", uvm_component parent = null);
        super.new(name, parent);
    endfunction

    virtual function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        m_env = aes_cbc_mac_env::type_id::create("m_env", this);

        if (!uvm_config_db#(virtual aes_cbc_mac_interface)::get(this, "uvm_test_top.*", "aes_vif", vif)) begin
            `uvm_fatal(get_type_name(), "Failed to get virtual interface in base test")
        end
    endfunction

    virtual task reset_phase(uvm_phase phase);
        super.reset_phase(phase);
        phase.raise_objection(this, "Applying reset to DUT");
        `uvm_info(get_type_name(), "Reset phase started", UVM_MEDIUM)
        
        vif.rst_n <= 1'b0;
        repeat(5) @(posedge vif.clk);
        vif.rst_n <= 1'b1;
        
        `uvm_info(get_type_name(), "Reset phase finished", UVM_MEDIUM)
        phase.drop_objection(this, "Reset applied");
    endtask

    virtual task main_phase(uvm_phase phase);
        aes_cbc_mac_sequence seq = aes_cbc_mac_sequence::type_id::create("seq");
        phase.raise_objection(this);
        seq.start(m_env.m_agent.m_sequencer);
        #100ns;
        phase.drop_objection(this);
    endtask
endclass

//----------------------------------------------------------------------
// Top level module for the aes_cbc_mac_uvm
//----------------------------------------------------------------------
module aes_cbc_mac_uvm;
    bit clk;

    // Clock generation
    initial begin
        clk = 0;
        forever #5ns clk = ~clk;
    end

    // Instantiate interface
    aes_cbc_mac_interface vif(clk);
    
    // Instantiate DUT
    aes_cbc_mac #(
        .DATA_WIDTH(DATA_WIDTH)
    ) dut (
        .clk(clk),  
        .rst_n(vif.rst_n),

        .start_i(vif.start), 
        .done_o(vif.done),

        .key_i(vif.key),
        .message_i(vif.message),
        .mac_o(vif.mac)
    );

    // Set interface in config_db for the testbench components
    initial begin
        uvm_config_db#(virtual aes_cbc_mac_interface)::set(null, "uvm_test_top.*", "aes_vif", vif);
    end
    
    // Reset generation and test execution
    initial begin
        $fsdbDumpfile("aes_dump.fsdb");
		$fsdbDumpvars(0, "+all");

        run_test("aes_cbc_mac_base_test");
    end

endmodule

