import le_types::*;
import params::*;
import uvm_pkg::*;

//parameters
localparam DATA_WIDTH = 256;

//Interface for AES_CBC_MAC Conditioner
interface aes_cbc_mac_interface (input bit clk);
    logic rst_n;

    logic start;
    logic done;

    logic [(DATA_WIDTH/2)-1:0] key;
    logic [DATA_WIDTH-1:0] message;
    logic [DATA_WIDTH-1:0] mac;
endinterface 

//Sequence Item for AES_CBC_MAC Conditioner 
class aes_cbc_mac_item extends uvm_sequence_item;
    `uvm_object_utils(aes_cbc_mac_item)

    rand bit    in;
    bit         out;

    virtual function string convert2str();
        return $sformatf("in=%0d, out=%0d", in, out);
    endfunction

    function new(string name = "Item");
        super.new(name);
    endfunction

endclass

//Sequence for AES_CBC_MAC Conditioner
class aes_cbc_mac_sequence extends uvm_sequence;
    `uvm_object_utils(aes)

endclass


//Scoreboard for AES_CBC_MAC Conditioner
class aes_cbc_mac_scoreboard extends uvm_scoreboard;


endclass



//Top level module for the aes_cbc_mac_uvm
module aes_cbc_mac_uvm; 



endmodule

