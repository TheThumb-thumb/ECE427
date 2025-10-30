SHELL = /bin/bash -o pipefail
export TSMC65RF_PDK_IC6=/ece498hk/libs/T65GP_RFMIM_2fF_1P0V_2P5V_1p9m_6X1Z1U_ALRDL_OA61_PDK

export TOP_DIR = $(PWD)

#TOP_TB_SRCS   	:= $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/top_tb.sv      $(PWD)/hvl/example_sram.v $(shell find $(PWD)/hdl/ -name '*.sv')
TOP_TB_SRCS   	:= $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/top_tb.sv      $(PWD)/hvl/example_sram.v $(PWD)/hdl/top.sv
TOP_TB_IO_SRCS   	:= $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/top_io_tb.sv      $(PWD)/hvl/example_sram.v $(PWD)/hdl/top_io.sv

TOP_TB_SRCS_DEBUG   	:= $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/top_debug_tb.sv      $(PWD)/hvl/example_sram.v $(PWD)/hdl/top.sv

TOP_TB_SRCS_CONDITIONER   	:= $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/conditioner_debug_tb.sv      $(PWD)/hvl/example_sram.v $(PWD)/hdl/top.sv



AES_CBC_MAC_TB_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/aes_cbc_mac_tb.sv
AES_CBC_MAC_UVM_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/uvm/aes_cbc_mac_uvm.sv
CONDITIONER_SRCS = $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/conditioner_basic_tb.sv
DRBG_TB_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/aes_ctr_drbg_tb.sv
DRBG_WRAP_TB_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/drbg_wrapper_tb.sv
OHT_TB_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/oht_tb.sv $(PWD)/hdl/Online_Health_Test.sv
OHT_TOP_TB_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/oht_top_tb.sv
OHTJ_TB_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/ohtj_tb.sv $(PWD)/hdl/ohtJ.sv
SRAM_TB_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/sram_tb.sv $(PWD)/sram_rf/oht_dp_sram/verilog/oht_dp_sram.v
TRIVIUM_TB_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/trivium_tb.sv $(PWD)/hdl/trivium.sv $(PWD)/hdl/trivium_top.sv
QUE_TB_SRCS := $(shell find $(PWD)/pkg/ -name '*.sv') $(PWD)/hvl/que_tb.sv $(PWD)/hdl/fifo.sv
SYNTH_TB_SRCS 	:= $(PWD)/hvl/top_tb_post.sv $(PWD)/hvl/example_sram.v $(PWD)/../syn/synout/top.gate.v $(TSMC65RF_PDK_IC6)/stdcell_dig/fb_tsmc065gp_rvt_lvt/aci/sc-ad10/verilog/tsmc65_rvt_sc_adv10.v
PNR_TB_SRCS   	:= $(PWD)/hvl/top_tb_post.sv $(PWD)/hvl/example_sram.v $(PWD)/../pnr/pnrout/top.pnr.v  $(TSMC65RF_PDK_IC6)/stdcell_dig/fb_tsmc065gp_rvt_lvt/aci/sc-ad10/verilog/tsmc65_rvt_sc_adv10.v $(PWD)/hvl/capacitors.sv

#Michael
CONTROL_TB_SRCS := $(PWD)/hvl/control_tb.sv $(PWD)/hdl/spi.sv $(PWD)/hdl/control.sv
SPI_TB_SRCS := $(PWD)/hvl/spi_tb.sv $(PWD)/hdl/spi.sv 



export VCS_ARCH_OVERRIDE=linux
VCS_FLAGS      = -full64 -lca -sverilog -timescale=1ps/1ps -debug_acc+all -kdb -fsdb -suppress=LCA_FEATURES_ENABLED -j4 +notimingcheck -assert svaext +define+RISCV_FORMAL +define+TOP_DIR=$TOP_DIR 
VCS_FLAGS_POST = -full64 -lca -sverilog -timescale=1ps/1ps -debug_acc+all -kdb -fsdb -suppress=LCA_FEATURES_ENABLED +neg_tchk -negdelay +compsdf +mindelays +sdfverbose -j4 -fgp

#Filelists
TOP_IO_FILELIST := $(PWD)/filelists/top_io_filelist.f
TOP_FILELIST := $(PWD)/filelists/top_filelist.f
AES_CBC_MAC_FILELIST := $(PWD)/filelists/aes_cbc_mac_filelist.f
OHT_TOP_FILELIST := $(PWD)/filelists/oht_top_filelist.f
DRBG_FILELIST := $(PWD)/filelists/drbg_filelist.f

.PHONY: top
top: $(TOP_TB_SRCS)
	mkdir -p vcs
	cd vcs && vcs $(TOP_TB_SRCS) $(VCS_FLAGS) -f $(TOP_FILELIST) -l top_compile.log -o top_tb
	cd vcs && ./top_tb -l top_simulation.log

.PHONY: top_io
top_io: $(TOP_TB_IO_SRCS)
	mkdir -p vcs
	cd vcs && vcs $(TOP_TB_IO_SRCS) $(VCS_FLAGS) -f $(TOP_IO_FILELIST) -l top_io_compile.log -o top_io_tb
	cd vcs && ./top_io_tb -l top_io_simulation.log

# ====================  THIS IS MICHAEL'S TEST FOR DEBUG FROM TOP ===================================

.PHONY: top_debug_tb
top_debug_tb:
	mkdir -p vcs
	cd vcs && vcs $(TOP_TB_SRCS_DEBUG) $(VCS_FLAGS) -f $(TOP_FILELIST) -l top_debu_compile.log -o top_debug_tb
	cd vcs && ./top_debug_tb -l top_debug_tb.log

.PHONY: verdi_top_debug_tb
verdi_top_debug_tb:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/top_debug_tb.fsdb


# ====================  THIS IS FOR TESTING THE CONTROL MODULE INDIVIDUALLY ===================================

.PHONY: control
control:
	mkdir -p vcs
	cd vcs && vcs $(CONTROL_TB_SRCS) $(VCS_FLAGS) -l control_compile.log -o control_tb
	cd vcs && ./control_tb -l control_simulation.log

.PHONY: verdi_control
verdi_control:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/control.fsdb

# ====================  THIS IS FOR TESTING THE CONDITIONER IN DEBUG MODE ===================================

.PHONY: conditioner_debug
conditioner_debug:
	mkdir -p vcs
	cd vcs && vcs $(TOP_TB_SRCS_CONDITIONER) $(VCS_FLAGS) -f $(TOP_FILELIST) -l conditioner_debug_tb.log -o conditioner_debug_tb
	cd vcs && ./conditioner_debug_tb -l conditioner_debug_tb.log

.PHONY: verdi_conditioner_debug
verdi_conditioner_debug:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/conditioner_debug_tb.fsdb


# ====================  THIS IS FOR TESTING THE SPI MODULE INDIVIDUALLY  ===================================

.PHONY: verdi_spi
verdi_spi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/spi_tb.fsdb

.PHONY: spi
spi:
	mkdir -p vcs
	cd vcs && vcs $(SPI_TB_SRCS) $(VCS_FLAGS) -l spi_compile.log -o spi_tb
	cd vcs && ./spi_tb -l spi_simulation.log


# ====================  THIS IS FOR TESTING THE DRBG WRAPPER INDIVIDUALLY  ===================================
.PHONY: drbg_wrap
drbg_wrap:
	mkdir -p vcs
	cd vcs && vcs $(DRBG_WRAP_TB_SRCS) $(VCS_FLAGS) -f $(DRBG_FILELIST) -l top_compile.log -o drbg_wrapper_tb
	cd vcs && ./drbg_wrapper_tb -l top_simulation.log

.PHONY: drbg_wrap_verdi
drbg_wrap_verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/drbg_wrapper_tb.fsdb


.PHONY: aes_cbc_mac
aes_cbc_mac:
	mkdir -p vcs
	cd vcs && vcs $(AES_CBC_MAC_TB_SRCS) $(VCS_FLAGS) -f $(AES_CBC_MAC_FILELIST) -l top_compile.log -o aes_cbc_mac_tb
	cd vcs && ./aes_cbc_mac_tb -l top_simulation.log

.PHONY: conditioner
conditioner:
	mkdir -p vcs
	cd vcs && vcs $(CONDITIONER_SRCS) $(VCS_FLAGS) -f $(AES_CBC_MAC_FILELIST) -l top_compile.log -o conditioner_basic_tb
	cd vcs && ./conditioner_basic_tb -l top_simulation.log	

.PHONY: aes_cbc_mac_uvm
aes_cbc_mac_uvm:
	mkdir -p vcs
	cd vcs && vcs $(AES_CBC_MAC_UVM_SRCS) $(VCS_FLAGS) -f $(AES_CBC_MAC_FILELIST) -l top_compile.log -o aes_cbc_mac_uvm -ntb_opts uvm
	cd vcs && ./aes_cbc_mac_uvm -l top_simulation.log

.PHONY: drbg
drbg:
	mkdir -p vcs
	cd vcs && vcs $(DRBG_TB_SRCS) $(VCS_FLAGS) -f $(DRBG_FILELIST) -l top_compile.log -o aes_ctr_drbg_tb
	cd vcs && ./aes_ctr_drbg_tb -l top_simulation.log
	


.PHONY: oht_top
oht_top:
	mkdir -p vcs
	cd vcs && vcs $(OHT_TOP_TB_SRCS) $(VCS_FLAGS) -f $(OHT_TOP_FILELIST) -l top_compile.log -o oht_top_tb
	cd vcs && ./oht_top_tb -l top_simulation.log

.PHONY: oht
oht:
	mkdir -p vcs
	cd vcs && vcs $(OHT_TB_SRCS) $(VCS_FLAGS) -o oht_tb
	cd vcs && ./oht_tb -l top_simulation.log

.PHONY: ohtj
ohtj:
	mkdir -p vcs
	cd vcs && vcs $(OHTJ_TB_SRCS) $(VCS_FLAGS) -o ohtj_tb
	cd vcs && ./ohtj_tb -l top_simulation.log

.PHONY: trivium
trivium:
	mkdir -p vcs
	cd vcs && vcs $(TRIVIUM_TB_SRCS) $(VCS_FLAGS) -l top_compile.log -o trivium_tb
	cd vcs && ./trivium_tb -l top_simulation.log

.PHONY: que
que:
	mkdir -p vcs
	cd vcs && vcs $(QUE_TB_SRCS) $(VCS_FLAGS) -l top_compile.log -o que_tb
	cd vcs && ./que_tb -l top_simulation.log

.PHONY: sram
sram:
	mkdir -p vcs
	cd vcs && vcs $(SRAM_TB_SRCS) $(VCS_FLAGS) -o sram_tb
	cd vcs && ./sram_tb -l top_simulation.log

vcs/synth_tb: $(SYNTH_TB_SRCS)
	mkdir -p vcs
	cd vcs && vcs $(SYNTH_TB_SRCS) $(VCS_FLAGS_POST) +notimingcheck -l synth_compile.log -o synth_tb
	cd vcs && ./synth_tb -l synth_simulation.log

vcs/pnr_tb: $(PNR_TB_SRCS)
	mkdir -p vcs
	cd vcs && vcs $(PNR_TB_SRCS) $(VCS_FLAGS_POST) +notimingcheck -l synth_compile.log -o pnr_tb
	cd vcs && ./pnr_tb -l pnr_simulation.log

.PHONY: verdi
verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/dump.fsdb

.PHONY: top_io_verdi
top_io_verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/top_io_dump.fsdb

.PHONY: aes_verdi
aes_verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/aes_dump.fsdb

.PHONY: oht_verdi
oht_verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/oht_dump.fsdb

.PHONY: ohtj_verdi
ohtj_verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/ohtj_dump.fsdb

.PHONY: drbg_verdi
drbg_verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/aes_ctr_drbg_tb.fsdb


.PHONY: oht_top_verdi
oht_top_verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/oht_top_dump.fsdb

.PHONY: sram_verdi
sram_verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/sram_dump.fsdb

.PHONY: tri_verdi
tri_verdi:
	mkdir -p verdi
	cd verdi && $(VERDI_HOME)/bin/verdi -ssf $(PWD)/vcs/trivium_dump.fsdb

.PHONY: clean
clean:
	rm -rf vcs verdi