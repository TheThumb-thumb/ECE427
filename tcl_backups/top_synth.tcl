source dc_warn.tcl

set hdlin_ff_always_sync_set_reset true
set hdlin_ff_always_async_set_reset false
set hdlin_infer_multibit default_all
set hdlin_check_no_latch true
set hdlin_auto_save_templates true
# set power_enable_minpower true
set_host_options -max_cores 4
set_app_var report_default_significant_digits 6
set design_toplevel top_io

get_license DC-Ultra-Features
get_license DC-Ultra-Opt

set SynopsysInstall [getenv "DCROOT"]
set search_path [list . \
   [format "%s%s" $SynopsysInstall /libraries/syn] \
   [format "%s%s" $SynopsysInstall /dw/sim_ver \
   ]]

set symbol_library [list generic.sdb]
set synthetic_library [list dw_foundation.sldb]

define_design_lib WORK -path ./work

define_name_rules nameRules -restricted "!@#$%^&*()\\-" -case_insensitive

set cell_path [getenv TSMC_DB_DIR]
set search_path [concat $search_path $cell_path]

set alib_library_analysis_path ./

set verilogout_show_unconnected_pins "true"

set target_library [format "%s" [getenv TSMC_DB_FAST]]

set sram_library [getenv SRAM_DB_FAST]

set link_library [concat [concat [concat "*" $target_library] $synthetic_library] $sram_library]

set top_dir_path /groups/ece427-group1/ECE427_root/LeSCOPE/rtl 

set modules [list \
   $top_dir_path/pkg/types.sv \
   $top_dir_path/hdl/sbox.sv \
   $top_dir_path/hdl/aes_round.sv \
   $top_dir_path/hdl/aes_round_final.sv \
   $top_dir_path/hdl/key_schedule.sv \
   $top_dir_path/hdl/aes_core.sv \
   $top_dir_path/hdl/aes_cbc_mac.sv \
   $top_dir_path/hdl/lru_arbiter_3.sv \
   $top_dir_path/hdl/conditioner.sv \
   $top_dir_path/hdl/aes_ctr_drbg.sv \
   $top_dir_path/hdl/drbg_wrapper.sv \
   $top_dir_path/hdl/ohtJ.sv \
   $top_dir_path/hdl/Online_Health_Test.sv \
   $top_dir_path/hdl/oht_aes_shifter.sv \
   $top_dir_path/hdl/fiao.sv \
   $top_dir_path/hdl/OHT_top.sv \
   $top_dir_path/hdl/spi.sv \
   $top_dir_path/hdl/control.sv \
   $top_dir_path/hdl/oht_sram_mux.sv \
   $top_dir_path/hdl/entropy_oht_mux.sv \
   $top_dir_path/hdl/output_buffer.sv \
   $top_dir_path/hdl/trivium.sv \
   $top_dir_path/hdl/trivium_top.sv \
   $top_dir_path/hdl/output_buffer.sv \
   $top_dir_path/hdl/iopad_stub.sv \
   $top_dir_path/hdl/io.sv \
   $top_dir_path/hdl/top.sv \
   $top_dir_path/hdl/rng_temp_ctrl.v \
   $top_dir_path/hdl/top_io.sv
]


foreach module $modules {
   puts "analyzing $module"
   analyze -library WORK -format sverilog "${module}"
}

elaborate $design_toplevel
current_design $design_toplevel

set_wire_load_model -name tsmc65_wl10

set_dont_touch [get_cells mixed_IC/oht_inst_0/rng_storage]

create_clock -name sdc_top_clk -period 4.5 -waveform {0 2.25} [get_pins mixed_IC/clk] 
set_clock_uncertainty 0.1 sdc_top_clk

create_generated_clock -name sdc_analog_clk -divide_by 1 -source mixed_IC/clk [get_ports analog_clk[*]]

create_generated_clock -name sdc_slow_clk -divide_by 2 -source mixed_IC/clk [get_pins mixed_IC/slow_clk]

# additional shit we hope works
# set_optimize_register_move true
# set_max_transition 0.5 [current_design]


set_fix_hold sdc_top_clk
set_fix_hold sdc_analog_clk
set_fix_hold sdc_slow_clk

set_input_delay -clock sdc_top_clk -max 1.5 rst_n_io
set_input_delay -clock sdc_top_clk -max 1.5 rand_req_io
set_input_delay -clock sdc_top_clk -max 1.5 rand_req_type_io[*]
set_input_delay -clock sdc_top_clk -max 1.5 ss_n_io
set_input_delay -clock sdc_top_clk -max 1.5 mosi_io
set_input_delay -clock sdc_top_clk -max 1.5 debug_io
set_input_delay -clock sdc_top_clk -max 1.5 output_to_input_direct_io
set_input_delay -clock sdc_top_clk -max 1.5 input_pin_1_io
set_input_delay -clock sdc_top_clk -max 1.5 temp_debug_io

set_output_delay -clock sdc_top_clk -max 1.5 rand_byte_io[*]
set_output_delay -clock sdc_top_clk -max 1.5 rand_valid_io
set_output_delay -clock sdc_top_clk -max 1.5 miso_io
set_output_delay -clock sdc_top_clk -max 1.5 spi_data_ready_io
set_output_delay -clock sdc_top_clk -max 1.5 output_pin_2_io
set_output_delay -clock sdc_top_clk -max 1.5 output_pin_1_io

set_input_delay -clock sdc_top_clk -min 1.0 rst_n_io
set_input_delay -clock sdc_top_clk -min 1.0 rand_req_io
set_input_delay -clock sdc_top_clk -min 1.0 rand_req_type_io[*]
set_input_delay -clock sdc_top_clk -min 1.0 ss_n_io
set_input_delay -clock sdc_top_clk -min 1.0 mosi_io
set_input_delay -clock sdc_top_clk -min 1.0 debug_io
set_input_delay -clock sdc_top_clk -min 1.0 output_to_input_direct_io
set_input_delay -clock sdc_top_clk -min 1.0 input_pin_1_io
set_input_delay -clock sdc_top_clk -min 1.0 temp_debug_io

set_output_delay -clock sdc_top_clk -min 1.0 rand_byte_io[*]
set_output_delay -clock sdc_top_clk -min 1.0 rand_valid_io
set_output_delay -clock sdc_top_clk -min 1.0 miso_io
set_output_delay -clock sdc_top_clk -min 1.0 spi_data_ready_io
set_output_delay -clock sdc_top_clk -min 1.0 output_pin_2_io
set_output_delay -clock sdc_top_clk -min 1.0 output_pin_1_io

# set_load -pin_load 2 [all_outputs]
set_load -pin_load 2 [get_ports {rand_byte_io[*] rand_valid_io slow_clk_io miso_io spi_data_ready_io output_pin_2_io output_pin_1_io}]

link

compile_ultra -gate_clock -retime
set current_design  $design_toplevel

########################

# set viol_nets [get_nets -hierarchical { \
#     */conditioner_0/n23609 \
#     */conditioner_0/n23446 \
#     */n22141 \
#     */u_drbg_rappin_u_drbg/n12552 \
# }]

# set_max_transition 0.48 $viol_nets

# compile_ultra -gate_clock -retime 

#######################

change_names -rules verilog -hierarchy
change_names -rules nameRules -hierarchy

report_area                      > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.area.rpt"]
report_area -hier                > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.area_hierarchical.rpt"]
report_timing -delay max         > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.setup.rpt"]
report_timing -delay min         > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.hold.rpt"]
report_timing -max_path 50       > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.timing.rpt"]
report_timing_requirement        > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.timing_req.rpt"]
report_constraint                > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.constraint.rpt"]
report_attribute                 > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.attribute.rpt"]
report_constraint -all_violators > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.viol.rpt"]
check_design                     > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.check.rpt"]
report_hierarchy                 > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.hierarchy.rpt"]
report_resources                 > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.resources.rpt"]
report_reference                 > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.reference.rpt"]
report_cell                      > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.cell.rpt"]
report_power -verbose            > [format "%s%s%s%s" [getenv REPORT_DIR_TOP] "/" $design_toplevel ".gate.power.rpt"]

write_sdf [format "%s%s%s%s" [getenv SYN_OUT_DIR_TOP] "/" $design_toplevel ".gate.sdf"]
write_sdc [format "%s%s%s%s" [getenv SYN_OUT_DIR_TOP] "/" $design_toplevel ".gate.sdc"]

write -format verilog -hierarchy -output  [format "%s%s%s%s" [getenv SYN_OUT_DIR_TOP] "/" $design_toplevel ".gate.v"]

# start_gui

exit
