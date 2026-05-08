vlib work

# ============================================================
# Top-level switches
#   USE_TILE_SIM_MODEL : 1 = compile with +define+USE_TILE_SIM_MODEL
#                         0 = omit that define
#   USE_SYN_WRAPPER_TB  : 1 = compile qeciphy_syn_wrapper + qeciphy_syn_wrapper_tb
#                         0 = compile qeciphy_dual_sim_top + qeciphy_dual_sim_top_tb
# ============================================================
set USE_TILE_SIM_MODEL 0
set USE_SYN_WRAPPER_TB  0

# Build the optional E-Tile sim model define string used throughout
if { $USE_TILE_SIM_MODEL } {
    set TILE_SIM_MODEL_DEF "+define+ETILE_SIM_MODEL"
} else {
    set TILE_SIM_MODEL_DEF ""
}

set USER_DEFINED_VERILOG_COMPILE_OPTIONS "+define+IP7581SERDES_UX_SIMSPEED +define+SRC_SPEC_SPEED_UP +define+SIM"

# Library files
vlog ../../../../src/qeciphy_build_cfg_pkg.sv
vlog ../../../../lib/riv_async_fifo/src/riv_async_fifo_cdc.sv
vlog ../../../../lib/riv_async_fifo/src/riv_async_fifo_cdc.sv
vlog ../../../../lib/riv_async_fifo/src/riv_async_fifo.sv
vlog ../../../../lib/riv_async_fifo/src/riv_async_fifo_ctl.sv
vlog ../../../../lib/riv_async_fifo/src/riv_async_fifo_mem.sv
vlog ../../../../lib/riv_counter/src/riv_counter.sv
vlog ../../../../lib/riv_synchronizer_2ff/src/riv_synchronizer_2ff.sv
vlog ../../../../lib/riv_counter/src/riv_counter_prim.sv

# Core QECIPHY source
vlog ../../../../src/qeciphy_pkg.sv
vlog ../../../../src/qeciphy_gtx_common.sv
vlog ../../../../src/qeciphy_crc_compute.sv
vlog ../../../../src/qeciphy_crc_check.sv
vlog ../../../../src/qeciphy_crc16_ibm3740.sv
vlog ../../../../src/qeciphy_crc8_smbus.sv
vlog ../../../../src/qeciphy_rx_monitor.sv
vlog ../../../../src/qeciphy_rx_boundary_gen.sv
vlog ../../../../src/qeciphy_rx_controller.sv
vlog ../../../../src/qeciphy_tx_boundary_gen.sv
vlog ../../../../src/qeciphy_tx_packet_gen.sv
vlog ../../../../src/qeciphy_tx_controller.sv
vlog ../../../../src/qeciphy_tx_64b_to_32b.sv
vlog ../../../../src/qeciphy_rx_comma_detect.sv
vlog ../../../../src/qeciphy_rx_32b_to_64b.sv
vlog +acc ../../../../src/qeciphy_serdes.sv
vlog ../../../../src/qeciphy_rx_channeldecoder.sv
vlog ../../../../src/qeciphy_tx_channelencoder.sv
vlog ../../../../src/qeciphy_controller.sv
vlog ../../../../src/qeciphy_cdc.sv
vlog ../../../../src/qeciphy_error_handler.sv
vlog ../../../../src/qeciphy_resetcontroller.sv

# Soft PCS (8b10b + word aligner)
vlog ../../../../src/soft_pcs/eth_8b10b_enc_a.v
vlog ../../../../src/soft_pcs/eth_8b10b_dec_a.v
vlog ../../../../src/soft_pcs/eth_8b10b_enc_x4_a.v
vlog ../../../../src/soft_pcs/eth_8b10b_dec_x4_a.v
vlog ../../../../src/soft_pcs/qeciphy_word_align.sv

# Tile simulation model (used under +define+SIM)
vlog +acc ../../../../example_designs/de10/tb/qeciphy_etile_sim_model.sv

# GT wrappers
vlog +acc ../../../../src/qeciphy_gt_altera.sv $TILE_SIM_MODEL_DEF
vlog ../../../../src/qeciphy_gt_xilinx.sv
vlog +acc ../../../../src/qeciphy_gt_wrapper.sv

# Top-level
#Include dir needed for qeciphy_build_pkg
vlog +acc ../../../../src/QECIPHY.sv +incdir+../../../../src/ $TILE_SIM_MODEL_DEF

# Example designs and testbenches
if { $USE_SYN_WRAPPER_TB } {
    vlog +acc ../../../../example_designs/de10/src/qeciphy_syn_wrapper.sv $TILE_SIM_MODEL_DEF
    vlog +acc ../../../../example_designs/de10/tb/qeciphy_syn_wrapper_tb.sv $TILE_SIM_MODEL_DEF
    set TB_TOP work.qeciphy_syn_wrapper_tb
} else {
    vlog ../../../../example_designs/de10/src/qeciphy_dual_wrapper.sv
    vlog ../../../../example_designs/de10/src/qeciphy_dual_sim_top.sv $TILE_SIM_MODEL_DEF
    vlog ../../../../example_designs/de10/tb/qeciphy_dual_sim_top_tb.sv $TILE_SIM_MODEL_DEF
    set TB_TOP work.qeciphy_dual_sim_top_tb
}

ld -t fs $TB_TOP

if { $USE_SYN_WRAPPER_TB }{
    do wave_syn_tb.do
}
else{
    do wave_dual_tb.do
}
set StdArithNoWarnings 1
run 1500us

simstats