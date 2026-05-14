onerror {resume}
quietly WaveActivateNextPane {} 0

# -- GT Altera wrapper signals (Instance 1) --
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/gt_ref_clk_i
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/f_clk_i
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/gt_rst_n_i
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rst
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/gt_power_good_o
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_clk_o
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_clk_2x_o
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_clk_o
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_clk_2x_o
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_tdata_i
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_tdata_charisk_i
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_encoded
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_parallel_data
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_tdata_o
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_parallel_data
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_unaligned
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/word_aligner_data_out
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_byte_aligned
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_datapath_resetn
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/gt_tx_rst_done_o
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/gt_rx_rst_done_o
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_ready
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_ready
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_reset_ack
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_reset_ack
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_pll_locked
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_freqlocked
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_reset_sync
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_reset_active
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_clkout2
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_clkout2
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/tx_reset_phy
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_serdes/i_qeciphy_gt_wrapper/gen_altera/i_qeciphy_gt_altera/rx_reset_phy

# -- QECIPHY controller --
add wave -noupdate /qeciphy_syn_wrapper_tb/i_qeciphy_syn_wrapper/i_QECIPHY/i_qeciphy_controller/*

TreeUpdate [SetDefaultTree]
WaveRestoreCursors {{Cursor 1} {0 fs} 0} {{Cursor 2} {50 us} 0}
quietly wave cursor active 1
configure wave -namecolwidth 150
configure wave -valuecolwidth 100
configure wave -justifyvalue left
configure wave -signalnamewidth 1
configure wave -snapdistance 10
configure wave -datasetprefix 0
configure wave -rowmargin 4
configure wave -childrowmargin 2
configure wave -gridoffset 0
configure wave -gridperiod 1
configure wave -griddelta 40
configure wave -timeline 0
configure wave -timelineunits fs
update
WaveRestoreZoom {0 fs} {100 us}
