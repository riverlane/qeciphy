// SPDX-License-Identifier: None
// -----------------------------------------------------------------------------
// File        : qeciphy_gtx_transceiver.sv
// Description : Lint stub for Xilinx GTX transceiver module.
//               Declares the module interface for tooling convenience only.
//               No functional implementation is provided.
// 
// Copyright (c) 2025 Riverlane Ltd.
// This file is not affiliated with or endorsed by Xilinx Inc. or AMD.
// The module names and ports are reproduced solely for build compatibility.
// -----------------------------------------------------------------------------

module qeciphy_gtx_transceiver (
    input         sysclk_in,
    input         soft_reset_tx_in,
    input         soft_reset_rx_in,
    input         dont_reset_on_data_error_in,
    output        gt0_tx_fsm_reset_done_out,
    output        gt0_rx_fsm_reset_done_out,
    input         gt0_data_valid_in,
    input  [ 8:0] gt0_drpaddr_in,
    input         gt0_drpclk_in,
    input  [15:0] gt0_drpdi_in,
    output [15:0] gt0_drpdo_out,
    input         gt0_drpen_in,
    output        gt0_drprdy_out,
    input         gt0_drpwe_in,
    output [ 7:0] gt0_dmonitorout_out,
    input  [ 2:0] gt0_loopback_in,
    input         gt0_eyescanreset_in,
    input         gt0_rxuserrdy_in,
    output        gt0_eyescandataerror_out,
    input         gt0_eyescantrigger_in,
    input         gt0_rxusrclk_in,
    input         gt0_rxusrclk2_in,
    output [31:0] gt0_rxdata_out,
    output [ 3:0] gt0_rxdisperr_out,
    output [ 3:0] gt0_rxnotintable_out,
    input         gt0_gtxrxp_in,
    input         gt0_gtxrxn_in,
    input         gt0_rxdfelpmreset_in,
    output [ 6:0] gt0_rxmonitorout_out,
    input  [ 1:0] gt0_rxmonitorsel_in,
    output        gt0_rxoutclk_out,
    output        gt0_rxoutclkfabric_out,
    input         gt0_gtrxreset_in,
    input         gt0_rxpmareset_in,
    input         gt0_rxslide_in,
    output [ 3:0] gt0_rxcharisk_out,
    output        gt0_rxresetdone_out,
    input         gt0_gttxreset_in,
    input         gt0_txuserrdy_in,
    input         gt0_txusrclk_in,
    input         gt0_txusrclk2_in,
    input  [31:0] gt0_txdata_in,
    output        gt0_gtxtxn_out,
    output        gt0_gtxtxp_out,
    output        gt0_txoutclk_out,
    output        gt0_txoutclkfabric_out,
    output        gt0_txoutclkpcs_out,
    input  [ 3:0] gt0_txcharisk_in,
    input         gt0_txpmareset_in,
    output        gt0_txresetdone_out,
    input         gt0_qplllock_in,
    input         gt0_qpllrefclklost_in,
    output        gt0_qpllreset_out,
    input         gt0_qplloutclk_in,
    input         gt0_qplloutrefclk_in
);

endmodule
