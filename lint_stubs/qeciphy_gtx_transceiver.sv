// SPDX-License-Identifier: BSD-2-Clause
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
    input  wire        sysclk_in,
    input  wire        soft_reset_tx_in,
    input  wire        soft_reset_rx_in,
    input  wire        dont_reset_on_data_error_in,
    output wire        gt0_tx_fsm_reset_done_out,
    output wire        gt0_rx_fsm_reset_done_out,
    input  wire        gt0_data_valid_in,
    input  wire [ 8:0] gt0_drpaddr_in,
    input  wire        gt0_drpclk_in,
    input  wire [15:0] gt0_drpdi_in,
    output wire [15:0] gt0_drpdo_out,
    input  wire        gt0_drpen_in,
    output wire        gt0_drprdy_out,
    input  wire        gt0_drpwe_in,
    output wire [ 7:0] gt0_dmonitorout_out,
    input  wire [ 2:0] gt0_loopback_in,
    input  wire        gt0_eyescanreset_in,
    input  wire        gt0_rxuserrdy_in,
    output wire        gt0_eyescandataerror_out,
    input  wire        gt0_eyescantrigger_in,
    input  wire        gt0_rxusrclk_in,
    input  wire        gt0_rxusrclk2_in,
    output wire [31:0] gt0_rxdata_out,
    output wire [ 3:0] gt0_rxdisperr_out,
    output wire [ 3:0] gt0_rxnotintable_out,
    input  wire        gt0_gtxrxp_in,
    input  wire        gt0_gtxrxn_in,
    input  wire        gt0_rxdfelpmreset_in,
    output wire [ 6:0] gt0_rxmonitorout_out,
    input  wire [ 1:0] gt0_rxmonitorsel_in,
    output wire        gt0_rxoutclk_out,
    output wire        gt0_rxoutclkfabric_out,
    input  wire        gt0_gtrxreset_in,
    input  wire        gt0_rxpmareset_in,
    output wire [ 3:0] gt0_rxcharisk_out,
    output wire        gt0_rxresetdone_out,
    input  wire        gt0_gttxreset_in,
    input  wire        gt0_txuserrdy_in,
    input  wire        gt0_txusrclk_in,
    input  wire        gt0_txusrclk2_in,
    input  wire [31:0] gt0_txdata_in,
    output wire        gt0_gtxtxn_out,
    output wire        gt0_gtxtxp_out,
    output wire        gt0_txoutclk_out,
    output wire        gt0_txoutclkfabric_out,
    output wire        gt0_txoutclkpcs_out,
    input  wire [ 3:0] gt0_txcharisk_in,
    input  wire        gt0_txpmareset_in,
    output wire        gt0_txresetdone_out,
    input  wire        gt0_qplllock_in,
    input  wire        gt0_qpllrefclklost_in,
    output wire        gt0_qpllreset_out,
    input  wire        gt0_qplloutclk_in,
    input  wire        gt0_qplloutrefclk_in,
    input  wire        gt0_rxpcommaalignen_in,
    input  wire        gt0_rxmcommaalignen_in,
    output wire        gt0_rxbyteisaligned_out,
    output wire        gt0_rxbyterealign_out,
    output wire        gt0_rxcommadet_out
);

   assign gt0_tx_fsm_reset_done_out = '0;
   assign gt0_rx_fsm_reset_done_out = '0;
   assign gt0_drpdo_out = '0;
   assign gt0_drprdy_out = '0;
   assign gt0_dmonitorout_out = '0;
   assign gt0_eyescandataerror_out = '0;
   assign gt0_rxdata_out = '0;
   assign gt0_rxdisperr_out = '0;
   assign gt0_rxnotintable_out = '0;
   assign gt0_rxmonitorout_out = '0;
   assign gt0_rxoutclk_out = '0;
   assign gt0_rxoutclkfabric_out = '0;
   assign gt0_rxcharisk_out = '0;
   assign gt0_rxresetdone_out = '0;
   assign gt0_gtxtxn_out = '0;
   assign gt0_gtxtxp_out = '0;
   assign gt0_txoutclk_out = '0;
   assign gt0_txoutclkfabric_out = '0;
   assign gt0_txoutclkpcs_out = '0;
   assign gt0_txresetdone_out = '0;
   assign gt0_qpllreset_out = '0;
   assign gt0_rxbyteisaligned_out = '0;
   assign gt0_rxbyterealign_out = '0;
   assign gt0_rxcommadet_out = '0;

endmodule
