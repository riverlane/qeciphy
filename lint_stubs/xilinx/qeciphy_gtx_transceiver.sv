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
    input  logic        sysclk_in,
    input  logic        soft_reset_tx_in,
    input  logic        soft_reset_rx_in,
    input  logic        dont_reset_on_data_error_in,
    output logic        gt0_tx_fsm_reset_done_out,
    output logic        gt0_rx_fsm_reset_done_out,
    input  logic        gt0_data_valid_in,
    input  logic [ 8:0] gt0_drpaddr_in,
    input  logic        gt0_drpclk_in,
    input  logic [15:0] gt0_drpdi_in,
    output logic [15:0] gt0_drpdo_out,
    input  logic        gt0_drpen_in,
    output logic        gt0_drprdy_out,
    input  logic        gt0_drpwe_in,
    output logic [ 7:0] gt0_dmonitorout_out,
    input  logic [ 2:0] gt0_loopback_in,
    input  logic        gt0_eyescanreset_in,
    input  logic        gt0_rxuserrdy_in,
    output logic        gt0_eyescandataerror_out,
    input  logic        gt0_eyescantrigger_in,
    input  logic        gt0_rxusrclk_in,
    input  logic        gt0_rxusrclk2_in,
    output logic [31:0] gt0_rxdata_out,
    output logic [ 3:0] gt0_rxdisperr_out,
    output logic [ 3:0] gt0_rxnotintable_out,
    input  logic        gt0_gtxrxp_in,
    input  logic        gt0_gtxrxn_in,
    input  logic        gt0_rxdfelpmreset_in,
    output logic [ 6:0] gt0_rxmonitorout_out,
    input  logic [ 1:0] gt0_rxmonitorsel_in,
    output logic        gt0_rxoutclk_out,
    output logic        gt0_rxoutclkfabric_out,
    input  logic        gt0_gtrxreset_in,
    input  logic        gt0_rxpmareset_in,
    output logic [ 3:0] gt0_rxcharisk_out,
    output logic        gt0_rxresetdone_out,
    input  logic        gt0_gttxreset_in,
    input  logic        gt0_txuserrdy_in,
    input  logic        gt0_txusrclk_in,
    input  logic        gt0_txusrclk2_in,
    input  logic [31:0] gt0_txdata_in,
    output logic        gt0_gtxtxn_out,
    output logic        gt0_gtxtxp_out,
    output logic        gt0_txoutclk_out,
    output logic        gt0_txoutclkfabric_out,
    output logic        gt0_txoutclkpcs_out,
    input  logic [ 3:0] gt0_txcharisk_in,
    input  logic        gt0_txpmareset_in,
    output logic        gt0_txresetdone_out,
    input  logic        gt0_qplllock_in,
    input  logic        gt0_qpllrefclklost_in,
    output logic        gt0_qpllreset_out,
    input  logic        gt0_qplloutclk_in,
    input  logic        gt0_qplloutrefclk_in,
    input  logic        gt0_rxpcommaalignen_in,
    input  logic        gt0_rxmcommaalignen_in,
    output logic        gt0_rxbyteisaligned_out,
    output logic        gt0_rxbyterealign_out,
    output logic        gt0_rxcommadet_out
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
