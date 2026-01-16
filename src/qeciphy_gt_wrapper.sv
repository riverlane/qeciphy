// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Dogancan Davutoglu, Aniket Datta

module qeciphy_gt_wrapper #(
    parameter GT_TYPE = "GTY"  // Valid values: "GTX", "GTY", "GTH"
) (
    input logic gt_ref_clk_i,

    input  logic f_clk_i,
    input  logic gt_rst_n_i,
    output logic gt_power_good_o,

    output logic        tx_clk_o,
    output logic        tx_clk_2x_o,
    input  logic [31:0] tx_tdata_i,
    output logic        gt_tx_rst_done_o,

    output logic        rx_clk_o,
    output logic        rx_clk_2x_o,
    output logic [31:0] rx_tdata_o,
    output logic        gt_rx_rst_done_o,
    output logic        rx_slide_rdy_o,
    input  logic        rx_slide_i
);

   // -------------------------------------------------------------
   // Common signal declaration
   // -------------------------------------------------------------

   logic rxoutclk;
   logic txoutclk;

   // -------------------------------------------------------------
   // GTY transceiver instantiation
   // -------------------------------------------------------------
   generate
      if (GT_TYPE == "GTY") begin : gen_GTY_transceiver
         // -------------------------------------------------------------
         // Transceiver specific declaration
         // -------------------------------------------------------------
         logic txpmaresetdone;
         logic rxpmaresetdone;
         logic userclk_tx_reset;
         logic userclk_rx_reset;
         assign userclk_tx_reset = ~txpmaresetdone;
         assign userclk_rx_reset = ~rxpmaresetdone;

         qeciphy_gty_transceiver transceiver (
             .gtwiz_userclk_tx_active_in        (~userclk_tx_reset),
             .gtwiz_userclk_rx_active_in        (~userclk_rx_reset),
             .gtwiz_reset_clk_freerun_in        (f_clk_i),
             .gtwiz_reset_all_in                (~gt_rst_n_i),
             .gtwiz_reset_tx_pll_and_datapath_in(~gt_rst_n_i),
             .gtwiz_reset_tx_datapath_in        (1'b0),
             .gtwiz_reset_rx_pll_and_datapath_in(~gt_rst_n_i),
             .gtwiz_reset_rx_datapath_in        (1'b0),
             .gtwiz_reset_rx_cdr_stable_out     (),
             .gtwiz_reset_tx_done_out           (gt_tx_rst_done_o),
             .gtwiz_reset_rx_done_out           (gt_rx_rst_done_o),
             .gtwiz_userdata_tx_in              (tx_tdata_i),
             .gtwiz_userdata_rx_out             (rx_tdata_o),
             .gtrefclk00_in                     (gt_ref_clk_i),
             .qpll0lock_out                     (),
             .qpll0outclk_out                   (),
             .qpll0outrefclk_out                (),
             .gtyrxn_in                         (),
             .gtyrxp_in                         (),
             .gtytxn_out                        (),
             .gtytxp_out                        (),
             .rx8b10ben_in                      (1'b1),
             .rxusrclk_in                       (rx_clk_2x_o),
             .rxusrclk2_in                      (rx_clk_2x_o),
             .tx8b10ben_in                      (1'b1),
             .txctrl0_in                        (16'd0),
             .txctrl1_in                        (16'd0),
             .txctrl2_in                        (8'd0),
             .txusrclk_in                       (tx_clk_2x_o),
             .txusrclk2_in                      (tx_clk_2x_o),
             .gtpowergood_out                   (gt_power_good_o),
             .rxctrl0_out                       (),
             .rxctrl1_out                       (),
             .rxctrl2_out                       (),
             .rxctrl3_out                       (),
             .rxoutclk_out                      (rxoutclk),
             .rxpmaresetdone_out                (rxpmaresetdone),
             .txoutclk_out                      (txoutclk),
             .txpmaresetdone_out                (txpmaresetdone),
             .rxsliderdy_out                    (rx_slide_rdy_o),
             .rxslide_in                        (rx_slide_i)
         );

         // -------------------------------------------------------------
         // Clock buffers
         // -------------------------------------------------------------

         // The rx_clk_2x_o is used both as rxusrclk_in and rxusrclk2_in.
         // This should be okay as they are both expected to be of the same frequency for a 32 bit datapath.
         // Please refer: https://docs.amd.com/v/u/en-US/ug578-ultrascale-gty-transceivers : Table 4-51
         BUFG_GT i_BUFG_gt_rx_clk (
             .CE     (1'b1),
             .CEMASK (1'b0),
             .CLR    (userclk_rx_reset),
             .CLRMASK(1'b0),
             .DIV    (3'b000),
             .I      (rxoutclk),
             .O      (rx_clk_2x_o)
         );

         // The rx_clk_o is used by the Channel Decoder of the QEC-Phy when converting 32 bit data into 64 bits.
         // rx_clk_o = rx_clk_2x_o/2 and they should be phase aligned.
         BUFG_GT i_BUFG_rx_clk (
             .CE     (1'b1),
             .CEMASK (1'b0),
             .CLR    (userclk_rx_reset),
             .CLRMASK(1'b0),
             .DIV    (3'b001),
             .I      (rxoutclk),
             .O      (rx_clk_o)
         );

         // The tx_clk_2x_o is used both as txusrclk_in and txusrclk2_in.
         // This should be okay as they are both expected to be of the same frequency for a 32 bit datapath.
         // Please refer: https://docs.amd.com/v/u/en-US/ug578-ultrascale-gty-transceivers : Table 3-3
         BUFG_GT i_BUFG_gt_tx_clk (
             .CE     (1'b1),
             .CEMASK (1'b0),
             .CLR    (userclk_tx_reset),
             .CLRMASK(1'b0),
             .DIV    (3'b000),
             .I      (txoutclk),
             .O      (tx_clk_2x_o)
         );

         // The tx_clk_o is used by the Channel Encoder of the QEC-Phy when converting 64 bit data into 32 bits.
         // tx_clk_o = tx_clk_2x_o/2 and they should be phase aligned.
         BUFG_GT i_BUFG_tx_clk (
             .CE     (1'b1),
             .CEMASK (1'b0),
             .CLR    (userclk_tx_reset),
             .CLRMASK(1'b0),
             .DIV    (3'b001),
             .I      (txoutclk),
             .O      (tx_clk_o)
         );

      end else if (GT_TYPE == "GTH") begin : gen_GTH_transceiver

         // -------------------------------------------------------------
         // Transceiver specific declaration
         // -------------------------------------------------------------
         logic txpmaresetdone;
         logic rxpmaresetdone;
         logic userclk_tx_reset;
         logic userclk_rx_reset;
         assign userclk_tx_reset = ~txpmaresetdone;
         assign userclk_rx_reset = ~rxpmaresetdone;

         qeciphy_gth_transceiver transceiver (
             .gtwiz_userclk_tx_active_in        (~userclk_tx_reset),
             .gtwiz_userclk_rx_active_in        (~userclk_rx_reset),
             .gtwiz_reset_clk_freerun_in        (f_clk_i),
             .gtwiz_reset_all_in                (~gt_rst_n_i),
             .gtwiz_reset_tx_pll_and_datapath_in(~gt_rst_n_i),
             .gtwiz_reset_tx_datapath_in        (1'b0),
             .gtwiz_reset_rx_pll_and_datapath_in(~gt_rst_n_i),
             .gtwiz_reset_rx_datapath_in        (1'b0),
             .gtwiz_reset_rx_cdr_stable_out     (),
             .gtwiz_reset_tx_done_out           (gt_tx_rst_done_o),
             .gtwiz_reset_rx_done_out           (gt_rx_rst_done_o),
             .gtwiz_userdata_tx_in              (tx_tdata_i),
             .gtwiz_userdata_rx_out             (rx_tdata_o),
             .gtrefclk00_in                     (gt_ref_clk_i),
             .qpll0lock_out                     (),
             .qpll0outclk_out                   (),
             .qpll0outrefclk_out                (),
             .gthrxn_in                         (),
             .gthrxp_in                         (),
             .gthtxn_out                        (),
             .gthtxp_out                        (),
             .rx8b10ben_in                      (1'b1),
             .rxusrclk_in                       (rx_clk_2x_o),
             .rxusrclk2_in                      (rx_clk_2x_o),
             .tx8b10ben_in                      (1'b1),
             .txctrl0_in                        (16'd0),
             .txctrl1_in                        (16'd0),
             .txctrl2_in                        (8'd0),
             .txusrclk_in                       (tx_clk_2x_o),
             .txusrclk2_in                      (tx_clk_2x_o),
             .gtpowergood_out                   (gt_power_good_o),
             .rxctrl0_out                       (),
             .rxctrl1_out                       (),
             .rxctrl2_out                       (),
             .rxctrl3_out                       (),
             .rxoutclk_out                      (rxoutclk),
             .rxpmaresetdone_out                (rxpmaresetdone),
             .txoutclk_out                      (txoutclk),
             .txpmaresetdone_out                (txpmaresetdone),
             .rxsliderdy_out                    (rx_slide_rdy_o),
             .rxslide_in                        (rx_slide_i)
         );

         // -------------------------------------------------------------
         // Clock buffers
         // -------------------------------------------------------------

         // The rx_clk_2x_o is used both as rxusrclk_in and rxusrclk2_in.
         // This should be okay as they are both expected to be of the same frequency for a 32 bit datapath.
         // Please refer: https://docs.amd.com/v/u/en-US/ug578-ultrascale-gty-transceivers : Table 4-51
         BUFG_GT i_BUFG_gt_rx_clk (
             .CE     (1'b1),
             .CEMASK (1'b0),
             .CLR    (userclk_rx_reset),
             .CLRMASK(1'b0),
             .DIV    (3'b000),
             .I      (rxoutclk),
             .O      (rx_clk_2x_o)
         );

         // The rx_clk_o is used by the Channel Decoder of the QEC-Phy when converting 32 bit data into 64 bits.
         // rx_clk_o = rx_clk_2x_o/2 and they should be phase aligned.
         BUFG_GT i_BUFG_rx_clk (
             .CE     (1'b1),
             .CEMASK (1'b0),
             .CLR    (userclk_rx_reset),
             .CLRMASK(1'b0),
             .DIV    (3'b001),
             .I      (rxoutclk),
             .O      (rx_clk_o)
         );

         // The tx_clk_2x_o is used both as txusrclk_in and txusrclk2_in.
         // This should be okay as they are both expected to be of the same frequency for a 32 bit datapath.
         // Please refer: https://docs.amd.com/v/u/en-US/ug578-ultrascale-gty-transceivers : Table 3-3
         BUFG_GT i_BUFG_gt_tx_clk (
             .CE     (1'b1),
             .CEMASK (1'b0),
             .CLR    (userclk_tx_reset),
             .CLRMASK(1'b0),
             .DIV    (3'b000),
             .I      (txoutclk),
             .O      (tx_clk_2x_o)
         );

         // The tx_clk_o is used by the Channel Encoder of the QEC-Phy when converting 64 bit data into 32 bits.
         // tx_clk_o = tx_clk_2x_o/2 and they should be phase aligned.
         BUFG_GT i_BUFG_tx_clk (
             .CE     (1'b1),
             .CEMASK (1'b0),
             .CLR    (userclk_tx_reset),
             .CLRMASK(1'b0),
             .DIV    (3'b001),
             .I      (txoutclk),
             .O      (tx_clk_o)
         );

      end else if (GT_TYPE == "GTX") begin : gen_GTX_transceiver
         // -------------------------------------------------------------
         // Transceiver specific declaration
         // -------------------------------------------------------------
         logic qplllock_out;
         logic qpllrefclklost_out;
         logic qpllreset_in;
         logic qplloutclk_out;
         logic qplloutrefclk_out;
         logic txoutclk_stopped;
         logic txoutclk_stopped_d1;
         logic rxoutclk_stopped;
         logic rxoutclk_stopped_d1;
         logic txoutclk_stopped_fall;
         logic rxoutclk_stopped_fall;
         logic tx_mmcm_reset;
         logic rx_mmcm_reset;
         logic rxpmaresetdone;

         qeciphy_gtx_transceiver transceiver (
             .sysclk_in                  (f_clk_i),             // input wire sysclk_in
             .soft_reset_tx_in           (1'b0),                // input wire soft_reset_tx_in
             .soft_reset_rx_in           (1'b0),                // input wire soft_reset_rx_in
             .dont_reset_on_data_error_in(1'b1),                // input wire dont_reset_on_data_error_in
             .gt0_tx_fsm_reset_done_out  (gt_tx_rst_done_o),    // output wire gt0_tx_fsm_reset_done_out
             .gt0_rx_fsm_reset_done_out  (gt_rx_rst_done_o),    // output wire gt0_rx_fsm_reset_done_out
             .gt0_data_valid_in          (rxpmaresetdone),      // input wire gt0_data_valid_in
             .gt0_drpaddr_in             (9'h00),               // input wire [8:0] gt0_drpaddr_in
             .gt0_drpclk_in              (f_clk_i),             // input wire gt0_drpclk_in
             .gt0_drpdi_in               (16'h0000),            // input wire [15:0] gt0_drpdi_in
             .gt0_drpdo_out              (),                    // output wire [15:0] gt0_drpdo_out
             .gt0_drpen_in               (1'b0),                // input wire gt0_drpen_in
             .gt0_drprdy_out             (),                    // output wire gt0_drprdy_out
             .gt0_drpwe_in               (1'b0),                // input wire gt0_drpwe_in
             .gt0_dmonitorout_out        (),                    // output wire [7:0] gt0_dmonitorout_out
             .gt0_loopback_in            (3'b000),              // input wire [2:0] gt0_loopback_in
             .gt0_eyescanreset_in        (1'b0),                // input wire gt0_eyescanreset_in
             .gt0_rxuserrdy_in           (1'b1),                // input wire gt0_rxuserrdy_in
             .gt0_eyescandataerror_out   (),                    // output wire gt0_eyescandataerror_out
             .gt0_eyescantrigger_in      (1'b0),                // input wire gt0_eyescantrigger_in
             .gt0_rxusrclk_in            (rx_clk_2x_o),         // input wire gt0_rxusrclk_in
             .gt0_rxusrclk2_in           (rx_clk_2x_o),         // input wire gt0_rxusrclk2_in
             .gt0_rxdata_out             (rx_tdata_o),          // output wire [31:0] gt0_rxdata_out
             .gt0_rxdisperr_out          (),                    // output wire [3:0] gt0_rxdisperr_out
             .gt0_rxnotintable_out       (),                    // output wire [3:0] gt0_rxnotintable_out
             .gt0_gtxrxp_in              (),                    // input wire gt0_gtxrxp_in
             .gt0_gtxrxn_in              (),                    // input wire gt0_gtxrxn_in
             .gt0_rxdfelpmreset_in       (1'b0),                // input wire gt0_rxdfelpmreset_in
             .gt0_rxmonitorout_out       (),                    // output wire [6:0] gt0_rxmonitorout_out
             .gt0_rxmonitorsel_in        (2'b00),               // input wire [1:0] gt0_rxmonitorsel_in
             .gt0_rxoutclk_out           (rxoutclk),            // output wire gt0_rxoutclk_out
             .gt0_rxoutclkfabric_out     (),                    // output wire gt0_rxoutclkfabric_out
             .gt0_gtrxreset_in           (~gt_rst_n_i),         // input wire gt0_gtrxreset_in
             .gt0_rxpmareset_in          (~gt_rst_n_i),         // input wire gt0_rxpmareset_in
             .gt0_rxslide_in             (rx_slide_i),          // input wire gt0_rxslide_in
             .gt0_rxcharisk_out          (),                    // output wire [3:0] gt0_rxcharisk_out
             .gt0_rxresetdone_out        (rxpmaresetdone),      // output wire gt0_rxresetdone_out
             .gt0_gttxreset_in           (~gt_rst_n_i),         // input wire gt0_gttxreset_in
             .gt0_txuserrdy_in           (1'b1),                // input wire gt0_txuserrdy_in
             .gt0_txusrclk_in            (tx_clk_2x_o),         // input wire gt0_txusrclk_in
             .gt0_txusrclk2_in           (tx_clk_2x_o),         // input wire gt0_txusrclk2_in
             .gt0_txdata_in              (tx_tdata_i),          // input wire [31:0] gt0_txdata_in
             .gt0_gtxtxn_out             (),                    // output wire gt0_gtxtxn_out
             .gt0_gtxtxp_out             (),                    // output wire gt0_gtxtxp_out
             .gt0_txoutclk_out           (txoutclk),            // output wire gt0_txoutclk_out
             .gt0_txoutclkfabric_out     (),                    // output wire gt0_txoutclkfabric_out
             .gt0_txoutclkpcs_out        (),                    // output wire gt0_txoutclkpcs_out
             .gt0_txcharisk_in           (4'h0),                // input wire [3:0] gt0_txcharisk_in
             .gt0_txpmareset_in          (~gt_rst_n_i),         // input wire gt0_txpmareset_in
             .gt0_txresetdone_out        (),                    // output wire gt0_txresetdone_out
             .gt0_qplllock_in            (qplllock_out),        // input wire gt0_qplllock_in
             .gt0_qpllrefclklost_in      (qpllrefclklost_out),  // input wire gt0_qpllrefclklost_in
             .gt0_qpllreset_out          (qpllreset_in),        // output wire gt0_qpllreset_out
             .gt0_qplloutclk_in          (qplloutclk_out),      // input wire gt0_qplloutclk_in
             .gt0_qplloutrefclk_in       (qplloutrefclk_out)    // input wire gt0_qplloutrefclk_in
         );

         // GTX transceiver does not have RXSLIDERDY
         assign rx_slide_rdy_o = 1'b1;
         // GTX transceiver does not have gt_power_good
         assign gt_power_good_o = 1'b1;

         // MMCMs must be reset after clk input gets interrupted
         // Async reset generation for TX MMCM
         assign txoutclk_stopped_fall = txoutclk_stopped & ~txoutclk_stopped_d1;
         always_ff @(posedge f_clk_i) begin
            txoutclk_stopped_d1 <= txoutclk_stopped;
            if (txoutclk_stopped_fall) tx_mmcm_reset <= 1'b1;
            else tx_mmcm_reset <= 1'b0;
         end

         // Async reset generation for RX MMCM
         assign rxoutclk_stopped_fall = rxoutclk_stopped & ~rxoutclk_stopped_d1;
         always_ff @(posedge f_clk_i) begin
            rxoutclk_stopped_d1 <= rxoutclk_stopped;
            if (rxoutclk_stopped_fall) rx_mmcm_reset <= 1'b1;
            else rx_mmcm_reset <= 1'b0;
         end

         qeciphy_gtx_common i_gtx_common (
             .qpllrefclksel_in  (3'b010),
             .gtrefclk0_in      (1'b0),
             .gtrefclk1_in      (gt_ref_clk_i),
             .qplllock_out      (qplllock_out),
             .qplllockdetclk_in (f_clk_i),
             .qplloutclk_out    (qplloutclk_out),
             .qplloutrefclk_out (qplloutrefclk_out),
             .qpllrefclklost_out(qpllrefclklost_out),
             .qpllreset_in      (qpllreset_in)
         );

         qeciphy_clk_mmcm i_tx_clks (
             .clk_in           (txoutclk),
             .reset            (tx_mmcm_reset),
             .clk_out          (tx_clk_o),
             .clk_out_2x       (tx_clk_2x_o),
             .input_clk_stopped(txoutclk_stopped)
         );

         qeciphy_clk_mmcm i_rx_clks (
             .clk_in           (rxoutclk),
             .reset            (rx_mmcm_reset),
             .clk_out          (rx_clk_o),
             .clk_out_2x       (rx_clk_2x_o),
             .input_clk_stopped(rxoutclk_stopped)
         );

      end
   endgenerate

endmodule  // qeciphy_gt_wrapper
