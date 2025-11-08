// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta

`include "qeciphy_pkg.sv"

module QECIPHY #(
    parameter GT_TYPE = "GTY"
) (
    input  logic        RCLK,
    input  logic        FCLK,
    input  logic        ACLK,
    input  logic        ARSTn,
    input  logic [63:0] TX_TDATA,
    input  logic        TX_TVALID,
    output logic        TX_TREADY,
    output logic [63:0] RX_TDATA,
    output logic        RX_TVALID,
    input  logic        RX_TREADY,
    output logic [ 3:0] STATUS,
    output logic [ 3:0] ECODE,
    input  logic        PSTATE,
    input  logic        PREQ,
    output logic        PACCEPT,
    output logic        PACTIVE
);

   // -------------------------------------------------------------
   // Local declaration
   // -------------------------------------------------------------

   logic contr_rst_n;
   logic axis_rx_rst_n;
   logic axis_tx_rst_n;
   logic reset_done;
   logic rx_rdy_axis;
   logic remote_rx_rdy_axis;
   logic fap_missing_axis;
   logic crc_mismatch_axis;
   logic remote_pd_req_axis;
   logic remote_pd_ack_axis;
   logic pd_req_axis;
   logic pd_ack_axis;
   logic gt_power_good_axis;
   logic gt_rx_reset_done_axis;
   logic gt_tx_reset_done_axis;
   logic allow_user_tx;

   logic tx_clk;
   logic tx_rst_n;
   logic rx_rdy_tclk;
   logic remote_rx_rdy_tclk;
   logic pd_req_tclk;
   logic pd_ack_tclk;

   logic gt_tx_clk;
   logic [31:0] gt_tx_data;
   logic gt_tx_reset_done_tclk;

   logic rx_clk;
   logic rx_rst_n;
   logic rx_rdy_rclk;
   logic remote_rx_rdy_rclk;
   logic fap_missing_rclk;
   logic crc_mismatch_rclk;
   logic remote_pd_req_rclk;
   logic remote_pd_ack_rclk;

   logic gt_rx_clk;
   logic [31:0] gt_rx_data;
   logic rx_slide_rdy;
   logic rx_slide;
   logic gt_rx_reset_done_rclk;

   logic gt_rst_n;
   logic gt_power_good_fclk;

   // -------------------------------------------------------------
   // CDC
   // -------------------------------------------------------------

   riv_synchronizer_2ff i_rx_rdy_axis (
       .src_in(rx_rdy_rclk),
       .dst_clk(ACLK),
       .dst_rst_n(ARSTn),
       .dst_out(rx_rdy_axis)
   );

   riv_synchronizer_2ff i_sync_remote_rx_rdy_axis (
       .src_in(remote_rx_rdy_rclk),
       .dst_clk(ACLK),
       .dst_rst_n(ARSTn),
       .dst_out(remote_rx_rdy_axis)
   );

   riv_synchronizer_2ff i_sync_fap_missing_axis (
       .src_in(fap_missing_rclk),
       .dst_clk(ACLK),
       .dst_rst_n(ARSTn),
       .dst_out(fap_missing_axis)
   );

   riv_synchronizer_2ff i_sync_crc_mismatch_axis (
       .src_in(crc_mismatch_rclk),
       .dst_clk(ACLK),
       .dst_rst_n(ARSTn),
       .dst_out(crc_mismatch_axis)
   );

   riv_synchronizer_2ff i_sync_remote_pd_req_axis (
       .src_in(remote_pd_req_rclk),
       .dst_clk(ACLK),
       .dst_rst_n(ARSTn),
       .dst_out(remote_pd_req_axis)
   );

   riv_synchronizer_2ff i_sync_remote_pd_ack_axis (
       .src_in(remote_pd_ack_rclk),
       .dst_clk(ACLK),
       .dst_rst_n(ARSTn),
       .dst_out(remote_pd_ack_axis)
   );

   riv_synchronizer_2ff i_sync_gt_tx_reset_done_axis (
       .src_in(gt_tx_reset_done_tclk),
       .dst_clk(ACLK),
       .dst_rst_n(ARSTn),
       .dst_out(gt_tx_reset_done_axis)
   );

   riv_synchronizer_2ff i_sync_gt_rx_reset_done_axis (
       .src_in(gt_rx_reset_done_rclk),
       .dst_clk(ACLK),
       .dst_rst_n(ARSTn),
       .dst_out(gt_rx_reset_done_axis)
   );

   riv_synchronizer_2ff i_sync_gt_power_good_axis (
       .src_in(gt_power_good_fclk),
       .dst_clk(ACLK),
       .dst_rst_n(ARSTn),
       .dst_out(gt_power_good_axis)
   );

   riv_synchronizer_2ff i_sync_rx_rdy_tclk (
       .src_in(rx_rdy_rclk),
       .dst_clk(tx_clk),
       .dst_rst_n(tx_rst_n),
       .dst_out(rx_rdy_tclk)
   );

   riv_synchronizer_2ff i_sync_remote_rx_rdy_tclk (
       .src_in(remote_rx_rdy_rclk),
       .dst_clk(tx_clk),
       .dst_rst_n(tx_rst_n),
       .dst_out(remote_rx_rdy_tclk)
   );

   riv_synchronizer_2ff i_sync_pd_req_tclk (
       .src_in(pd_req_axis),
       .dst_clk(tx_clk),
       .dst_rst_n(tx_rst_n),
       .dst_out(pd_req_tclk)
   );

   riv_synchronizer_2ff i_sync_pd_ack_tclk (
       .src_in(pd_ack_axis),
       .dst_clk(tx_clk),
       .dst_rst_n(tx_rst_n),
       .dst_out(pd_ack_tclk)
   );

   // -------------------------------------------------------------
   // Controller instance
   // -------------------------------------------------------------

   qeciphy_controller i_qeciphy_controller (
       .axis_clk       (ACLK),
       .axis_rst_n     (ARSTn),
       .i_reset_done   (reset_done),
       .i_rx_rdy       (rx_rdy_axis),
       .i_remote_rx_rdy(remote_rx_rdy_axis),
       .i_fap_missing  (fap_missing_axis),
       .i_crc_error    (crc_mismatch_axis),
       .o_state        (STATUS),
       .o_ecode        (ECODE),
       .i_pstate       (PSTATE),
       .i_preq         (PREQ),
       .o_paccept      (PACCEPT),
       .o_pactive      (PACTIVE),
       .i_tx_tvalid    (TX_TVALID),
       .i_remote_pd_ack(remote_pd_ack_axis),
       .i_remote_pd_req(remote_pd_req_axis),
       .o_pd_ack       (pd_ack_axis),
       .o_pd_req       (pd_req_axis),
       .o_allow_user_tx(allow_user_tx),
       .o_rst_n        (contr_rst_n)
   );

   // -------------------------------------------------------------
   // Tx channel instance
   // -------------------------------------------------------------

   qeciphy_tx i_qeciphy_tx (
       .axis_clk            (ACLK),
       .axis_rst_n          (axis_tx_rst_n),
       .i_data              (TX_TDATA),
       .o_ready             (TX_TREADY),
       .i_valid             (TX_TVALID),
       .i_allow_user_tx     (allow_user_tx),

       .tx_clk         (tx_clk),
       .tx_rst_n       (tx_rst_n),
       .i_rx_rdy       (rx_rdy_tclk),
       .i_remote_rx_rdy(remote_rx_rdy_tclk),
       .i_pd_req       (pd_req_tclk),
       .i_pd_ack       (pd_ack_tclk),

       .gt_tx_clk   (gt_tx_clk),
       .o_gt_tx_data(gt_tx_data)
   );

   // -------------------------------------------------------------
   // Rx channel instance
   // -------------------------------------------------------------

   qeciphy_rx i_qeciphy_rx (
       .axis_clk  (ACLK),
       .axis_rst_n(axis_rx_rst_n),
       .o_data    (RX_TDATA),
       .o_valid   (RX_TVALID),
       .i_ready   (RX_TREADY),

       .gt_rx_clk     (gt_rx_clk),
       .i_gt_rx_data  (gt_rx_data),
       .i_rx_slide_rdy(rx_slide_rdy),
       .o_rx_slide    (rx_slide),

       .rx_clk         (rx_clk),
       .rx_rst_n       (rx_rst_n),
       .o_rx_rdy       (rx_rdy_rclk),
       .o_remote_rx_rdy(remote_rx_rdy_rclk),
       .o_remote_pd_req(remote_pd_req_rclk),
       .o_remote_pd_ack(remote_pd_ack_rclk),
       .o_fap_missing  (fap_missing_rclk),
       .o_crc_mismatch (crc_mismatch_rclk)
   );

   // -------------------------------------------------------------
   // Transceiver wrapper instance
   // -------------------------------------------------------------

   (* KEEP_HIERARCHY = "TRUE" *)
   qeciphy_gt_wrapper #(
       .GT_TYPE(GT_TYPE)
   ) i_qeciphy_gt_wrapper (
       .gt_ref_clk(RCLK),

       .fclk           (FCLK),
       .rst_n          (gt_rst_n),
       .o_gt_power_good(gt_power_good_fclk),

       .tx_clk(tx_clk),

       .gt_tx_clk      (gt_tx_clk),
       .i_gt_tx_data   (gt_tx_data),
       .o_tx_reset_done(gt_tx_reset_done_tclk),

       .rx_clk(rx_clk),

       .gt_rx_clk      (gt_rx_clk),
       .o_gt_rx_data   (gt_rx_data),
       .o_rx_reset_done(gt_rx_reset_done_rclk),
       .o_rx_slide_rdy (rx_slide_rdy),
       .i_rx_slide     (rx_slide)

   );

   // -------------------------------------------------------------
   // Reset controller instance
   // -------------------------------------------------------------

   qeciphy_resetcontroller i_qeciphy_resetcontroller (
       .axis_clk          (ACLK),
       .axis_rst_n        (contr_rst_n),
       .o_axis_rx_rst_n   (axis_rx_rst_n),
       .o_axis_tx_rst_n   (axis_tx_rst_n),
       .o_reset_done      (reset_done),
       .i_gt_tx_reset_done(gt_tx_reset_done_axis),
       .i_gt_rx_reset_done(gt_rx_reset_done_axis),
       .i_gt_power_good   (gt_power_good_axis),

       .tx_clk    (tx_clk),
       .o_tx_rst_n(tx_rst_n),

       .rx_clk    (rx_clk),
       .o_rx_rst_n(rx_rst_n),

       .fclk      (FCLK),
       .o_gt_rst_n(gt_rst_n)
   );

endmodule  // QECIPHY
