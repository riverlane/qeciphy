// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2024-2026 Riverlane Ltd.
// Original authors: Dogancan Davutoglu, Aniket Datta

module qeciphy_gt_wrapper #(
    parameter string GT_TYPE = "GTY"  // Valid values: "GTX", "GTY", "GTH", "ETILE", or "FTILE" 
) (
    input logic gt_ref_clk_i,

    input  logic f_clk_i,
    input  logic gt_rst_n_i,
    output logic gt_power_good_o,

    output logic        tx_clk_o,
    output logic        tx_clk_2x_o,
    input  logic [31:0] tx_tdata_i,
    input  logic [ 3:0] tx_tdata_charisk_i,
    output logic        gt_tx_rst_done_o,

    output logic        rx_clk_o,
    output logic        rx_clk_2x_o,
    output logic [31:0] rx_tdata_o,
    output logic        gt_rx_rst_done_o,
    output logic        rx_byte_aligned_o,

    // GT differential signals
    input  logic gt_rx_p_i,
    input  logic gt_rx_n_i,
    output logic gt_tx_p_o,
    output logic gt_tx_n_o
);

   // -------------------------------------------------------------
   // Vendor-specific GT wrapper selection
   // -------------------------------------------------------------
   generate
      if (GT_TYPE inside {"FTILE", "ETILE"}) begin : gen_altera
         qeciphy_gt_altera #(
             .GT_TYPE(GT_TYPE)
         ) i_qeciphy_gt_altera (
             .gt_ref_clk_i      (gt_ref_clk_i),
             .gt_rx_p_i         (gt_rx_p_i),
             .gt_rx_n_i         (gt_rx_n_i),
             .gt_tx_p_o         (gt_tx_p_o),
             .gt_tx_n_o         (gt_tx_n_o),
             .f_clk_i           (f_clk_i),
             .gt_rst_n_i        (gt_rst_n_i),
             .gt_power_good_o   (gt_power_good_o),
             .tx_clk_o          (tx_clk_o),
             .tx_clk_2x_o       (tx_clk_2x_o),
             .tx_tdata_i        (tx_tdata_i),
             .tx_tdata_charisk_i(tx_tdata_charisk_i),
             .gt_tx_rst_done_o  (gt_tx_rst_done_o),
             .rx_clk_o          (rx_clk_o),
             .rx_clk_2x_o       (rx_clk_2x_o),
             .rx_tdata_o        (rx_tdata_o),
             .gt_rx_rst_done_o  (gt_rx_rst_done_o),
             .rx_byte_aligned_o (rx_byte_aligned_o)
         );
      end else begin : gen_xilinx
         qeciphy_gt_xilinx #(
             .GT_TYPE(GT_TYPE)
         ) i_qeciphy_gt_xilinx (
             .gt_ref_clk_i      (gt_ref_clk_i),
             .gt_rx_p_i         (gt_rx_p_i),
             .gt_rx_n_i         (gt_rx_n_i),
             .gt_tx_p_o         (gt_tx_p_o),
             .gt_tx_n_o         (gt_tx_n_o),
             .f_clk_i           (f_clk_i),
             .gt_rst_n_i        (gt_rst_n_i),
             .gt_power_good_o   (gt_power_good_o),
             .tx_clk_o          (tx_clk_o),
             .tx_clk_2x_o       (tx_clk_2x_o),
             .tx_tdata_i        (tx_tdata_i),
             .tx_tdata_charisk_i(tx_tdata_charisk_i),
             .gt_tx_rst_done_o  (gt_tx_rst_done_o),
             .rx_clk_o          (rx_clk_o),
             .rx_clk_2x_o       (rx_clk_2x_o),
             .rx_tdata_o        (rx_tdata_o),
             .gt_rx_rst_done_o  (gt_rx_rst_done_o),
             .rx_byte_aligned_o (rx_byte_aligned_o)
         );
      end
   endgenerate

endmodule  // qeciphy_gt_wrapper
