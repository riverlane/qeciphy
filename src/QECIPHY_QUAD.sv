// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Evan Sun

//------------------------------------------------------------------------------
// QECIPHY_QUAD Top-Level Module
//------------------------------------------------------------------------------
// Instantiates NUM_LANES (1-4) QECIPHY lanes sharing one transceiver quad.
// For a single lane, instantiate QECIPHY directly.
//
// - Xilinx GTY: lanes share one GT COMMON (QPLL0), instantiated here. Requires
//   transceiver.gt_common = "external" and transceiver.shared_channel_core = "true".
//   GTH is untested; GTX is unsupported.
// - Altera E-/F-tile: no shared PLL, so lanes sit side by side sharing RCLK.
//   Any per-tile refclk IP stays in your top level.
//
// RCLK/FCLK are shared; ACLK/ARSTn are per lane. Lane pin placement is left to your
// constraints. A single lane's reset never resets the shared QPLL0 (see qpll0reset).
//------------------------------------------------------------------------------

`include "qeciphy_build_cfg_pkg.sv"

module QECIPHY_QUAD #(
    parameter int NUM_LANES = 4  // Lanes in this quad (1-4)
) (
    // =========================================================================
    // Clock and Reset Interface
    // =========================================================================
    input logic                 RCLK,  // Transceiver reference clock (shared by all lanes)
    input logic                 FCLK,  // Free-running fabric clock (shared by all lanes)
    input logic [NUM_LANES-1:0] ACLK,  // Per-lane AXI4-Stream interface clock
    input logic [NUM_LANES-1:0] ARSTn, // Per-lane master reset (active-low), synchronous to that lane's ACLK

    // =========================================================================
    // AXI4-Stream TX Interface (User -> QECIPHY), per lane
    // =========================================================================
    input  logic [         63:0] TX_TDATA [NUM_LANES],
    input  logic [NUM_LANES-1:0] TX_TVALID,
    output logic [NUM_LANES-1:0] TX_TREADY,

    // =========================================================================
    // AXI4-Stream RX Interface (QECIPHY -> User), per lane
    // =========================================================================
    output logic [         63:0] RX_TDATA [NUM_LANES],
    output logic [NUM_LANES-1:0] RX_TVALID,
    input  logic [NUM_LANES-1:0] RX_TREADY,

    // =========================================================================
    // Status and Control Interface, per lane
    // =========================================================================
    output logic [          3:0] STATUS     [NUM_LANES],
    output logic [          3:0] ECODE      [NUM_LANES],
    output logic [NUM_LANES-1:0] LINK_READY,
    output logic [NUM_LANES-1:0] FAULT_FATAL,

    // =========================================================================
    // Transceiver Differential Signals, per lane
    // =========================================================================
    input  logic [NUM_LANES-1:0] GT_RX_P,
    input  logic [NUM_LANES-1:0] GT_RX_N,
    output logic [NUM_LANES-1:0] GT_TX_P,
    output logic [NUM_LANES-1:0] GT_TX_N
);

   localparam string GT_TYPE = qeciphy_build_cfg_pkg::QECIPHY_GT_TYPE;

   // =========================================================================
   // Configuration checks
   // =========================================================================
   generate
      if (NUM_LANES < 1 || NUM_LANES > 4) begin : gen_num_lanes_check
         $error("QECIPHY_QUAD: NUM_LANES must be between 1 and 4 (got %0d)", NUM_LANES);
      end

      if (GT_TYPE == "GTX") begin : gen_gtx_check
         $error("QECIPHY_QUAD: GT_TYPE GTX is not supported - each GTX lane embeds its own GT COMMON, so GTX lanes cannot share a quad. Use QECIPHY instead.");
      end else if ((GT_TYPE == "GTY" || GT_TYPE == "GTH") && qeciphy_build_cfg_pkg::QECIPHY_GT_COMMON_MODE != "external") begin : gen_gt_common_check
         $error(
             "QECIPHY_QUAD: GT_TYPE %s needs a shared GT COMMON - set transceiver.gt_common to \"external\" and transceiver.shared_channel_core to \"true\" in config.json, then re-run render-design.",
             GT_TYPE
         );
      end else if (!(GT_TYPE == "GTY" || GT_TYPE == "GTH" || GT_TYPE == "ETILE" || GT_TYPE == "FTILE")) begin : gen_gt_type_check
         $error("QECIPHY_QUAD: unsupported GT_TYPE \"%s\". Valid values: GTY, GTH, ETILE, FTILE.", GT_TYPE);
      end
   endgenerate

   // =========================================================================
   // Xilinx GTY/GTH: one GT COMMON (QPLL0) shared by every lane
   // =========================================================================
`ifdef QECIPHY_GT_COMMON_EXTERNAL
   logic                 qpll0outclk;
   logic                 qpll0outrefclk;
   logic                 qpll0lock;
   logic                 qpll0refclklost;
   logic [NUM_LANES-1:0] gt_qpll_reset;
   logic                 qpll0reset;

   // Neither the wizard's reset helper nor QECIPHY's reset controller recovers from a QPLL
   // lock loss after its sequence ends, so ORing the per-lane requests would let one lane's
   // reset break the rest. Reset the shared QPLL only:
   //  - &gt_qpll_reset: at power-up, released when the first lane reaches wait-for-lock.
   //  - &(~ARSTn):      when all lanes are reset together (e.g. after a refclk interruption).
   assign qpll0reset = (&gt_qpll_reset) | (&(~ARSTn));

   generate
      if (GT_TYPE == "GTY") begin : gen_gty_common
         qeciphy_gty_common i_gt_common (
             .qpll0refclksel_in  (3'b001),
             .gtrefclk00_in      (RCLK),
             .gtrefclk01_in      (1'b0),
             .qpll0lock_out      (qpll0lock),
             .qpll0lockdetclk_in (FCLK),
             .qpll0outclk_out    (qpll0outclk),
             .qpll0outrefclk_out (qpll0outrefclk),
             .qpll0refclklost_out(qpll0refclklost),
             .qpll0reset_in      (qpll0reset)
         );
      end else if (GT_TYPE == "GTH") begin : gen_gth_common
         qeciphy_gth_common i_gt_common (
             .qpll0refclksel_in  (3'b001),
             .gtrefclk00_in      (RCLK),
             .gtrefclk01_in      (1'b0),
             .qpll0lock_out      (qpll0lock),
             .qpll0lockdetclk_in (FCLK),
             .qpll0outclk_out    (qpll0outclk),
             .qpll0outrefclk_out (qpll0outrefclk),
             .qpll0refclklost_out(qpll0refclklost),
             .qpll0reset_in      (qpll0reset)
         );
      end
   endgenerate
`endif

   // =========================================================================
   // Lanes
   // =========================================================================
   generate
      for (genvar i = 0; i < NUM_LANES; i++) begin : gen_lane
         QECIPHY i_QECIPHY (
             .RCLK (RCLK),
             .FCLK (FCLK),
             .ACLK (ACLK[i]),
             .ARSTn(ARSTn[i]),

             .TX_TDATA (TX_TDATA[i]),
             .TX_TVALID(TX_TVALID[i]),
             .TX_TREADY(TX_TREADY[i]),

             .RX_TDATA (RX_TDATA[i]),
             .RX_TVALID(RX_TVALID[i]),
             .RX_TREADY(RX_TREADY[i]),

             .STATUS     (STATUS[i]),
             .ECODE      (ECODE[i]),
             .LINK_READY (LINK_READY[i]),
             .FAULT_FATAL(FAULT_FATAL[i]),

`ifdef QECIPHY_GT_COMMON_EXTERNAL
             .GT_QPLL_CLK   (qpll0outclk),
             .GT_QPLL_REFCLK(qpll0outrefclk),
             .GT_QPLL_LOCK  (qpll0lock),
             .GT_QPLL_RESET (gt_qpll_reset[i]),

`endif
             .GT_RX_P(GT_RX_P[i]),
             .GT_RX_N(GT_RX_N[i]),
             .GT_TX_P(GT_TX_P[i]),
             .GT_TX_N(GT_TX_N[i])
         );
      end
   endgenerate

endmodule  // QECIPHY_QUAD
