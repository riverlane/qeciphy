// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Dual QECIPHY simulation top-level with all ports exposed

module qeciphy_dual_sim_top (
    // Base clocks for IP generation
    input logic gt_refclk_in_p_1,
    input logic gt_refclk_in_p_2,
    input logic clk_100_p,         // 100 MHz system clock

    // QECIPHY Instance 1 - TX AXI Stream Interface
    input  logic [63:0] TX_TDATA_1,
    input  logic        TX_TVALID_1,
    output logic        TX_TREADY_1,

    // QECIPHY Instance 1 - RX AXI Stream Interface  
    output logic [63:0] RX_TDATA_1,
    output logic        RX_TVALID_1,
    input  logic        RX_TREADY_1,

    // QECIPHY Instance 1 - Status Interface
    output logic [3:0] STATUS_1,
    output logic [3:0] ECODE_1,
    output logic       LINK_READY_1,
    output logic       FAULT_FATAL_1,

    // QECIPHY Instance 1 - GT Interface
    input  logic GT_RX_N_1,
    input  logic GT_RX_P_1,
    output logic GT_TX_N_1,
    output logic GT_TX_P_1,

    // QECIPHY Instance 2 - TX AXI Stream Interface
    input  logic [63:0] TX_TDATA_2,
    input  logic        TX_TVALID_2,
    output logic        TX_TREADY_2,

    // QECIPHY Instance 2 - RX AXI Stream Interface
    output logic [63:0] RX_TDATA_2,
    output logic        RX_TVALID_2,
    input  logic        RX_TREADY_2,

    // QECIPHY Instance 2 - Status Interface
    output logic [3:0] STATUS_2,
    output logic [3:0] ECODE_2,
    output logic       LINK_READY_2,
    output logic       FAULT_FATAL_2,

    // QECIPHY Instance 2 - GT Interface
    input  logic GT_RX_N_2,
    input  logic GT_RX_P_2,
    output logic GT_TX_N_2,
    output logic GT_TX_P_2
);

   // System clock (100 MHz) shared by both instances
   logic       sys_clk_100;
   logic       sys_clk_200;
   logic       init_done_n;
   logic       rst_n;
   logic       ARSTn;
   logic [4:0] rst_counter;
   logic [4:0] rst_counter_nxt;

   // Per-instance reference clock signals
   logic       RCLK_1;
   logic       RCLK_2;
   logic       out_systempll_synthlock_1;
   logic       out_systempll_clk_1;
   logic       out_systempll_synthlock_2;
   logic       out_systempll_clk_2;

   // Aliases for TB observability
   logic       ACLK_1;
   logic       ACLK_2;
   assign ACLK_1 = sys_clk_100;
   assign ACLK_2 = sys_clk_100;

   // POR reset from configuration IP
   assign rst_n  = !init_done_n;
   reset_release reset_release_inst (.ninit_done(init_done_n));

   // Buffer 100 MHz system clock
   sys_clk_100 u0 (
       .inclk (clk_100_p),
       .outclk(sys_clk_100)
   );

   sys_clk_200_pll clk200_inst (
       .refclk  (sys_clk_100),  //   input,  width = 1,  refclk.clk
       .locked  (),             //  output,  width = 1,  locked.export
       .rst     (1'b0),         //   input,  width = 1,   reset.reset
       .axis_clk(sys_clk_200)   //  output,  width = 1, outclk0.clk
   );

   assign RCLK_1          = gt_refclk_in_p_1;
   assign RCLK_2          = gt_refclk_in_p_2;

   // 16-cycle synchronous reset de-assertion (shared across both instances)
   assign ARSTn           = rst_counter[4];
   assign rst_counter_nxt = ARSTn ? rst_counter : rst_counter + 5'h1;

   always_ff @(posedge sys_clk_100 or negedge rst_n) begin
      if (!rst_n) rst_counter <= 5'h0;
      else rst_counter <= rst_counter_nxt;
   end

   // QECIPHY Instance 1
   QECIPHY i_QECIPHY_1 (
       .RCLK       (RCLK_1),
       .FCLK       (sys_clk_200),
       .ACLK       (sys_clk_200),
       .ARSTn      (ARSTn),
       .TX_TDATA   (TX_TDATA_1),
       .TX_TVALID  (TX_TVALID_1),
       .TX_TREADY  (TX_TREADY_1),
       .RX_TDATA   (RX_TDATA_1),
       .RX_TVALID  (RX_TVALID_1),
       .RX_TREADY  (RX_TREADY_1),
       .STATUS     (STATUS_1),
       .ECODE      (ECODE_1),
       .LINK_READY (LINK_READY_1),
       .FAULT_FATAL(FAULT_FATAL_1),
       .GT_RX_P    (GT_RX_P_1),
       .GT_RX_N    (GT_RX_N_1),
       .GT_TX_P    (GT_TX_P_1),
       .GT_TX_N    (GT_TX_N_1)
   );

   // QECIPHY Instance 2
   QECIPHY i_QECIPHY_2 (
       .RCLK       (RCLK_2),
       .FCLK       (sys_clk_200),
       .ACLK       (sys_clk_200),
       .ARSTn      (ARSTn),
       .TX_TDATA   (TX_TDATA_2),
       .TX_TVALID  (TX_TVALID_2),
       .TX_TREADY  (TX_TREADY_2),
       .RX_TDATA   (RX_TDATA_2),
       .RX_TVALID  (RX_TVALID_2),
       .RX_TREADY  (RX_TREADY_2),
       .STATUS     (STATUS_2),
       .ECODE      (ECODE_2),
       .LINK_READY (LINK_READY_2),
       .FAULT_FATAL(FAULT_FATAL_2),
       .GT_RX_P    (GT_RX_P_2),
       .GT_RX_N    (GT_RX_N_2),
       .GT_TX_P    (GT_TX_P_2),
       .GT_TX_N    (GT_TX_N_2)
   );

endmodule
