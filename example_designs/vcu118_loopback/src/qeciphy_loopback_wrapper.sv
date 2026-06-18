// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2025 Riverlane Ltd.

module qeciphy_loopback_wrapper (
    input  logic       gt_refclk_in_p,
    input  logic       gt_refclk_in_n,
    input  logic [1:0] gt_rx_p,
    input  logic [1:0] gt_rx_n,
    output logic [1:0] gt_tx_p,
    output logic [1:0] gt_tx_n,
    output logic [3:0] led
);

   logic        RCLK;
   logic        FCLK;
   logic        ACLK;
   logic        ARSTn;
   logic [ 4:0] rst_counter;
   logic [ 4:0] rst_counter_nxt;
   logic        rst_n_async;
   logic [ 1:0] rst_n_sf;
   logic        rst_n;
   logic        clk_freerun;
   logic [ 3:0] sfp_enable;

   logic [63:0] TX_TDATA_0;
   logic [63:0] TX_TDATA_0_nxt;
   logic        TX_TVALID_0;
   logic        TX_TREADY_0;
   logic [63:0] RX_TDATA_0;
   logic        RX_TVALID_0;
   logic        RX_TREADY_0;
   logic [ 3:0] STATUS_0;
   logic [ 3:0] ECODE_0;
   logic [63:0] RX_TDATA_ref_0;
   logic [63:0] RX_TDATA_ref_0_nxt;
   logic        RXDATA_error_0;
   logic        RXDATA_error_0_nxt;

   logic [63:0] TX_TDATA_1;
   logic [63:0] TX_TDATA_1_nxt;
   logic        TX_TVALID_1;
   logic        TX_TREADY_1;
   logic [63:0] RX_TDATA_1;
   logic        RX_TVALID_1;
   logic        RX_TREADY_1;
   logic [ 3:0] STATUS_1;
   logic [ 3:0] ECODE_1;
   logic [63:0] RX_TDATA_ref_1;
   logic [63:0] RX_TDATA_ref_1_nxt;
   logic        RXDATA_error_1;
   logic        RXDATA_error_1_nxt;

   // Refer: https://docs.amd.com/r/en-US/ug974-vivado-ultrascale-libraries/IBUFDS_GTE4
   IBUFDS_GTE4 #(
       .REFCLK_EN_TX_PATH(1'b0),
       .REFCLK_HROW_CK_SEL(2'b00),
       .REFCLK_ICNTL_RX(2'b00)
   ) i_buff_gtrefclk (
       .O    (RCLK),
       .ODIV2(clk_freerun),
       .CEB  (1'b0),
       .I    (gt_refclk_in_p),
       .IB   (gt_refclk_in_n)
   );

   BUFG_GT i_buff_fclk (
       .O      (FCLK),
       .CE     (1'b1),
       .CEMASK (1'b1),
       .CLR    (1'b0),
       .CLRMASK(1'b1),
       .DIV    (3'b000),
       .I      (clk_freerun)
   );

   qeciphy_rx_ila i_rx_ila (
       .clk   (ACLK),
       .probe0(RX_TDATA_0),
       .probe1(RX_TVALID_0),
       .probe2(STATUS_0),
       .probe3(ECODE_0),
       .probe4(sfp_enable),
       .probe5(RXDATA_error_0)
   );

   qeciphy_vio i_vio (
       .clk       (ACLK),
       .probe_out0(rst_n_async),
       .probe_out1(sfp_enable)
   );

   // Generate 16 cycle reset that de-asserts synchronously
   assign ARSTn = rst_counter[4];
   assign rst_counter_nxt = ARSTn ? rst_counter : rst_counter + 5'h1;
   assign rst_n = rst_n_sf[1];

   always_ff @(posedge ACLK or negedge rst_n) begin
      if (!rst_n) rst_counter <= 5'h0;
      else rst_counter <= rst_counter_nxt;
   end

   always_ff @(posedge ACLK) begin
      if (!rst_n_async) rst_n_sf <= 2'h0;
      else rst_n_sf <= {rst_n_sf[0], 1'b1};
   end

   // Connect free-running clock to AXI clock for simplicity
   assign ACLK = FCLK;

   // By the spec
   assign RX_TREADY_0 = 1'b1;
   assign RX_TREADY_1 = 1'b1;

   // LED: STATUS ok for each PHY, then no RX error for each PHY
   assign led[0] = (STATUS_0 == 4'b0100) ? 1'b1 : 1'b0;
   assign led[1] = (STATUS_1 == 4'b0100) ? 1'b1 : 1'b0;
   assign led[2] = ~RXDATA_error_0;
   assign led[3] = ~RXDATA_error_1;

   // PHY 0: drive incrementing TX data
   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) TX_TVALID_0 <= 1'b0;
      else TX_TVALID_0 <= 1'b1;
   end

   assign TX_TDATA_0_nxt = TX_TREADY_0 ? TX_TDATA_0 + 64'h1 : TX_TDATA_0;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) TX_TDATA_0 <= '0;
      else TX_TDATA_0 <= TX_TDATA_0_nxt;
   end

   // PHY 1: drive incrementing TX data
   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) TX_TVALID_1 <= 1'b0;
      else TX_TVALID_1 <= 1'b1;
   end

   assign TX_TDATA_1_nxt = TX_TREADY_1 ? TX_TDATA_1 + 64'h1 : TX_TDATA_1;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) TX_TDATA_1 <= '0;
      else TX_TDATA_1 <= TX_TDATA_1_nxt;
   end

   // PHY 0: verify received data
   assign RX_TDATA_ref_0_nxt = RX_TVALID_0 ? RX_TDATA_ref_0 + 64'h1 : RX_TDATA_ref_0;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) RX_TDATA_ref_0 <= '0;
      else RX_TDATA_ref_0 <= RX_TDATA_ref_0_nxt;
   end

   assign RXDATA_error_0_nxt = RX_TVALID_0 ? (RX_TDATA_ref_0 != RX_TDATA_0) : RXDATA_error_0;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) RXDATA_error_0 <= '0;
      else RXDATA_error_0 <= RXDATA_error_0_nxt;
   end

   // PHY 1: verify received data
   assign RX_TDATA_ref_1_nxt = RX_TVALID_1 ? RX_TDATA_ref_1 + 64'h1 : RX_TDATA_ref_1;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) RX_TDATA_ref_1 <= '0;
      else RX_TDATA_ref_1 <= RX_TDATA_ref_1_nxt;
   end

   assign RXDATA_error_1_nxt = RX_TVALID_1 ? (RX_TDATA_ref_1 != RX_TDATA_1) : RXDATA_error_1;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) RXDATA_error_1 <= '0;
      else RXDATA_error_1 <= RXDATA_error_1_nxt;
   end

   QECIPHY #(
       .GT_TYPE("GTY")
   ) i_QECIPHY_0 (
       .RCLK     (RCLK),
       .FCLK     (FCLK),
       .ACLK     (ACLK),
       .ARSTn    (ARSTn),
       .TX_TDATA (TX_TDATA_0),
       .TX_TVALID(TX_TVALID_0),
       .TX_TREADY(TX_TREADY_0),
       .RX_TDATA (RX_TDATA_0),
       .RX_TVALID(RX_TVALID_0),
       .RX_TREADY(RX_TREADY_0),
       .STATUS   (STATUS_0),
       .ECODE    (ECODE_0),
       .GT_RX_P  (gt_rx_p[0]),
       .GT_RX_N  (gt_rx_n[0]),
       .GT_TX_P  (gt_tx_p[0]),
       .GT_TX_N  (gt_tx_n[0])
   );

   QECIPHY #(
       .GT_TYPE("GTY")
   ) i_QECIPHY_1 (
       .RCLK     (RCLK),
       .FCLK     (FCLK),
       .ACLK     (ACLK),
       .ARSTn    (ARSTn),
       .TX_TDATA (TX_TDATA_1),
       .TX_TVALID(TX_TVALID_1),
       .TX_TREADY(TX_TREADY_1),
       .RX_TDATA (RX_TDATA_1),
       .RX_TVALID(RX_TVALID_1),
       .RX_TREADY(RX_TREADY_1),
       .STATUS   (STATUS_1),
       .ECODE    (ECODE_1),
       .GT_RX_P  (gt_rx_p[1]),
       .GT_RX_N  (gt_rx_n[1]),
       .GT_TX_P  (gt_tx_p[1]),
       .GT_TX_N  (gt_tx_n[1])
   );

endmodule
