// SPDX-License-Identifier: None
// Copyright (c) 2025 Riverlane Ltd.
// Original authors: Dogancan Davutoglu, Gargi Sunil, Aniket Datta

module qeciphy_syn_wrapper (
    input  logic       gt_refclk_in_p,
    input  logic       gt_refclk_in_n,
    input  logic       clk_freerun_p,
    input  logic       clk_freerun_n,
    output logic [1:0] led
);

   // Signal declarations
   logic        RCLK;
   logic        FCLK;
   logic        ACLK;
   logic        ARSTn;
   logic [63:0] TX_TDATA;
   logic [63:0] TX_TDATA_nxt;
   logic        TX_TVALID;
   logic        TX_TREADY;
   logic [63:0] RX_TDATA;
   logic        RX_TVALID;
   logic        RX_TREADY;
   logic        PSTATE;
   logic        PREQ;
   logic        PACCEPT;
   logic        PACTIVE;
   logic [ 3:0] STATUS;
   logic [ 3:0] ECODE;
   logic [ 4:0] rst_counter;
   logic [ 4:0] rst_counter_nxt;
   logic        rst_n_async;
   logic [ 1:0] rst_n_sf;
   logic        rst_n;
   logic        clk_freerun;
   logic [ 3:0] sfp_enable;
   logic [63:0] RX_TDATA_ref;
   logic [63:0] RX_TDATA_ref_nxt;
   logic        RXDATA_error;
   logic        RXDATA_error_nxt;

   IBUFDS_GTE2 i_buff_gtrefclk (
       .O    (RCLK),
       .ODIV2(),
       .CEB  (1'b0),
       .I    (gt_refclk_in_p),
       .IB   (gt_refclk_in_n)
   );

   IBUFDS i_ibufds_freerun (
       .O (clk_freerun),
       .I (clk_freerun_p),
       .IB(clk_freerun_n)
   );

   BUFG i_buff_fclk (
       .O(FCLK),
       .I(clk_freerun)
   );

   qeciphy_rx_ila i_rx_ila (
       .clk   (ACLK),
       .probe0(RX_TDATA),
       .probe1(RX_TVALID),
       .probe2(PACCEPT),
       .probe3(PACTIVE),
       .probe4(STATUS),
       .probe5(ECODE),
       .probe6(sfp_enable),
       .probe7(RXDATA_error)
   );

   qeciphy_vio i_vio (
       .clk       (ACLK),
       .probe_out0(rst_n_async),
       .probe_out1(PSTATE),
       .probe_out2(PREQ),
       .probe_out3(sfp_enable)
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
   assign RX_TREADY = 1'b1;

   // For debugging
   assign led[0] = (STATUS == 4'b0100) ? 1'b1 : 1'b0;
   assign led[1] = (ECODE == 4'b0000) ? 1'b1 : 1'b0;

   // Drive the transmitter QECI-PHY TX data pins
   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) TX_TVALID <= 1'b0;
      else TX_TVALID <= 1'b1;
   end

   assign TX_TDATA_nxt = TX_TREADY ? TX_TDATA + 64'h1 : TX_TDATA;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) TX_TDATA <= 'h0;
      else TX_TDATA <= TX_TDATA_nxt;
   end

   // Verify receiver data  
   assign RX_TDATA_ref_nxt = RX_TVALID ? RX_TDATA_ref + 64'h1 : RX_TDATA_ref;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) RX_TDATA_ref <= 'h0;
      else RX_TDATA_ref <= RX_TDATA_ref_nxt;
   end

   assign RXDATA_error_nxt = RX_TVALID ? (RX_TDATA_ref != RX_TDATA) : RXDATA_error;

   always_ff @(posedge FCLK or negedge ARSTn) begin
      if (!ARSTn) RXDATA_error <= 'h0;
      else RXDATA_error <= RXDATA_error_nxt;
   end

   QECIPHY #(
       .GT_TYPE("GTX")
   ) i_QECIPHY (
       .RCLK     (RCLK),
       .FCLK     (FCLK),
       .ACLK     (ACLK),
       .ARSTn    (ARSTn),
       .TX_TDATA (TX_TDATA),
       .TX_TVALID(TX_TVALID),
       .TX_TREADY(TX_TREADY),
       .RX_TDATA (RX_TDATA),
       .RX_TVALID(RX_TVALID),
       .RX_TREADY(RX_TREADY),
       .PSTATE   (PSTATE),
       .PREQ     (PREQ),
       .PACCEPT  (PACCEPT),
       .PACTIVE  (PACTIVE),
       .STATUS   (STATUS),
       .ECODE    (ECODE)
   );

endmodule
