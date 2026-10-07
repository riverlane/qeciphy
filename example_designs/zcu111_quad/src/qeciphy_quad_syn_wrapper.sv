// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Evan Sun
//
// Quad example design: NUM_LANES QECIPHY lanes sharing one GT quad via
// QECIPHY_QUAD, on the ZCU111's SFP0-SFP3 cages (bank 128, GTYE4_CHANNEL_X0Y4-7).
// Per-lane channel placement is set in this profile's constraints.xdc.
//
// Each lane's VIO scratch register bit 0 drives that lane's SFP_tx_enable.
// Only 3 status LEDs are available, so `led` summarises all lanes.

module qeciphy_quad_syn_wrapper #(
    parameter int NUM_LANES = 4
) (
    input  logic                 gt_refclk_in_p,
    input  logic                 gt_refclk_in_n,
    input  logic [NUM_LANES-1:0] gt_rx_p,
    input  logic [NUM_LANES-1:0] gt_rx_n,
    output logic [NUM_LANES-1:0] gt_tx_p,
    output logic [NUM_LANES-1:0] gt_tx_n,
    output logic [NUM_LANES-1:0] SFP_tx_enable,
    output logic [          2:0] led
);

   // Shared quad clocking - one physical quad has a single reference clock.
   logic RCLK;
   logic FCLK;
   logic clk_freerun;

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

   // Per-lane signals, arrayed for connection to QECIPHY_QUAD.
   logic [NUM_LANES-1:0] ACLK;
   logic [NUM_LANES-1:0] ARSTn;
   logic [         63:0] TX_TDATA       [NUM_LANES];
   logic [         63:0] TX_TDATA_nxt   [NUM_LANES];
   logic [NUM_LANES-1:0] TX_TVALID;
   logic [NUM_LANES-1:0] TX_TREADY;
   logic [         63:0] RX_TDATA       [NUM_LANES];
   logic [NUM_LANES-1:0] RX_TVALID;
   logic [NUM_LANES-1:0] RX_TREADY;
   logic [          3:0] STATUS         [NUM_LANES];
   logic [          3:0] ECODE          [NUM_LANES];
   logic [NUM_LANES-1:0] LINK_READY;
   logic [NUM_LANES-1:0] FAULT_FATAL;

   // Per-lane LED contributions, combined into the single shared `led` below.
   logic [NUM_LANES-1:0] lane_link_up;
   logic [NUM_LANES-1:0] lane_no_error;
   logic [NUM_LANES-1:0] lane_rxdata_ok;

   generate
      for (genvar i = 0; i < NUM_LANES; i++) begin : gen_lane

         logic [ 4:0] rst_counter;
         logic [ 4:0] rst_counter_nxt;
         logic        rst_n_async;
         logic [ 1:0] rst_n_sf;
         logic        rst_n;
         logic [63:0] RX_TDATA_ref;
         logic [63:0] RX_TDATA_ref_nxt;
         logic        RXDATA_error;
         logic        RXDATA_error_nxt;
         // VIO/ILA scratch register (bit 0: SFP_tx_enable[i])
         logic [ 3:0] dbg_ctrl;

         // Connect free-running clock to this lane's AXI clock for simplicity
         assign ACLK[i] = FCLK;

         qeciphy_rx_ila i_rx_ila (
             .clk   (ACLK[i]),
             .probe0(RX_TDATA[i]),
             .probe1(RX_TVALID[i]),
             .probe2(STATUS[i]),
             .probe3(ECODE[i]),
             .probe4(dbg_ctrl),
             .probe5(RXDATA_error)
         );

         qeciphy_vio i_vio (
             .clk       (ACLK[i]),
             .probe_out0(rst_n_async),
             .probe_out1(dbg_ctrl)
         );

         assign SFP_tx_enable[i] = dbg_ctrl[0];

         // Generate 16 cycle reset that de-asserts synchronously
         assign ARSTn[i] = rst_counter[4];
         assign rst_counter_nxt = ARSTn[i] ? rst_counter : rst_counter + 5'h1;
         assign rst_n = rst_n_sf[1];

         always_ff @(posedge ACLK[i] or negedge rst_n) begin
            if (!rst_n) rst_counter <= 5'h0;
            else rst_counter <= rst_counter_nxt;
         end

         always_ff @(posedge ACLK[i]) begin
            if (!rst_n_async) rst_n_sf <= 2'h0;
            else rst_n_sf <= {rst_n_sf[0], 1'b1};
         end

         // By the spec
         assign RX_TREADY[i] = 1'b1;

         // For debugging - combined into the shared `led` outside this loop
         assign lane_link_up[i] = (STATUS[i] == 4'b0100) ? 1'b1 : 1'b0;
         assign lane_no_error[i] = (ECODE[i] == 4'b0000) ? 1'b1 : 1'b0;
         assign lane_rxdata_ok[i] = ~RXDATA_error;

         // Drive the transmitter QECI-PHY TX data pins
         always_ff @(posedge FCLK or negedge ARSTn[i]) begin
            if (!ARSTn[i]) TX_TVALID[i] <= 1'b0;
            else TX_TVALID[i] <= 1'b1;
         end

         assign TX_TDATA_nxt[i] = TX_TREADY[i] ? TX_TDATA[i] + 64'h1 : TX_TDATA[i];

         always_ff @(posedge FCLK or negedge ARSTn[i]) begin
            if (!ARSTn[i]) TX_TDATA[i] <= 'h0;
            else TX_TDATA[i] <= TX_TDATA_nxt[i];
         end

         // Verify receiver data
         assign RX_TDATA_ref_nxt = RX_TVALID[i] ? RX_TDATA_ref + 64'h1 : RX_TDATA_ref;

         always_ff @(posedge FCLK or negedge ARSTn[i]) begin
            if (!ARSTn[i]) RX_TDATA_ref <= 'h0;
            else RX_TDATA_ref <= RX_TDATA_ref_nxt;
         end

         assign RXDATA_error_nxt = RX_TVALID[i] ? (RX_TDATA_ref != RX_TDATA[i]) : RXDATA_error;

         always_ff @(posedge FCLK or negedge ARSTn[i]) begin
            if (!ARSTn[i]) RXDATA_error <= 'h0;
            else RXDATA_error <= RXDATA_error_nxt;
         end

      end
   endgenerate

   // Summarize all active lanes onto the 3 physical LEDs available.
   assign led[0] = &lane_link_up;
   assign led[1] = &lane_no_error;
   assign led[2] = &lane_rxdata_ok;

   QECIPHY_QUAD #(
       .NUM_LANES(NUM_LANES)
   ) i_QECIPHY_QUAD (
       .RCLK (RCLK),
       .FCLK (FCLK),
       .ACLK (ACLK),
       .ARSTn(ARSTn),

       .TX_TDATA (TX_TDATA),
       .TX_TVALID(TX_TVALID),
       .TX_TREADY(TX_TREADY),

       .RX_TDATA (RX_TDATA),
       .RX_TVALID(RX_TVALID),
       .RX_TREADY(RX_TREADY),

       .STATUS     (STATUS),
       .ECODE      (ECODE),
       .LINK_READY (LINK_READY),
       .FAULT_FATAL(FAULT_FATAL),

       .GT_RX_P(gt_rx_p),
       .GT_RX_N(gt_rx_n),
       .GT_TX_P(gt_tx_p),
       .GT_TX_N(gt_tx_n)
   );

endmodule  // qeciphy_quad_syn_wrapper
