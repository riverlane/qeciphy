// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta, Dogancan Davutoglu, Gargi Sunil

`timescale 1ns / 1ps `default_nettype none

module qeciphy_tb;

   //----------------------------------------
   // Macros
   //----------------------------------------
   `define msg_info(_str) $display("INFO:  (%0.2fus) %s", $realtime/1000.0, ``_str)
   `define msg_fatal(_str) $display("FATAL: (%0.2fus) %s", $realtime/1000.0, ``_str)

`ifndef GT_TYPE
   `define GT_TYPE "GTY"
`endif

   glbl glbl ();

   //----------------------------------------
   // Local parameters
   //----------------------------------------

   // All periods in [ns]
   localparam real RCLK_PERIOD_NS = (`GT_TYPE == "GTX") ? 8.0 : (`GT_TYPE == "GTH") ? 6.4 : 6.4;

   localparam real FCLK_PERIOD_NS = (`GT_TYPE == "GTX") ? 8.0 : (`GT_TYPE == "GTH") ? 6.4 : 6.4;

   localparam real ACLK_PERIOD_NS = 4.0;  // >= 156.25 MHz
   localparam real QPLL_PERIOD_NS = 0.08;

   localparam int MAX_CYCLES = 32'h0002_0000;
   localparam int MAX_SLIDE = 40;
   localparam int BIT_SLIDE = (`GT_TYPE == "GTX") ? 16 : (`GT_TYPE == "GTH") ? 3 : 9;

   localparam int TEST_SEQUENCE_LEN = 2048;
   localparam string TEST_DATASET = "random";  // "counter" or "random"
   localparam time SLEEP_DURATION = 10000ns;
   localparam int SLEEP_AT_TX_INDEX = 1000;

   //----------------------------------------
   // Typedefs
   //----------------------------------------

   typedef struct packed {
      logic [63:0] tdata;
      logic        tvalid;
      logic        tready;
   } axis_t;

   typedef enum logic [3:0] {
      RESET,
      WAIT_FOR_RESET,
      LINK_TRAINING,
      RX_LOCKED,
      LINK_READY,
      FAULT_FATAL,
      SLEEP,
      WAIT_FOR_POWERDOWN
   } fsm_t;

   typedef enum logic [3:0] {
      OK,
      FAP_MISSING,
      CRC_ERROR
   } error_t;

   //----------------------------------------
   // Signals
   //----------------------------------------

   logic                   rclk             [                  0:1];
   logic                   fclk             [                  0:1];
   logic                   aclk             [                  0:1];
   logic                   arstn            [                  0:1];

   logic                   pstate           [                  0:1];
   logic                   preq             [                  0:1];
   logic                   paccept          [                  0:1];

   fsm_t                   status           [                  0:1];
   error_t                 ecode            [                  0:1];

   axis_t                  axis_tx          [                  0:1];
   axis_t                  axis_rx          [                  0:1];

   logic   [         31:0] cycle_cnt;
   logic                   qpllclk;

   //----------------------------------------
   // TB storage
   //----------------------------------------

   logic   [         63:0] tx0_test_data    [0:TEST_SEQUENCE_LEN-1];
   logic   [         63:0] tx1_test_data    [0:TEST_SEQUENCE_LEN-1];
   logic   [         63:0] rx0_captured_data[0:TEST_SEQUENCE_LEN-1];
   logic   [         63:0] rx1_captured_data[0:TEST_SEQUENCE_LEN-1];

   int                     rx0_idx;
   int                     rx1_idx;
   int                     tx0_idx;
   int                     tx1_idx;

   logic                   rx0_capture_done;
   logic                   rx1_capture_done;

   logic   [MAX_SLIDE-1:0] dut1_txn;
   logic   [MAX_SLIDE-1:0] dut1_txp;
   logic   [MAX_SLIDE-1:0] dut0_txn;
   logic   [MAX_SLIDE-1:0] dut0_txp;

   //----------------------------------------
   // Clocks & reset
   //----------------------------------------

   initial begin
      rclk[0] = 1'b1;
      fclk[0] = 1'b1;
      aclk[0] = 1'b1;

      rclk[1] = 1'b0;
      fclk[1] = 1'b0;
      aclk[1] = 1'b0;

      qpllclk = 1'b0;
   end

   always #(RCLK_PERIOD_NS / 2.0) rclk[0] = ~rclk[0];
   always #(FCLK_PERIOD_NS / 2.0) fclk[0] = ~fclk[0];
   always #(ACLK_PERIOD_NS / 2.0) aclk[0] = ~aclk[0];

   always #(RCLK_PERIOD_NS / 2.0) rclk[1] = ~rclk[1];
   always #(FCLK_PERIOD_NS / 2.0) fclk[1] = ~fclk[1];
   always #(ACLK_PERIOD_NS / 2.0) aclk[1] = ~aclk[1];

   always #(QPLL_PERIOD_NS / 2.0) qpllclk = ~qpllclk;

   // Resets: assert at t=0, deassert after some cycles
   initial begin
      arstn[0] = 1'b0;
      arstn[1] = 1'b0;

      repeat (5) @(posedge aclk[0]);
      arstn[0] = 1'b1;
      `msg_info("PHY reset deasserted on DUT0");

      repeat (5) @(posedge aclk[1]);
      arstn[1] = 1'b1;
      `msg_info("PHY reset deasserted on DUT1");
   end

   //----------------------------------------
   // Initial TB conditions
   //----------------------------------------

   // AXI-Stream RX ready per spec
   initial begin
      axis_rx[0].tready = 1'b1;
      axis_rx[1].tready = 1'b1;
   end

   // TX defaults
   initial begin
      axis_tx[0].tvalid = 1'b0;
      axis_tx[1].tvalid = 1'b0;
      axis_tx[0].tdata  = '0;
      axis_tx[1].tdata  = '0;
   end

   // P-channel defaults
   initial begin
      pstate[0] = 1'b1;
      pstate[1] = 1'b1;
      preq[0]   = 1'b0;
      preq[1]   = 1'b0;
   end

   // Test data generation
   initial begin
      if (TEST_DATASET == "counter") begin
         for (int t = 0; t < TEST_SEQUENCE_LEN; t++) begin
            tx0_test_data[t] = 64'(t);
            tx1_test_data[t] = 64'(t);
         end
      end else begin : gen_random
         for (int t = 0; t < TEST_SEQUENCE_LEN; t++) begin
            tx0_test_data[t] = {$urandom, $urandom};
            tx1_test_data[t] = {$urandom, $urandom};
         end
      end

      axis_tx[0].tdata = tx0_test_data[0];
      axis_tx[1].tdata = tx1_test_data[0];
   end

   //----------------------------------------
   // High-speed serial connectivity
   //----------------------------------------

   generate
      if (`GT_TYPE == "GTX") begin : gen_gtx_links
         assign dut0.i_qeciphy_gt_wrapper.gen_GTX_transceiver.transceiver.gt0_gtxrxn_in = dut1_txn[BIT_SLIDE-1];
         assign dut0.i_qeciphy_gt_wrapper.gen_GTX_transceiver.transceiver.gt0_gtxrxp_in = dut1_txp[BIT_SLIDE-1];

         assign dut1.i_qeciphy_gt_wrapper.gen_GTX_transceiver.transceiver.gt0_gtxrxn_in = dut0_txn[BIT_SLIDE-1];
         assign dut1.i_qeciphy_gt_wrapper.gen_GTX_transceiver.transceiver.gt0_gtxrxp_in = dut0_txp[BIT_SLIDE-1];

         always_ff @(posedge qpllclk) begin
            dut1_txn <= {dut1_txn[MAX_SLIDE-2:0], dut1.i_qeciphy_gt_wrapper.gen_GTX_transceiver.transceiver.gt0_gtxtxn_out};
            dut1_txp <= {dut1_txp[MAX_SLIDE-2:0], dut1.i_qeciphy_gt_wrapper.gen_GTX_transceiver.transceiver.gt0_gtxtxp_out};
            dut0_txn <= {dut0_txn[MAX_SLIDE-2:0], dut0.i_qeciphy_gt_wrapper.gen_GTX_transceiver.transceiver.gt0_gtxtxn_out};
            dut0_txp <= {dut0_txp[MAX_SLIDE-2:0], dut0.i_qeciphy_gt_wrapper.gen_GTX_transceiver.transceiver.gt0_gtxtxp_out};
         end
      end else if (`GT_TYPE == "GTY") begin : gen_gty_links
         assign dut0.i_qeciphy_gt_wrapper.gen_GTY_transceiver.transceiver.gtyrxn_in = dut1_txn[BIT_SLIDE-1];
         assign dut0.i_qeciphy_gt_wrapper.gen_GTY_transceiver.transceiver.gtyrxp_in = dut1_txp[BIT_SLIDE-1];

         assign dut1.i_qeciphy_gt_wrapper.gen_GTY_transceiver.transceiver.gtyrxn_in = dut0_txn[BIT_SLIDE-1];
         assign dut1.i_qeciphy_gt_wrapper.gen_GTY_transceiver.transceiver.gtyrxp_in = dut0_txp[BIT_SLIDE-1];

         always_ff @(posedge qpllclk) begin
            dut1_txn <= {dut1_txn[MAX_SLIDE-2:0], dut1.i_qeciphy_gt_wrapper.gen_GTY_transceiver.transceiver.gtytxn_out};
            dut1_txp <= {dut1_txp[MAX_SLIDE-2:0], dut1.i_qeciphy_gt_wrapper.gen_GTY_transceiver.transceiver.gtytxp_out};
            dut0_txn <= {dut0_txn[MAX_SLIDE-2:0], dut0.i_qeciphy_gt_wrapper.gen_GTY_transceiver.transceiver.gtytxn_out};
            dut0_txp <= {dut0_txp[MAX_SLIDE-2:0], dut0.i_qeciphy_gt_wrapper.gen_GTY_transceiver.transceiver.gtytxp_out};
         end
      end else if (`GT_TYPE == "GTH") begin : gen_gth_links
         assign dut0.i_qeciphy_gt_wrapper.gen_GTH_transceiver.transceiver.gthrxn_in = dut1_txn[BIT_SLIDE-1];
         assign dut0.i_qeciphy_gt_wrapper.gen_GTH_transceiver.transceiver.gthrxp_in = dut1_txp[BIT_SLIDE-1];

         assign dut1.i_qeciphy_gt_wrapper.gen_GTH_transceiver.transceiver.gthrxn_in = dut0_txn[BIT_SLIDE-1];
         assign dut1.i_qeciphy_gt_wrapper.gen_GTH_transceiver.transceiver.gthrxp_in = dut0_txp[BIT_SLIDE-1];

         always_ff @(posedge qpllclk) begin
            dut1_txn <= {dut1_txn[MAX_SLIDE-2:0], dut1.i_qeciphy_gt_wrapper.gen_GTH_transceiver.transceiver.gthtxn_out};
            dut1_txp <= {dut1_txp[MAX_SLIDE-2:0], dut1.i_qeciphy_gt_wrapper.gen_GTH_transceiver.transceiver.gthtxp_out};
            dut0_txn <= {dut0_txn[MAX_SLIDE-2:0], dut0.i_qeciphy_gt_wrapper.gen_GTH_transceiver.transceiver.gthtxn_out};
            dut0_txp <= {dut0_txp[MAX_SLIDE-2:0], dut0.i_qeciphy_gt_wrapper.gen_GTH_transceiver.transceiver.gthtxp_out};
         end
      end
   endgenerate

   //----------------------------------------
   // Capture RX data
   //----------------------------------------

   always_ff @(posedge aclk[0] or negedge arstn[0]) begin
      if (!arstn[0]) begin
         rx0_captured_data <= '{default: '0};
         rx0_idx           <= 0;
         rx0_capture_done  <= 1'b0;
      end else begin
         if (axis_rx[0].tvalid && axis_rx[0].tready) begin
            rx0_captured_data[rx0_idx] <= axis_rx[0].tdata;
            rx0_idx                    <= rx0_idx + 1;
         end

         if (rx0_idx == TEST_SEQUENCE_LEN) begin
            rx0_capture_done <= 1'b1;
         end else if (rx0_idx > TEST_SEQUENCE_LEN) begin
            `msg_fatal("RX[0] captured more samples than expected");
            $fatal();
         end
      end
   end

   always_ff @(posedge aclk[1] or negedge arstn[1]) begin
      if (!arstn[1]) begin
         rx1_captured_data <= '{default: '0};
         rx1_idx           <= 0;
         rx1_capture_done  <= 1'b0;
      end else begin
         if (axis_rx[1].tvalid && axis_rx[1].tready) begin
            rx1_captured_data[rx1_idx] <= axis_rx[1].tdata;
            rx1_idx                    <= rx1_idx + 1;
         end

         if (rx1_idx == TEST_SEQUENCE_LEN) begin
            rx1_capture_done <= 1'b1;
         end else if (rx1_idx > TEST_SEQUENCE_LEN) begin
            `msg_fatal("RX[1] captured more samples than expected");
            $fatal();
         end
      end
   end

   // Cycle counter & watchdog
   always_ff @(posedge aclk[0] or negedge arstn[0]) begin
      if (!arstn[0]) begin
         cycle_cnt <= '0;
      end else begin
         cycle_cnt <= cycle_cnt + 1'b1;
      end
   end

   always_ff @(posedge aclk[0]) begin
      if (cycle_cnt == MAX_CYCLES) begin
         `msg_fatal("Watchdog timeout");
         $fatal();
      end
   end

   //----------------------------------------
   // Tasks
   //----------------------------------------

   task automatic check_link_training;
      while (!(status[0] == LINK_TRAINING && status[1] == LINK_TRAINING)) begin
         @(posedge aclk[0]);
      end
      `msg_info("Link training started");
   endtask

   task automatic check_link_ready;
      while (!(status[0] == LINK_READY && status[1] == LINK_READY)) begin
         @(posedge aclk[0]);
      end
      `msg_info("Link training complete");
   endtask

   // DUT0 TX driver
   task automatic drive_tx0_data;
      tx0_idx = 0;

      @(posedge aclk[0]);
      axis_tx[0].tdata  <= tx0_test_data[tx0_idx];
      axis_tx[0].tvalid <= 1'b1;

      while (tx0_idx < TEST_SEQUENCE_LEN) begin
         @(posedge aclk[0]);
         if (axis_tx[0].tready) begin
            tx0_idx++;
            if (tx0_idx == TEST_SEQUENCE_LEN) begin
               axis_tx[0].tvalid <= 1'b0;
            end else begin
               axis_tx[0].tdata  <= tx0_test_data[tx0_idx];
               axis_tx[0].tvalid <= 1'b1;
            end
         end
      end
   endtask

   // DUT1 TX driver
   task automatic drive_tx1_data;
      tx1_idx = 0;

      @(posedge aclk[1]);
      axis_tx[1].tdata  <= tx1_test_data[tx1_idx];
      axis_tx[1].tvalid <= 1'b1;

      while (tx1_idx < TEST_SEQUENCE_LEN) begin
         @(posedge aclk[1]);
         if (axis_tx[1].tready) begin
            tx1_idx++;
            if (tx1_idx == TEST_SEQUENCE_LEN) begin
               axis_tx[1].tvalid <= 1'b0;
            end else begin
               axis_tx[1].tdata  <= tx1_test_data[tx1_idx];
               axis_tx[1].tvalid <= 1'b1;
            end
         end
      end
   endtask

   task automatic compare_rx0_tx1;
      while (!rx0_capture_done) @(posedge aclk[0]);
      `msg_info("Validating data: DUT1 TX -> DUT0 RX");
      for (int idx = 0; idx < TEST_SEQUENCE_LEN; idx++) begin
         assert (tx1_test_data[idx] == rx0_captured_data[idx])
         else begin
            $display("Sample index: %4d - TX_DATA[1]: %h != RX_DATA[0]: %h", idx, tx1_test_data[idx], rx0_captured_data[idx]);
            `msg_fatal("RX[0] data does not match TX[1] data");
            $fatal();
         end
      end
   endtask

   task automatic compare_rx1_tx0;
      while (!rx1_capture_done) @(posedge aclk[1]);
      `msg_info("Validating data: DUT0 TX -> DUT1 RX");
      for (int idx = 0; idx < TEST_SEQUENCE_LEN; idx++) begin
         assert (tx0_test_data[idx] == rx1_captured_data[idx])
         else begin
            $display("Sample index: %4d - TX_DATA[0]: %h != RX_DATA[1]: %h", idx, tx0_test_data[idx], rx1_captured_data[idx]);
            `msg_fatal("RX[1] data does not match TX[0] data");
            $fatal();
         end
      end
   endtask

   task automatic wait_for_paccept(input bit dut, input bit val);
      if (dut == 0) begin
         while (paccept[0] == val) @(posedge aclk[0]);
      end else begin
         while (paccept[1] == val) @(posedge aclk[1]);
      end
   endtask

   task automatic power_down_req(input bit dut);
      string message;
      if (dut == 0) begin
         @(posedge aclk[0]);
         pstate[0] <= 1'b0;
         @(posedge aclk[0]);
         preq[0] <= 1'b1;
      end else begin
         @(posedge aclk[1]);
         pstate[1] <= 1'b0;
         @(posedge aclk[1]);
         preq[1] <= 1'b1;
      end

      message = $sformatf("Power-down request sent to DUT%0d", dut);
      `msg_info(message);

      wait_for_paccept(dut, 1'b0);

      if (dut == 0) begin
         @(posedge aclk[0]);
         preq[0] <= 1'b0;
      end else begin
         @(posedge aclk[1]);
         preq[1] <= 1'b0;
      end

      wait_for_paccept(dut, 1'b1);
      message = $sformatf("Power-down request accepted by DUT%0d", dut);
      `msg_info(message);
   endtask

   task automatic power_up_req(input bit dut);
      string message;
      if (dut == 0) begin
         @(posedge aclk[0]);
         pstate[0] <= 1'b1;
         @(posedge aclk[0]);
         preq[0] <= 1'b1;
      end else begin
         @(posedge aclk[1]);
         pstate[1] <= 1'b1;
         @(posedge aclk[1]);
         preq[1] <= 1'b1;
      end

      message = $sformatf("Power-up request sent to DUT%0d", dut);
      `msg_info(message);

      wait_for_paccept(dut, 1'b0);

      if (dut == 0) begin
         @(posedge aclk[0]);
         preq[0] <= 1'b0;
      end else begin
         @(posedge aclk[1]);
         preq[1] <= 1'b0;
      end

      wait_for_paccept(dut, 1'b1);
      message = $sformatf("Power-up request accepted by DUT%0d", dut);
      `msg_info(message);
   endtask

   //----------------------------------------
   // DUTs
   //----------------------------------------

   QECIPHY #(
       .GT_TYPE(`GT_TYPE)
   ) dut0 (
       .RCLK     (rclk[0]),
       .FCLK     (fclk[0]),
       .ACLK     (aclk[0]),
       .ARSTn    (arstn[0]),
       .TX_TDATA (axis_tx[0].tdata),
       .TX_TVALID(axis_tx[0].tvalid),
       .TX_TREADY(axis_tx[0].tready),
       .RX_TDATA (axis_rx[0].tdata),
       .RX_TVALID(axis_rx[0].tvalid),
       .RX_TREADY(axis_rx[0].tready),
       .STATUS   (status[0]),
       .ECODE    (ecode[0]),
       .PSTATE   (pstate[0]),
       .PREQ     (preq[0]),
       .PACCEPT  (paccept[0])
   );

   QECIPHY #(
       .GT_TYPE(`GT_TYPE)
   ) dut1 (
       .RCLK     (rclk[1]),
       .FCLK     (fclk[1]),
       .ACLK     (aclk[1]),
       .ARSTn    (arstn[1]),
       .TX_TDATA (axis_tx[1].tdata),
       .TX_TVALID(axis_tx[1].tvalid),
       .TX_TREADY(axis_tx[1].tready),
       .RX_TDATA (axis_rx[1].tdata),
       .RX_TVALID(axis_rx[1].tvalid),
       .RX_TREADY(axis_rx[1].tready),
       .STATUS   (status[1]),
       .ECODE    (ecode[1]),
       .PSTATE   (pstate[1]),
       .PREQ     (preq[1]),
       .PACCEPT  (paccept[1])
   );

   //----------------------------------------
   // Main test flow
   //----------------------------------------

   initial begin
      // Wait for both resets deasserted
      @(posedge arstn[0]);
      @(posedge arstn[1]);

      check_link_training();
      check_link_ready();

      `msg_info("Starting data transmission on both links");

      // Start drivers in parallel
      fork
         drive_tx0_data();
         drive_tx1_data();
      join_none

      // Run until TX[0] reaches sleep index
      `msg_info("Sending valid data before sleep");
      while (tx0_idx < SLEEP_AT_TX_INDEX) @(posedge aclk[0]);

      power_down_req(1'b0);
      #(SLEEP_DURATION);
      power_up_req(1'b0);

      compare_rx0_tx1();
      compare_rx1_tx0();

      `msg_info("Test passed okay");
      $finish;
   end

endmodule
