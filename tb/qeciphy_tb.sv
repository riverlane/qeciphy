// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta, Dogancan Davutoglu, Gargi Sunil

`timescale 1ns / 1ps `default_nettype none

`include "../src/qeciphy_pkg.sv"
`include "qeciphy_sim_cfg_pkg.sv"

module qeciphy_tb;

   import qeciphy_pkg::*;
   import qeciphy_sim_cfg_pkg::*;

`ifdef XSIM
   `include "all_bind.svh"
`endif

   //----------------------------------------
   // Macros
   //----------------------------------------
   `define msg_info(_str) $display("INFO:  (%0.2fus) %s", $realtime/1000.0, ``_str)
   `define msg_fatal(_str) $display("FATAL: (%0.2fus) %s", $realtime/1000.0, ``_str)

   glbl glbl ();

   //----------------------------------------
   // Local parameters
   //----------------------------------------

   localparam real ACLK_PERIOD_NS = 4.0;  // >= 156.25 MHz

   localparam int MAX_CYCLES = 32'h0002_0000;

   localparam int TEST_SEQUENCE_LEN = 2048;
   localparam string TEST_DATASET = "random";  // "counter" or "random"

   //----------------------------------------
   // Typedefs
   //----------------------------------------

   typedef struct packed {
      logic [63:0] tdata;
      logic        tvalid;
      logic        tready;
   } axis_t;

   //----------------------------------------
   // Signals
   //----------------------------------------

   logic                   rclk             [                  0:1];
   logic                   fclk             [                  0:1];
   logic                   aclk             [                  0:1];
   logic                   arstn            [                  0:1];

   qeciphy_status_t        status           [                  0:1];
   qeciphy_error_t         ecode            [                  0:1];

   axis_t                  axis_tx          [                  0:1];
   axis_t                  axis_rx          [                  0:1];

   logic            [31:0] cycle_cnt;

   //----------------------------------------
   // TB storage
   //----------------------------------------

   logic            [63:0] tx0_test_data    [0:TEST_SEQUENCE_LEN-1];
   logic            [63:0] tx1_test_data    [0:TEST_SEQUENCE_LEN-1];
   logic            [63:0] rx0_captured_data[0:TEST_SEQUENCE_LEN-1];
   logic            [63:0] rx1_captured_data[0:TEST_SEQUENCE_LEN-1];

   int                     rx0_idx;
   int                     rx1_idx;
   int                     tx0_idx;
   int                     tx1_idx;

   logic                   rx0_capture_done;
   logic                   rx1_capture_done;

   // GT differential signals
   logic                   gt_tx_p          [                  0:1];
   logic                   gt_tx_n          [                  0:1];
   logic                   gt_rx_p          [                  0:1];
   logic                   gt_rx_n          [                  0:1];

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
   end

   always #(QECIPHY_RCLK_PERIOD_NS / 2.0) rclk[0] = ~rclk[0];
   always #(QECIPHY_FCLK_PERIOD_NS / 2.0) fclk[0] = ~fclk[0];
   always #(ACLK_PERIOD_NS / 2.0) aclk[0] = ~aclk[0];

   always #(QECIPHY_RCLK_PERIOD_NS / 2.0) rclk[1] = ~rclk[1];
   always #(QECIPHY_FCLK_PERIOD_NS / 2.0) fclk[1] = ~fclk[1];
   always #(ACLK_PERIOD_NS / 2.0) aclk[1] = ~aclk[1];

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

   assign gt_rx_p[0] = gt_tx_p[1];
   assign gt_rx_n[0] = gt_tx_n[1];
   assign gt_rx_p[1] = gt_tx_p[0];
   assign gt_rx_n[1] = gt_tx_n[0];

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

   //----------------------------------------
   // DUTs
   //----------------------------------------

   QECIPHY dut0 (
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
       .GT_RX_P  (gt_rx_p[0]),
       .GT_RX_N  (gt_rx_n[0]),
       .GT_TX_P  (gt_tx_p[0]),
       .GT_TX_N  (gt_tx_n[0])
   );

   QECIPHY dut1 (
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
       .GT_RX_P  (gt_rx_p[1]),
       .GT_RX_N  (gt_rx_n[1]),
       .GT_TX_P  (gt_tx_p[1]),
       .GT_TX_N  (gt_tx_n[1])
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

      compare_rx0_tx1();
      compare_rx1_tx0();

      `msg_info("Test passed okay");
      $finish;
   end

endmodule
