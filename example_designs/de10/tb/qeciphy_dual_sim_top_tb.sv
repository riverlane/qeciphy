// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Testbench for dual QECIPHY simulation top-level

`timescale 1ps / 1ps
`default_nettype none

module qeciphy_dual_sim_top_tb;

   //----------------------------------------
   // Macros
   //----------------------------------------
   `define msg_info(_str) $display("INFO:  (%0.2fus) %s", $realtime/1000.0, ``_str)
   `define msg_fatal(_str) $display("FATAL: (%0.2fus) %s", $realtime/1000.0, ``_str)

   //----------------------------------------
   // Local parameters
   //----------------------------------------
   localparam int MAX_CYCLES = 32'h0002_0000;
   localparam int TEST_SEQUENCE_LEN = 2048;
   localparam string TEST_DATASET = "counter";  // "counter" or "random"

   //----------------------------------------
   // Typedefs
   //----------------------------------------
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

   // Clock signals
   logic        gt_refclk_in_p_1;
   logic        gt_refclk_in_p_2;
   logic        clk_100_p;

   // Internal clock signals (generated inside DUT, extracted for TB use)
   logic        ACLK_1;
   logic        ACLK_2;

   // QECIPHY Instance 1 signals
   logic [63:0] TX_TDATA_1;
   logic        TX_TVALID_1;
   logic        TX_TREADY_1;
   logic [63:0] RX_TDATA_1;
   logic        RX_TVALID_1;
   logic        RX_TREADY_1;
   logic [ 3:0] STATUS_1;
   logic [ 3:0] ECODE_1;
   logic        LINK_READY_1;
   logic        FAULT_FATAL_1;
   logic        GT_RX_N_1;
   logic        GT_RX_P_1;
   logic        GT_TX_N_1;
   logic        GT_TX_P_1;

   // QECIPHY Instance 2 signals  
   logic [63:0] TX_TDATA_2;
   logic        TX_TVALID_2;
   logic        TX_TREADY_2;
   logic [63:0] RX_TDATA_2;
   logic        RX_TVALID_2;
   logic        RX_TREADY_2;
   logic [ 3:0] STATUS_2;
   logic [ 3:0] ECODE_2;
   logic        LINK_READY_2;
   logic        FAULT_FATAL_2;
   logic        GT_RX_N_2;
   logic        GT_RX_P_2;
   logic        GT_TX_N_2;
   logic        GT_TX_P_2;

   //----------------------------------------
   // TB storage
   //----------------------------------------
   logic [63:0] tx1_test_data    [0:TEST_SEQUENCE_LEN-1];
   logic [63:0] tx2_test_data    [0:TEST_SEQUENCE_LEN-1];
   logic [63:0] rx1_captured_data[0:TEST_SEQUENCE_LEN-1];
   logic [63:0] rx2_captured_data[0:TEST_SEQUENCE_LEN-1];

   int          rx1_idx;
   int          rx2_idx;
   int          tx1_idx;
   int          tx2_idx;

   logic        rx1_capture_done;
   logic        rx2_capture_done;
   logic [31:0] cycle_cnt;


   // Extract ACLK signals from DUT for testbench use
   assign ACLK_1 = qeciphy_dual_sim_top.sys_clk_100;
   assign ACLK_2 = qeciphy_dual_sim_top.sys_clk_100;

   //----------------------------------------
   // Reference Clock Generation
   //----------------------------------------
   // Generate 156.25 MHz reference clocks for both instances
   initial begin
      gt_refclk_in_p_1 = 1'b0;
      forever #3.2ns gt_refclk_in_p_1 = ~gt_refclk_in_p_1;  // 156.25 MHz
   end

   initial begin
      gt_refclk_in_p_2 = 1'b0;
      forever #3.2ns gt_refclk_in_p_2 = ~gt_refclk_in_p_2;  // 156.25 MHz
   end

   initial begin
      clk_100_p = 1'b0;
      forever #5ns clk_100_p = ~clk_100_p;  // 100 MHz system clock
   end

   //----------------------------------------
   // Reset generation
   //----------------------------------------
   // Reset is generated internally by the DUT (reset_release IP + counter).
   // Wait for DUT ARSTn to deassert in the main test flow.

   //----------------------------------------
   // Initial TB conditions
   //----------------------------------------
   // AXI-Stream RX ready per spec
   initial begin
      RX_TREADY_1 = 1'b1;
      RX_TREADY_2 = 1'b1;
   end

   // TX defaults
   initial begin
      TX_TVALID_1 = 1'b0;
      TX_TVALID_2 = 1'b0;
      TX_TDATA_1  = '0;
      TX_TDATA_2  = '0;
   end

   // Test data generation
   initial begin
      if (TEST_DATASET == "counter") begin
         for (int t = 0; t < TEST_SEQUENCE_LEN; t++) begin
            tx1_test_data[t] = 64'(t);
            tx2_test_data[t] = 64'(t + 1000);  // Different pattern
         end
      end else begin : gen_random
         for (int t = 0; t < TEST_SEQUENCE_LEN; t++) begin
            tx1_test_data[t] = {$urandom, $urandom};
            tx2_test_data[t] = {$urandom, $urandom};
         end
      end

      TX_TDATA_1 = tx1_test_data[0];
      TX_TDATA_2 = tx2_test_data[0];
   end

   //----------------------------------------
   // Capture RX data
   //----------------------------------------
   always_ff @(posedge ACLK_1 or negedge qeciphy_dual_sim_top.ARSTn) begin
      if (!qeciphy_dual_sim_top.ARSTn) begin
         rx1_captured_data <= '{default: '0};
         rx1_idx           <= 0;
         rx1_capture_done  <= 1'b0;
      end else begin
         if (RX_TVALID_1 && RX_TREADY_1) begin
            rx1_captured_data[rx1_idx] <= RX_TDATA_1;
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

   always_ff @(posedge ACLK_2 or negedge qeciphy_dual_sim_top.ARSTn) begin
      if (!qeciphy_dual_sim_top.ARSTn) begin
         rx2_captured_data <= '{default: '0};
         rx2_idx           <= 0;
         rx2_capture_done  <= 1'b0;
      end else begin
         if (RX_TVALID_2 && RX_TREADY_2) begin
            rx2_captured_data[rx2_idx] <= RX_TDATA_2;
            rx2_idx                    <= rx2_idx + 1;
         end

         if (rx2_idx == TEST_SEQUENCE_LEN) begin
            rx2_capture_done <= 1'b1;
         end else if (rx2_idx > TEST_SEQUENCE_LEN) begin
            `msg_fatal("RX[2] captured more samples than expected");
            $fatal();
         end
      end
   end

   // Cycle counter & watchdog
   always_ff @(posedge ACLK_1 or negedge qeciphy_dual_sim_top.ARSTn) begin
      if (!qeciphy_dual_sim_top.ARSTn) begin
         cycle_cnt <= '0;
      end else begin
         cycle_cnt <= cycle_cnt + 1'b1;
      end
   end


   // Cross-connect GT signals for loopback testing
   assign GT_RX_P_1 = GT_TX_P_2;
   assign GT_RX_N_1 = GT_TX_N_2;
   assign GT_RX_P_2 = GT_TX_P_1;
   assign GT_RX_N_2 = GT_TX_N_1;

`ifdef TILE_SIM_MODEL
   //----------------------------------------
   // FTile sim model parallel data cross-connect
   //----------------------------------------
   // Instance 1 RX receives Instance 2 TX parallel data
   assign qeciphy_dual_sim_top.i_QECIPHY_1
              .i_qeciphy_serdes.i_qeciphy_gt_wrapper
              .gen_altera.i_qeciphy_gt_altera
              .sim_ftile_rx_parallel_data
        = qeciphy_dual_sim_top.i_QECIPHY_2
              .i_qeciphy_serdes.i_qeciphy_gt_wrapper
              .gen_altera.i_qeciphy_gt_altera
              .sim_ftile_tx_parallel_data;

   // Instance 2 RX receives Instance 1 TX parallel data
   assign qeciphy_dual_sim_top.i_QECIPHY_2
              .i_qeciphy_serdes.i_qeciphy_gt_wrapper
              .gen_altera.i_qeciphy_gt_altera
              .sim_ftile_rx_parallel_data
        = qeciphy_dual_sim_top.i_QECIPHY_1
              .i_qeciphy_serdes.i_qeciphy_gt_wrapper
              .gen_altera.i_qeciphy_gt_altera
              .sim_ftile_tx_parallel_data;

`endif

   //
   // DUT instantiation
   qeciphy_dual_sim_top qeciphy_dual_sim_top (
       // Base clocks
       .gt_refclk_in_p_1(gt_refclk_in_p_1),
       .gt_refclk_in_p_2(gt_refclk_in_p_2),
       .clk_100_p       (clk_100_p),

       // QECIPHY Instance 1
       .TX_TDATA_1   (TX_TDATA_1),
       .TX_TVALID_1  (TX_TVALID_1),
       .TX_TREADY_1  (TX_TREADY_1),
       .RX_TDATA_1   (RX_TDATA_1),
       .RX_TVALID_1  (RX_TVALID_1),
       .RX_TREADY_1  (RX_TREADY_1),
       .STATUS_1     (STATUS_1),
       .ECODE_1      (ECODE_1),
       .LINK_READY_1 (LINK_READY_1),
       .FAULT_FATAL_1(FAULT_FATAL_1),
       .GT_RX_N_1    (GT_RX_N_1),
       .GT_RX_P_1    (GT_RX_P_1),
       .GT_TX_N_1    (GT_TX_N_1),
       .GT_TX_P_1    (GT_TX_P_1),

       // QECIPHY Instance 2
       .TX_TDATA_2   (TX_TDATA_2),
       .TX_TVALID_2  (TX_TVALID_2),
       .TX_TREADY_2  (TX_TREADY_2),
       .RX_TDATA_2   (RX_TDATA_2),
       .RX_TVALID_2  (RX_TVALID_2),
       .RX_TREADY_2  (RX_TREADY_2),
       .STATUS_2     (STATUS_2),
       .ECODE_2      (ECODE_2),
       .LINK_READY_2 (LINK_READY_2),
       .FAULT_FATAL_2(FAULT_FATAL_2),
       .GT_RX_N_2    (GT_RX_N_2),
       .GT_RX_P_2    (GT_RX_P_2),
       .GT_TX_N_2    (GT_TX_N_2),
       .GT_TX_P_2    (GT_TX_P_2)
   );

   //----------------------------------------
   // Tasks
   //----------------------------------------
   task automatic check_link_training;
      while (!(fsm_t'(STATUS_1) == LINK_TRAINING && fsm_t'(STATUS_2) == LINK_TRAINING)) begin
         @(posedge ACLK_1);
      end
      `msg_info("Link training started");
   endtask

   task automatic check_link_ready;
      while (!(LINK_READY_1 && LINK_READY_2)) begin
         @(posedge ACLK_1);
      end
      `msg_info("Link training complete");
   endtask

   // Instance 1 TX driver
   task automatic drive_tx1_data;
      tx1_idx = 0;

      @(posedge ACLK_1);
      TX_TDATA_1  <= tx1_test_data[tx1_idx];
      TX_TVALID_1 <= 1'b1;

      while (tx1_idx < TEST_SEQUENCE_LEN) begin
         @(posedge ACLK_1);
         if (TX_TREADY_1) begin
            tx1_idx++;
            if (tx1_idx == TEST_SEQUENCE_LEN) begin
               TX_TVALID_1 <= 1'b0;
            end else begin
               TX_TDATA_1  <= tx1_test_data[tx1_idx];
               TX_TVALID_1 <= 1'b1;
            end
         end
      end
   endtask

   // Instance 2 TX driver
   task automatic drive_tx2_data;
      tx2_idx = 0;

      @(posedge ACLK_2);
      TX_TDATA_2  <= tx2_test_data[tx2_idx];
      TX_TVALID_2 <= 1'b1;

      while (tx2_idx < TEST_SEQUENCE_LEN) begin
         @(posedge ACLK_2);
         if (TX_TREADY_2) begin
            tx2_idx++;
            if (tx2_idx == TEST_SEQUENCE_LEN) begin
               TX_TVALID_2 <= 1'b0;
            end else begin
               TX_TDATA_2  <= tx2_test_data[tx2_idx];
               TX_TVALID_2 <= 1'b1;
            end
         end
      end
   endtask

   task automatic compare_rx1_tx2;
      while (!rx1_capture_done) @(posedge ACLK_1);
      `msg_info("Validating data: Instance 2 TX -> Instance 1 RX");
      for (int idx = 0; idx < TEST_SEQUENCE_LEN; idx++) begin
         assert (tx2_test_data[idx] == rx1_captured_data[idx])
         else begin
            $display("Sample index: %4d - TX_DATA[2]: %h != RX_DATA[1]: %h", idx, tx2_test_data[idx], rx1_captured_data[idx]);
            `msg_fatal("RX[1] data does not match TX[2] data");
            $fatal();
         end
      end
   endtask

   task automatic compare_rx2_tx1;
      while (!rx2_capture_done) @(posedge ACLK_2);
      `msg_info("Validating data: Instance 1 TX -> Instance 2 RX");
      for (int idx = 0; idx < TEST_SEQUENCE_LEN; idx++) begin
         assert (tx1_test_data[idx] == rx2_captured_data[idx])
         else begin
            $display("Sample index: %4d - TX_DATA[1]: %h != RX_DATA[2]: %h", idx, tx1_test_data[idx], rx2_captured_data[idx]);
            `msg_fatal("RX[2] data does not match TX[1] data");
            $fatal();
         end
      end
   endtask

   //----------------------------------------
   // Main test flow
   //----------------------------------------
   initial begin
      // Wait for DUT internal reset to deassert
      wait (qeciphy_dual_sim_top.rst_n == 1'b1);
      `msg_info("System reset released");
      wait (qeciphy_dual_sim_top.ARSTn == 1'b1);
      `msg_info("PHY reset deasserted");

      check_link_training();
      check_link_ready();

      `msg_info("Starting data transmission on both links");

      // Start drivers in parallel
      fork
         drive_tx1_data();
         drive_tx2_data();
      join_none

      compare_rx1_tx2();
      compare_rx2_tx1();

      `msg_info("Test passed okay");
      $finish;
   end

   //   // Timeout using cycle counter
   //   always_ff @(posedge ACLK_1) begin
   //      if (cycle_cnt >= MAX_CYCLES) begin
   //         `msg_info("TIMEOUT: Simulation terminated after max cycles");
   //         $finish;
   //      end
   //   end
   //
   //   // Additional time-based timeout as backup
   //   initial begin
   //      #10ms;
   //      `msg_info("TIMEOUT: Simulation terminated (time-based)");
   //      $finish;
   //   end

endmodule
