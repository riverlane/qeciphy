// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: Aniket Datta, Dogancan Davutoglu, Gargi Sunil

module qeciphy_tb;

   `define msg_info(_str) $display("INFO: (%0.2fus) %s", $realtime/1000, ``_str)
   `define msg_fatal(_str) $display("FATAL: (%0.2fus) %s", $realtime/1000, ``_str)
`ifndef GT_TYPE  // GT transceiver type
   `define GT_TYPE "GTY" // default value
`endif

   // ---------------------------------------
   // Local parameters
   //----------------------------------------
   localparam RCLK_PERIOD = (`GT_TYPE == "GTX") ? 8 :  // Kasli GTX reference clock period [ns]
   (`GT_TYPE == "GTH") ? 6.4 :  // ZCU106 GTH reference clock period [ns]
   6.4;  // ZCU216 GTY reference clock period [ns][default]
   localparam FCLK_PERIOD = (`GT_TYPE == "GTX") ? 8 :  // Kasli free-running clock period [ns]
   (`GT_TYPE == "GTH") ? 6.4 :  // ZCU106 GTH reference clock period [ns]
   6.4;  // ZCU216 free-running clock period [ns][default]
   localparam ACLK_PERIOD = 4;  // AXI async clock period [ns]; ACLK frequency must be greater than or equal to 10000/64 = 156.25 MHz
   localparam MAX_CYCLES = 32'h0002_0000;
   localparam QPLL_PERIOD = 0.08;  // Transceiver serial bit clock period [ns]
   localparam integer BIT_SLIDE = (`GT_TYPE == "GTX") ? 16 :  // Initial bit slide on the GTX serial pins [qpll cycles] (to shorten the simulation time)
   (`GT_TYPE == "GTH") ? 3 :  // Initial bit slide on the GTH serial pins [qpll cycles] (to shorten the simulation time)
   9;  // Initial bit slide on the GTY serial pins [qpll cycles] (to shorten the simulation time)
   localparam integer MAX_SLIDE = 40;  // Possible bit slides for 32-bit interface (40-bit after encoding) [qpll cycles]

   localparam integer TEST_SEQUENCE_LEN = 2048;
   localparam string TEST_DATASET = "random";  // Options: "counter", "random"
   localparam time SLEEP_DURATION = 10000;  // Duration of TX[0] sleep [ns]
   localparam integer SLEEP_AT_TX_INDEX = 1000;  // The TX[0] data index at which sleep request occurs

   //----------------------------------------
   // Typedef
   //----------------------------------------

   typedef struct packed {
      logic p;
      logic n;
   } diff_pair_t;

   typedef struct packed {
      logic [63:0] tdata;
      logic        tvalid;
      logic        tready;
   } axis_t;

   typedef enum bit [3:0] {
      RESET,
      DATAPATH_RESET,
      WAIT_FOR_RESET,
      LINK_TRAINING,
      LINK_READY,
      FAULT_FATAL,
      SLEEP,
      WAIT_FOR_POWERDOWN
   } fsm_t;

   typedef enum bit [3:0] {
      OK,
      FAP_MISSING,
      CRC_ERROR
   } error_t;


   //----------------------------------------
   // Signals
   //----------------------------------------

   logic          rclk      [0:1];
   logic          fclk      [0:1];
   logic          aclk      [0:1];
   logic          arstn     [0:1];
   logic          pstate    [0:1];
   logic          preq      [0:1];
   logic          paccept   [0:1];
   fsm_t          status    [0:1];
   error_t        ecode     [0:1];
   axis_t         axis_tx   [0:1];
   axis_t         axis_rx   [0:1];
   logic   [31:0] cycle_cnt;

   logic          qpllclk;

   //----------------------------------------
   // Clocks and reset
   //----------------------------------------

   // clocks
   always #(RCLK_PERIOD / 2) rclk[0] = ~rclk[0];
   always #(FCLK_PERIOD / 2) fclk[0] = ~fclk[0];
   always #(ACLK_PERIOD / 2) aclk[0] = ~aclk[0];

   always #(RCLK_PERIOD / 2) rclk[1] = ~rclk[1];
   always #(FCLK_PERIOD / 2) fclk[1] = ~fclk[1];
   always #(ACLK_PERIOD / 2) aclk[1] = ~aclk[1];

   always #(QPLL_PERIOD / 2) qpllclk = ~qpllclk;

   initial begin
      rclk[0] = 1'b1;
      fclk[0] = 1'b1;
      aclk[0] = 1'b1;
      rclk[1] = 1'b0;
      fclk[1] = 1'b0;
      aclk[1] = 1'b0;
      qpllclk = 1'b0;
   end

   // Do not assert reset at the beginning
   initial begin
      arstn[0] = 1'b1;
      arstn[1] = 1'b1;
   end

   //----------------------------------------
   // TB signals
   //----------------------------------------
   logic   [         63:0] tx0_test_data    [0:TEST_SEQUENCE_LEN-1];
   logic   [         63:0] tx1_test_data    [0:TEST_SEQUENCE_LEN-1];
   logic   [         63:0] rx0_captured_data[0:TEST_SEQUENCE_LEN-1];
   logic   [         63:0] rx1_captured_data[0:TEST_SEQUENCE_LEN-1];
   integer                 rx0_idx;
   integer                 rx1_idx;
   integer                 tx0_idx;
   integer                 tx1_idx;
   logic                   rx0_capture_done;
   logic                   rx1_capture_done;
   logic   [MAX_SLIDE-1:0] dut1_txn;
   logic   [MAX_SLIDE-1:0] dut1_txp;
   logic   [MAX_SLIDE-1:0] dut0_txn;
   logic   [MAX_SLIDE-1:0] dut0_txp;

   // Requirement by spec
   initial begin
      axis_rx[0].tready = 1'b1;
      axis_rx[1].tready = 1'b1;
   end

   // TX data & valid initialisation
   initial begin
      axis_tx[0].tvalid = 1'b0;
      axis_tx[1].tvalid = 1'b0;
   end

   // P-Channel initialisation
   initial begin
      pstate[0] = 1'b1;
      preq[0]   = 1'b0;
      pstate[1] = 1'b1;
      preq[1]   = 1'b0;
   end

   //  Test data generation
   initial begin
      if (TEST_DATASET == "counter") begin
         for (int t = 0; t < TEST_SEQUENCE_LEN; t++) begin
            tx0_test_data[t] = 64'(t);
            tx1_test_data[t] = 64'(t);
         end
      end else if (TEST_DATASET == "random") begin
         std::randomize(tx0_test_data);
         std::randomize(tx1_test_data);
      end
      axis_tx[0].tdata = tx0_test_data[0];
      axis_tx[1].tdata = tx1_test_data[0];
   end

   // Getting high-speed serial pins of transceivers from their entities
   // and connecting the RX ports to Tx ports with some bit slide
   generate
      if (`GT_TYPE == "GTX") begin
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
      end else if (`GT_TYPE == "GTY") begin
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
      end else if (`GT_TYPE == "GTH") begin
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

   // Capture RX data into arrays
   always_ff @(posedge aclk[0] or negedge arstn[0]) begin
      if (!arstn[0]) begin
         rx0_captured_data <= '{default: 0};
         rx0_idx <= 0;
         rx0_capture_done <= 1'b0;
      end else begin
         if (axis_rx[0].tvalid && axis_rx[0].tready) begin
            rx0_captured_data[rx0_idx] <= axis_rx[0].tdata;
            rx0_idx <= rx0_idx + 1;
         end
      end
      if (rx0_idx == TEST_SEQUENCE_LEN) begin
         rx0_capture_done <= 1'b1;
      end else if (rx0_idx > TEST_SEQUENCE_LEN) begin
         `msg_fatal("RX[0] captured more samples than expected");
         $fatal();
      end
   end

   always_ff @(posedge aclk[1] or negedge arstn[1]) begin
      if (!arstn[1]) begin
         rx1_captured_data <= '{default: 0};
         rx1_idx <= 0;
         rx1_capture_done <= 1'b0;
      end else begin
         if (axis_rx[1].tvalid && axis_rx[1].tready) begin
            rx1_captured_data[rx1_idx] <= axis_rx[1].tdata;
            rx1_idx <= rx1_idx + 1;
         end
      end
      if (rx1_idx == TEST_SEQUENCE_LEN) begin
         rx1_capture_done <= 1'b1;
      end else if (rx1_idx > TEST_SEQUENCE_LEN) begin
         `msg_fatal("RX[1] captured more samples than expected");
         $fatal();
      end
   end

   always_ff @(posedge aclk[0] or negedge arstn[0]) begin
      if (!arstn[0]) cycle_cnt <= {32{1'b0}};
      else cycle_cnt <= cycle_cnt + 1'b1;
   end

   always_ff @(posedge aclk[0]) begin
      // Watchdog timeout: If MAX_CYCLES have elapsed, terminate
      // simulation.
      if (cycle_cnt == MAX_CYCLES) begin
         `msg_fatal("Watchdog timeout");
         $fatal();
      end
   end

   // Tasks
   task check_link_training;
      while (~(status[0] == LINK_TRAINING && status[1] == LINK_TRAINING)) begin
         @(posedge aclk[0]);
      end
      `msg_info("Link training started");
   endtask

   task check_link_ready;
      while (~(status[0] == LINK_READY && status[1] == LINK_READY)) begin
         @(posedge aclk[0]);
      end
      `msg_info("Link training complete");
   endtask

   task drive_tx0_data;
      tx0_idx = 0;
      axis_tx[0].tvalid = 1'b1;
      @(posedge aclk[0]);
      while (tx0_idx < TEST_SEQUENCE_LEN) begin
         if (axis_tx[0].tready) begin
            tx0_idx = tx0_idx + 1;
            if (tx0_idx == TEST_SEQUENCE_LEN) begin
               axis_tx[0].tvalid = 1'b0;
            end else begin
               axis_tx[0].tvalid = 1'b1;
               axis_tx[0].tdata  = tx0_test_data[tx0_idx];
            end
         end
         @(posedge aclk[0]);
      end
   endtask

   task drive_tx1_data;
      tx1_idx = 0;
      axis_tx[1].tvalid = 1'b1;
      @(posedge aclk[1]);
      while (tx1_idx < TEST_SEQUENCE_LEN) begin
         if (axis_tx[1].tready) begin
            tx1_idx = tx1_idx + 1;
            if (tx1_idx == TEST_SEQUENCE_LEN) begin
               axis_tx[1].tvalid = 1'b0;
            end else begin
               axis_tx[1].tvalid = 1'b1;
               axis_tx[1].tdata  = tx1_test_data[tx1_idx];
            end
         end
         @(posedge aclk[1]);
      end
   endtask

   task compare_rx0_tx1;
      while (~rx0_capture_done) begin
         @(posedge aclk[0]);
      end
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

   task compare_rx1_tx0;
      while (~rx1_capture_done) begin
         @(posedge aclk[1]);
      end
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

   task wait_for_paccept(input bit dut, input bit val);
      string message;
      while (paccept[dut] == val) begin
         @(posedge aclk[dut]);
      end
   endtask

   task power_down_req(input bit dut);
      string message;
      pstate[dut] = 1'b0;
      @(posedge aclk[dut]);
      preq[dut] = 1'b1;
      message   = $sformatf("Power-down request sent to DUT%d", dut);
      `msg_info(message);
      wait_for_paccept(dut, 0);
      @(posedge aclk[dut]);
      preq[dut] = 1'b0;
      wait_for_paccept(dut, 1);
      message = $sformatf("Power-down request accepted by DUT%d", dut);
      `msg_info(message);
   endtask

   task power_up_req(input bit dut);
      string message;
      pstate[dut] = 1'b1;
      @(posedge aclk[dut]);
      preq[dut] = 1'b1;
      message   = $sformatf("Power-up request sent to DUT%d", dut);
      `msg_info(message);
      wait_for_paccept(dut, 0);
      @(posedge aclk[dut]);
      preq[dut] = 1'b0;
      wait_for_paccept(dut, 1);
      message = $sformatf("Power-up request accepted by DUT%d", dut);
      `msg_info(message);
   endtask

   QECIPHY #(
       .GT_TYPE(`GT_TYPE)
   ) dut0 (
       .RCLK(rclk[0]),
       .FCLK(fclk[0]),
       .ACLK(aclk[0]),
       .ARSTn(arstn[0]),
       .TX_TDATA(axis_tx[0].tdata),
       .TX_TVALID(axis_tx[0].tvalid),
       .TX_TREADY(axis_tx[0].tready),
       .RX_TDATA(axis_rx[0].tdata),
       .RX_TVALID(axis_rx[0].tvalid),
       .RX_TREADY(axis_rx[0].tready),
       .STATUS(status[0]),
       .ECODE(ecode[0]),
       .PSTATE(pstate[0]),
       .PREQ(preq[0]),
       .PACCEPT(paccept[0])
   );

   QECIPHY #(
       .GT_TYPE(`GT_TYPE)
   ) dut1 (
       .RCLK(rclk[1]),
       .FCLK(fclk[1]),
       .ACLK(aclk[1]),
       .ARSTn(arstn[1]),
       .TX_TDATA(axis_tx[1].tdata),
       .TX_TVALID(axis_tx[1].tvalid),
       .TX_TREADY(axis_tx[1].tready),
       .RX_TDATA(axis_rx[1].tdata),
       .RX_TVALID(axis_rx[1].tvalid),
       .RX_TREADY(axis_rx[1].tready),
       .STATUS(status[1]),
       .ECODE(ecode[1]),
       .PSTATE(pstate[1]),
       .PREQ(preq[1]),
       .PACCEPT(paccept[1])
   );

   // Drive TX0 data
   initial begin
      drive_tx0_data;
   end

   // Drive TX1 data
   initial begin
      drive_tx1_data;
   end

   // Main test flow
   initial begin
      #10 @(posedge aclk[0]) arstn[0] = 1'b0;
      `msg_info("PHY reset asserted on DUT0");
      #15 @(posedge aclk[1]) arstn[1] = 1'b0;
      `msg_info("PHY reset asserted on DUT1");
      #50 @(posedge aclk[0]) arstn[0] = 1'b1;
      `msg_info("PHY reset deasserted on DUT0");
      #15 @(posedge aclk[1]) arstn[1] = 1'b1;
      `msg_info("PHY reset deasserted on DUT1");

      // Check link status
      check_link_training;
      check_link_ready;

      // Run until the TX[0] index reaches to the target before sleep
      `msg_info("Sending valid data");
      while (tx0_idx < SLEEP_AT_TX_INDEX) begin
         @(posedge aclk[0]);
      end

      // Do a sleep & wake-up on TX[0]
      power_down_req(0);
      #5000;
      power_up_req(0);

      // Compare received data
      compare_rx0_tx1;
      compare_rx1_tx0;

      `msg_info("Test passed okay");

      $finish;
   end
endmodule  // qeciphy_tb
