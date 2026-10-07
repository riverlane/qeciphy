// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Evan Sun
//
// Back-to-back test of two QECIPHY_QUAD DUTs (lane i of DUT0 <-> lane i of DUT1),
// like tb/qeciphy_tb.sv. Each lane runs in its own generate block to avoid
// fork/join_none loop-variable capture.

`timescale 1ns / 1ps
`default_nettype none

`include "../src/qeciphy_pkg.sv"
`include "../src/qeciphy_build_cfg_pkg.sv"
`include "../tb/qeciphy_sim_cfg_pkg.sv"

module qeciphy_quad_tb;

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
   localparam int NUM_LANES = 4;  // "quad" - matches QECIPHY_QUAD's default

   localparam real ACLK_PERIOD_NS = 4.0;  // >= 156.25 MHz

   localparam int MAX_CYCLES = 32'h0003_0000;

   localparam int TEST_SEQUENCE_LEN = 2048;
   localparam string TEST_DATASET = "random";  // "counter" or "random"

   //----------------------------------------
   // Signals
   //----------------------------------------

   // RCLK/FCLK shared by all lanes; ACLK/ARSTn are per lane but toggle together here.
   logic                   rclk            [0:1];
   logic                   fclk            [0:1];
   logic [  NUM_LANES-1:0] aclk            [0:1];
   logic [  NUM_LANES-1:0] arstn           [0:1];

   logic [            3:0] status          [0:1] [NUM_LANES];
   logic [            3:0] ecode           [0:1] [NUM_LANES];
   logic [  NUM_LANES-1:0] link_ready      [0:1];
   logic [  NUM_LANES-1:0] fault_fatal     [0:1];

   logic [           63:0] tx_tdata        [0:1] [NUM_LANES];
   logic [  NUM_LANES-1:0] tx_tvalid       [0:1];
   logic [  NUM_LANES-1:0] tx_tready       [0:1];

   logic [           63:0] rx_tdata        [0:1] [NUM_LANES];
   logic [  NUM_LANES-1:0] rx_tvalid       [0:1];
   logic [  NUM_LANES-1:0] rx_tready       [0:1];

   // GT differential signals - vector cross-connect below wires up every lane
   logic [  NUM_LANES-1:0] gt_tx_p         [0:1];
   logic [  NUM_LANES-1:0] gt_tx_n         [0:1];
   logic [  NUM_LANES-1:0] gt_rx_p         [0:1];
   logic [  NUM_LANES-1:0] gt_rx_n         [0:1];

   logic [           31:0] cycle_cnt;

   // Bit (d*NUM_LANES+l) set once that lane's data is checked; one writer per bit.
   logic [2*NUM_LANES-1:0] done_flags;

   //----------------------------------------
   // TB storage
   //----------------------------------------

   logic [           63:0] tx_test_data    [0:1] [NUM_LANES] [0:TEST_SEQUENCE_LEN-1];
   logic [           63:0] rx_captured_data[0:1] [NUM_LANES] [0:TEST_SEQUENCE_LEN-1];

   int                     rx_idx          [0:1] [NUM_LANES];
   logic                   rx_capture_done [0:1] [NUM_LANES];

   //----------------------------------------
   // Clocks & reset
   //----------------------------------------

   initial begin
      rclk[0] = 1'b1;
      fclk[0] = 1'b1;
      aclk[0] = {NUM_LANES{1'b1}};

      rclk[1] = 1'b0;
      fclk[1] = 1'b0;
      aclk[1] = {NUM_LANES{1'b0}};
   end

   always #(QECIPHY_RCLK_PERIOD_NS / 2.0) rclk[0] = ~rclk[0];
   always #(QECIPHY_FCLK_PERIOD_NS / 2.0) fclk[0] = ~fclk[0];
   always #(ACLK_PERIOD_NS / 2.0) aclk[0] = ~aclk[0];

   always #(QECIPHY_RCLK_PERIOD_NS / 2.0) rclk[1] = ~rclk[1];
   always #(QECIPHY_FCLK_PERIOD_NS / 2.0) fclk[1] = ~fclk[1];
   always #(ACLK_PERIOD_NS / 2.0) aclk[1] = ~aclk[1];

   // Resets: assert at t=0, deassert (all lanes of a DUT together) after some cycles
   initial begin
      arstn[0] = '0;
      arstn[1] = '0;

      repeat (5) @(posedge aclk[0][0]);
      arstn[0] = {NUM_LANES{1'b1}};
      `msg_info("PHY reset deasserted on DUT0 (all lanes)");

      repeat (5) @(posedge aclk[1][0]);
      arstn[1] = {NUM_LANES{1'b1}};
      `msg_info("PHY reset deasserted on DUT1 (all lanes)");
   end

   //----------------------------------------
   // Initial TB conditions
   //----------------------------------------

   // AXI-Stream RX ready per spec
   initial begin
      rx_tready[0] = {NUM_LANES{1'b1}};
      rx_tready[1] = {NUM_LANES{1'b1}};
   end

   //----------------------------------------
   // High-speed serial connectivity
   //----------------------------------------
   // Lane i of DUT0 <-> lane i of DUT1.

   assign gt_rx_p[0] = gt_tx_p[1];
   assign gt_rx_n[0] = gt_tx_n[1];
   assign gt_rx_p[1] = gt_tx_p[0];
   assign gt_rx_n[1] = gt_tx_n[0];

   //----------------------------------------
   // Per-DUT, per-lane test data / drive / capture / check
   //----------------------------------------

   generate
      for (genvar d = 0; d < 2; d++) begin : gen_dut
         for (genvar l = 0; l < NUM_LANES; l++) begin : gen_lane

            localparam int OtherDut = 1 - d;

            // ---- Test data generation ----
            initial begin
               if (TEST_DATASET == "counter") begin
                  for (int t = 0; t < TEST_SEQUENCE_LEN; t++) begin
                     tx_test_data[d][l][t] = 64'(t);
                  end
               end else begin : gen_random
                  for (int t = 0; t < TEST_SEQUENCE_LEN; t++) begin
                     tx_test_data[d][l][t] = {$urandom, $urandom};
                  end
               end
            end

            // ---- RX capture ----
            always_ff @(posedge aclk[d][l] or negedge arstn[d][l]) begin
               if (!arstn[d][l]) begin
                  rx_captured_data[d][l] <= '{default: '0};
                  rx_idx[d][l]           <= 0;
                  rx_capture_done[d][l]  <= 1'b0;
               end else begin
                  if (rx_tvalid[d][l] && rx_tready[d][l]) begin
                     rx_captured_data[d][l][rx_idx[d][l]] <= rx_tdata[d][l];
                     rx_idx[d][l]                         <= rx_idx[d][l] + 1;
                  end

                  if (rx_idx[d][l] == TEST_SEQUENCE_LEN) begin
                     rx_capture_done[d][l] <= 1'b1;
                  end else if (rx_idx[d][l] > TEST_SEQUENCE_LEN) begin
                     `msg_fatal($sformatf("RX[dut%0d][lane%0d] captured more samples than expected", d, l));
                     $fatal();
                  end
               end
            end

            // ---- TX driver: starts once this lane's link is ready ----
            initial begin
               int idx;

               tx_tdata[d][l]  = '0;
               tx_tvalid[d][l] = 1'b0;

               wait (arstn[d][l]);
               while (status[d][l] !== LINK_TRAINING) @(posedge aclk[d][l]);
               `msg_info($sformatf("Link training started on DUT%0d lane%0d", d, l));
               wait (link_ready[d][l]);
               `msg_info($sformatf("Link training complete on DUT%0d lane%0d", d, l));

               idx = 0;
               @(posedge aclk[d][l]);
               tx_tdata[d][l]  <= tx_test_data[d][l][idx];
               tx_tvalid[d][l] <= 1'b1;

               while (idx < TEST_SEQUENCE_LEN) begin
                  @(posedge aclk[d][l]);
                  if (tx_tready[d][l]) begin
                     idx++;
                     if (idx == TEST_SEQUENCE_LEN) begin
                        tx_tvalid[d][l] <= 1'b0;
                     end else begin
                        tx_tdata[d][l]  <= tx_test_data[d][l][idx];
                        tx_tvalid[d][l] <= 1'b1;
                     end
                  end
               end
            end

            // ---- Compare this lane's captured RX data against the peer DUT's TX data ----
            initial begin
               // wait(), not while(!x): rx_capture_done is X until its first clock edge, and
               // while(!X) exits immediately.
               wait (rx_capture_done[d][l]);
               `msg_info($sformatf("Validating data: DUT%0d lane%0d TX -> DUT%0d lane%0d RX", OtherDut, l, d, l));

               for (int idx = 0; idx < TEST_SEQUENCE_LEN; idx++) begin
                  assert (tx_test_data[OtherDut][l][idx] == rx_captured_data[d][l][idx])
                  else begin
                     $display("DUT%0d lane%0d idx %4d - TX_DATA: %h != RX_DATA: %h", OtherDut, l, idx, tx_test_data[OtherDut][l][idx], rx_captured_data[d][l][idx]);
                     `msg_fatal($sformatf("RX[dut%0d][lane%0d] data does not match peer TX data", d, l));
                     $fatal();
                  end
               end

               done_flags[d*NUM_LANES+l] = 1'b1;
            end

         end
      end
   endgenerate

   // Cycle counter & watchdog (tracked off DUT0 lane0, which resets first)
   always_ff @(posedge aclk[0][0] or negedge arstn[0][0]) begin
      if (!arstn[0][0]) begin
         cycle_cnt <= '0;
      end else begin
         cycle_cnt <= cycle_cnt + 1'b1;
      end
   end

   always_ff @(posedge aclk[0][0]) begin
      if (cycle_cnt == MAX_CYCLES) begin
         `msg_fatal("Watchdog timeout");
         $fatal();
      end
   end

   //----------------------------------------
   // DUTs
   //----------------------------------------

   generate
      for (genvar d = 0; d < 2; d++) begin : gen_quad_dut
         QECIPHY_QUAD #(
             .NUM_LANES(NUM_LANES)
         ) dut (
             .RCLK (rclk[d]),
             .FCLK (fclk[d]),
             .ACLK (aclk[d]),
             .ARSTn(arstn[d]),

             .TX_TDATA (tx_tdata[d]),
             .TX_TVALID(tx_tvalid[d]),
             .TX_TREADY(tx_tready[d]),

             .RX_TDATA (rx_tdata[d]),
             .RX_TVALID(rx_tvalid[d]),
             .RX_TREADY(rx_tready[d]),

             .STATUS     (status[d]),
             .ECODE      (ecode[d]),
             .LINK_READY (link_ready[d]),
             .FAULT_FATAL(fault_fatal[d]),

             .GT_RX_P(gt_rx_p[d]),
             .GT_RX_N(gt_rx_n[d]),
             .GT_TX_P(gt_tx_p[d]),
             .GT_TX_N(gt_tx_n[d])
         );
      end
   endgenerate

   //----------------------------------------
   // Main test flow
   //----------------------------------------

   // Two identically mis-configured DUTs can still link at the wrong rate, so also check
   // the shortest GT_TX_P interval (one UI with 8b10b data) against 1/line rate.
   localparam real EXPECTED_UI_PS = 1000.0 / QECIPHY_LINE_RATE_GBPS;
   localparam real UI_TOLERANCE = 0.05;

   logic ui_measure = 1'b0;
   real  min_tx_edge_interval_ps[0:1][NUM_LANES];

   always @(posedge (&link_ready[0] && &link_ready[1])) ui_measure = 1'b1;

   generate
      for (genvar d = 0; d < 2; d++) begin : gen_ui_measure
         for (genvar l = 0; l < NUM_LANES; l++) begin : gen_lane
            realtime last_edge = 0;
            initial min_tx_edge_interval_ps[d][l] = 1.0e9;
            always @(gt_tx_p[d][l]) begin
               if (ui_measure && (gt_tx_p[d][l] === 1'b0 || gt_tx_p[d][l] === 1'b1)) begin
                  if (last_edge > 0 && ($realtime - last_edge) * 1000.0 < min_tx_edge_interval_ps[d][l]) min_tx_edge_interval_ps[d][l] = ($realtime - last_edge) * 1000.0;
                  last_edge = $realtime;
               end
            end
         end
      end
   endgenerate

   task automatic check_line_rate();
      for (int d = 0; d < 2; d++) begin
         for (int l = 0; l < NUM_LANES; l++) begin
            real ui = min_tx_edge_interval_ps[d][l];
            `msg_info($sformatf("DUT%0d lane%0d TX unit interval %0.2f ps (expected %0.2f ps for %0.4f Gbps)", d, l, ui, EXPECTED_UI_PS, QECIPHY_LINE_RATE_GBPS));
            if (ui < EXPECTED_UI_PS * (1.0 - UI_TOLERANCE) || ui > EXPECTED_UI_PS * (1.0 + UI_TOLERANCE)) begin
               `msg_fatal($sformatf("DUT%0d lane%0d is running at %0.4f Gbps, not %0.4f Gbps", d, l, 1000.0 / ui, QECIPHY_LINE_RATE_GBPS));
               $fatal();
            end
         end
      end
   endtask

   // Phase 2: reset one DUT0 lane alone and check the other lanes and both shared QPLL0s
   // stay up (nothing recovers from a QPLL lock loss - see QECIPHY_QUAD).
   localparam int SINGLE_RESET_LANE = 1;  // not lane 0 - the watchdog counter runs off DUT0 lane 0
   localparam int SINGLE_RESET_HOLD_CYCLES = 16;
   localparam int SINGLE_RESET_OBSERVE_CYCLES = 32'h0000_8000;

   logic single_reset_monitor = 1'b0;

   generate
      for (genvar d = 0; d < 2; d++) begin : gen_single_reset_monitor
         always @(posedge aclk[d][0]) begin
            if (single_reset_monitor) begin
               for (int l = 0; l < NUM_LANES; l++) begin
                  if (l != SINGLE_RESET_LANE && (link_ready[d][l] !== 1'b1 || fault_fatal[d][l] !== 1'b0)) begin
                     `msg_fatal($sformatf(
                                "DUT%0d lane%0d disturbed by DUT0 lane%0d reset (LINK_READY=%b FAULT_FATAL=%b STATUS=%h)", d, l, SINGLE_RESET_LANE, link_ready[d][l], fault_fatal[d][l], status[d][l]));
                     $fatal();
                  end
               end
`ifdef QECIPHY_GT_COMMON_EXTERNAL
               if (gen_quad_dut[d].dut.qpll0lock !== 1'b1) begin
                  `msg_fatal($sformatf("DUT%0d shared QPLL0 lost lock during DUT0 lane%0d reset", d, SINGLE_RESET_LANE));
                  $fatal();
               end
`endif
            end
         end
      end
   endgenerate

   initial begin
      done_flags = '0;
      wait (&done_flags);
      `msg_info("All lanes on both DUTs verified");
      ui_measure = 1'b0;
      check_line_rate();

      `msg_info($sformatf("Resetting DUT0 lane%0d on its own", SINGLE_RESET_LANE));
      single_reset_monitor = 1'b1;
      arstn[0][SINGLE_RESET_LANE] = 1'b0;
      repeat (SINGLE_RESET_HOLD_CYCLES) @(posedge aclk[0][SINGLE_RESET_LANE]);
      arstn[0][SINGLE_RESET_LANE] = 1'b1;

      // Long enough for the lane's GT reset sequence. Re-training depends on the protocol's
      // one-sided reset handling, so it's reported, not checked.
      fork
         begin
            wait (link_ready[0][SINGLE_RESET_LANE] === 1'b1);
            `msg_info($sformatf("DUT0 lane%0d re-trained after its reset", SINGLE_RESET_LANE));
         end
      join_none
      repeat (SINGLE_RESET_OBSERVE_CYCLES) @(posedge aclk[0][0]);
      if (link_ready[0][SINGLE_RESET_LANE] !== 1'b1) begin
         `msg_info($sformatf("DUT0 lane%0d had not re-trained by the end of the observation window (informational)", SINGLE_RESET_LANE));
      end
      single_reset_monitor = 1'b0;

      `msg_info("Test passed okay - all lanes on both DUTs verified at the configured line rate, and a single-lane reset left the others undisturbed");
      $finish;
   end

endmodule
