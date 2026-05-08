// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Simple testbench for qeciphy_syn_wrapper

`timescale 1ps / 1ps

module qeciphy_syn_wrapper_tb;

   // Testbench signals
   logic gt_refclk_in_p;
   logic clk_100_p;

   // DUT signals
   logic GT_RXP_1;
   logic GT_RXN_1;
   logic GT_TXP_1;
   logic GT_TXN_1;
   logic i2c_qsfpdd0_enable;
   wire i2c_qsfpdd0_scl;
   wire i2c_qsfpdd0_sda;
   logic qsfpdd_1v2_port_en;
   logic qsfpdd_1v2_port_int_n;
   logic [2:0] qsfpdd0_fpga_led;
   logic [3:0] fpga_led;

   // Test control signals
   logic test_pass;
   logic test_complete;
   integer error_count;

   // Clock generation
   initial begin
      gt_refclk_in_p = 1'b0;
      forever #3.2ns gt_refclk_in_p = ~gt_refclk_in_p;  // 156.25 MHz reference clock
   end

   initial begin
      clk_100_p = 1'b0;
      forever #5ns clk_100_p = ~clk_100_p;  // 100 MHz system clock
   end

`ifdef TILE_SIM_MODEL
   //Nothing to connect if you're using just one tile sim model
`endif

   // DUT instantiation
   qeciphy_syn_wrapper qeciphy_syn_wrapper (
       .gt_refclk_in_p       (gt_refclk_in_p),
       .clk_100_p            (clk_100_p),
       .GT_RXP               (GT_RXP_1),
       .GT_RXN               (GT_RXN_1),
       .GT_TXP               (GT_TXP_1),
       .GT_TXN               (GT_TXN_1),
       .i2c_qsfpdd0_enable   (i2c_qsfpdd0_enable),
       .i2c_qsfpdd0_scl      (i2c_qsfpdd0_scl),
       .i2c_qsfpdd0_sda      (i2c_qsfpdd0_sda),
       .qsfpdd_1v2_port_en   (qsfpdd_1v2_port_en),
       .qsfpdd_1v2_port_int_n(qsfpdd_1v2_port_int_n),
       .qsfpdd0_fpga_led     (qsfpdd0_fpga_led),
       .fpga_led             (fpga_led)
   );

   // QSFP-DD module signals initialization
   initial begin
      // Control signals
      qsfpdd_1v2_port_int_n = 1'b1;  // No interrupt (active low)
   end

   // Connect GTY signals for loopback testing
   assign GT_RXP_1 = GT_TXP_1;  // Loopback connection
   assign GT_RXN_1 = GT_TXN_1;

   // I2C pull-ups (simple model)
   pullup (i2c_qsfpdd0_scl);
   pullup (i2c_qsfpdd0_sda);

   // Test stimulus and monitoring
   initial begin
      $display("=== QECIPHY Synthesis Wrapper Testbench ===");
      $display("Starting simulation at time %0t", $time);

      // Initialize variables
      test_pass = 1'b1;
      test_complete = 1'b0;
      error_count = 0;

      // Wait for reset and initialization
      wait (qeciphy_syn_wrapper.rst_n == 1'b1);
      $display("Reset deasserted at time %0t", $time);

      // Wait for QECI-PHY initialization
      repeat (100) @(posedge qeciphy_syn_wrapper.FCLK);

      // Monitor key signals
      fork
         monitor_clocks();
         monitor_reset_sequence();
         monitor_qeciphy_status();
         monitor_data_path();
      join_any

      // Wait for test completion or timeout
      fork
         begin
            #1ms;  // Timeout
            $display("ERROR: Test timeout reached");
            error_count++;
            test_complete = 1'b1;
         end
         begin
            wait (test_complete);
         end
      join_any

      // Test results
      if (error_count == 0) begin
         $display("=== TEST PASSED ===");
         $display("All checks completed successfully");
      end else begin
         $display("=== TEST FAILED ===");
         $display("Total errors: %0d", error_count);
      end

      $display("Simulation completed at time %0t", $time);
      $finish;
   end

   // Monitor clock generation
   task monitor_clocks();
      $display("Monitoring clocks...");

      // Wait for clocks to be stable
      repeat (10) @(posedge gt_refclk_in_p);

      // Check if internal clocks are generated
      if (qeciphy_syn_wrapper.RCLK !== 1'bx && qeciphy_syn_wrapper.FCLK !== 1'bx) begin
         $display("PASS: Internal clocks generated - RCLK and FCLK active");
      end else begin
         $display("ERROR: Internal clocks not properly generated");
         error_count++;
      end

      // Monitor clock frequencies (simple check)
      repeat (1000) @(posedge qeciphy_syn_wrapper.FCLK);
      $display("PASS: FCLK running for extended period");
   endtask

   // Monitor reset sequence
   task monitor_reset_sequence();
      $display("Monitoring reset sequence...");

      // Wait for reset to be released
      wait (qeciphy_syn_wrapper.rst_n == 1'b1);
      $display("System reset released");

      // Wait for internal reset counter
      wait (qeciphy_syn_wrapper.ARSTn == 1'b1);
      $display("PASS: Internal reset sequence completed (ARSTn active)");

      // Verify reset counter functionality
      if (qeciphy_syn_wrapper.rst_counter == 5'h10) begin
         $display("PASS: Reset counter reached expected value");
      end else begin
         $display("WARNING: Reset counter value unexpected: %0h", qeciphy_syn_wrapper.rst_counter);
      end
   endtask

   // Monitor QECI-PHY status
   task monitor_qeciphy_status();
      $display("Monitoring QECI-PHY status...");

      // Wait for initialization
      repeat (50) @(posedge qeciphy_syn_wrapper.FCLK);

      // Monitor status changes
      forever begin
         @(qeciphy_syn_wrapper.STATUS or qeciphy_syn_wrapper.ECODE);
         $display("Status: STATUS=0x%h, ECODE=0x%h at time %0t", qeciphy_syn_wrapper.STATUS, qeciphy_syn_wrapper.ECODE, $time);

         // Check for specific status values
         if (qeciphy_syn_wrapper.STATUS == 4'b0100) begin
            $display("PASS: QECI-PHY reached operational status");
         end

         if (qeciphy_syn_wrapper.ECODE != 4'b0000) begin
            $display("WARNING: QECI-PHY error code detected: 0x%h", qeciphy_syn_wrapper.ECODE);
         end
      end
   endtask

   // Monitor data path
   task monitor_data_path();
      integer tx_count, rx_count;
      logic [63:0] last_tx_data, last_rx_data;

      $display("Monitoring data path for loopback communication...");

      tx_count = 0;
      rx_count = 0;
      last_tx_data = 64'h0;
      last_rx_data = 64'h0;

      fork
         // Monitor TX path
         forever begin
            @(posedge qeciphy_syn_wrapper.FCLK);
            if (qeciphy_syn_wrapper.TX_TVALID && qeciphy_syn_wrapper.TX_TREADY) begin
               tx_count++;
               if (qeciphy_syn_wrapper.TX_TDATA != last_tx_data + 1 && tx_count > 1) begin
                  $display("WARNING: TX data sequence error. Expected: 0x%h, Got: 0x%h", last_tx_data + 1, qeciphy_syn_wrapper.TX_TDATA);
               end
               last_tx_data = qeciphy_syn_wrapper.TX_TDATA;

               if (tx_count == 50) begin
                  $display("PASS: TX transmitted 50 packets successfully");
               end
            end
         end

         // Monitor RX path (loopback)
         forever begin
            @(posedge qeciphy_syn_wrapper.FCLK);
            if (qeciphy_syn_wrapper.RX_TVALID && qeciphy_syn_wrapper.RX_TREADY) begin
               rx_count++;
               last_rx_data = qeciphy_syn_wrapper.RX_TDATA;

               if (rx_count == 50) begin
                  $display("PASS: RX received 50 packets in loopback");
                  test_complete = 1'b1;
               end
            end
         end

         // Monitor data integrity
         forever begin
            @(posedge qeciphy_syn_wrapper.FCLK);
            if (qeciphy_syn_wrapper.RXDATA_error) begin
               $display("ERROR: RX data error detected at time %0t", $time);
               error_count++;
            end
         end
      join_any
   endtask

   // Waveform dumping
   initial begin
      $dumpfile("qeciphy_syn_wrapper_tb.vcd");
      $dumpvars(0, qeciphy_syn_wrapper_tb);
   end

   // Signal value change monitoring for debugging
   initial begin
      $monitor("Time=%0t | rst_n=%b ARSTn=%b TX_V=%b RX_V=%b", $time, qeciphy_syn_wrapper.rst_n, qeciphy_syn_wrapper.ARSTn, qeciphy_syn_wrapper.TX_TVALID, qeciphy_syn_wrapper.RX_TVALID);
   end

endmodule
