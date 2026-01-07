// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_rx_controller_harness;

   logic clk_i;
   logic rst_n_i;
   logic enable_i;
   logic rx_locked_i;
   logic crc_err_i;
   logic faw_err_i;
   logic rx_enable_o;
   logic rx_rdy_o;
   logic rx_fault_fatal_o;
   logic [3:0] rx_error_code_o;

   qeciphy_rx_controller dut (.*);

   // Input Assumptions

   // Helper logic to track continuous rx_enable_o high time
   // Models: rx_boundary_gen restarts lock process if rx_enable_o ever goes low
   // Requires at least 100 cycles of uninterrupted rx_enable_o high time before lock can assert
   logic [7:0] rx_enable_age_cnt;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i || !rx_enable_o) begin
         rx_enable_age_cnt <= 8'd0;
      end else if (rx_enable_o && rx_enable_age_cnt < 8'd255) begin
         rx_enable_age_cnt <= rx_enable_age_cnt + 8'd1;
      end
   end

   // rx_locked_i can only be asserted after rx_enable_o has been high for at least 100 cycles
   property p_rx_locked_needs_enable_delay;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          rx_locked_i
      ) |-> (rx_enable_age_cnt >= 8'd100);
   endproperty

   p_rx_locked_needs_enable_delay_A :
   assume property (p_rx_locked_needs_enable_delay);

   // rx_locked_i is sticky - once asserted, stays high until rx_enable_o falls
   property p_rx_locked_sticky_until_enable_falls;
      @(posedge clk_i) disable iff (!rst_n_i) rx_locked_i && rx_enable_o |-> ##1 rx_locked_i;
   endproperty

   p_rx_locked_sticky_until_enable_falls_A :
   assume property (p_rx_locked_sticky_until_enable_falls);

   // rx_locked_i goes low when rx_enable_o goes low
   property p_rx_locked_falls_with_enable;
      @(posedge clk_i) disable iff (!rst_n_i) $fell(
          rx_enable_o
      ) |-> ##1 !rx_locked_i;
   endproperty

   p_rx_locked_falls_with_enable_A :
   assume property (p_rx_locked_falls_with_enable);

   // crc_err_i can only be asserted at least 1 cycle after rx_locked_i is asserted
   property p_crc_err_requires_locked_delay;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          crc_err_i
      ) |-> $past(
          rx_locked_i
      );
   endproperty

   p_crc_err_requires_locked_delay_A :
   assume property (p_crc_err_requires_locked_delay);

   // faw_err_i can only be asserted at least 1 cycle after rx_locked_i is asserted
   property p_faw_err_requires_locked_delay;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          faw_err_i
      ) |-> $past(
          rx_locked_i
      );
   endproperty

   p_faw_err_requires_locked_delay_A :
   assume property (p_faw_err_requires_locked_delay);

   // crc_err_i and faw_err_i are mutually exclusive (only one can be asserted at a time)
   property p_errors_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(crc_err_i && faw_err_i);
   endproperty

   p_errors_mutually_exclusive_A :
   assume property (p_errors_mutually_exclusive);

   // crc_err_i is sticky - once asserted, stays high until rx_enable_o falls
   property p_crc_err_sticky_until_enable_falls;
      @(posedge clk_i) disable iff (!rst_n_i) crc_err_i && rx_enable_o |-> ##1 crc_err_i;
   endproperty

   p_crc_err_sticky_until_enable_falls_A :
   assume property (p_crc_err_sticky_until_enable_falls);

   // faw_err_i is sticky - once asserted, stays high until rx_enable_o falls  
   property p_faw_err_sticky_until_enable_falls;
      @(posedge clk_i) disable iff (!rst_n_i) faw_err_i && rx_enable_o |-> ##1 faw_err_i;
   endproperty

   p_faw_err_sticky_until_enable_falls_A :
   assume property (p_faw_err_sticky_until_enable_falls);

   // Error signals go low when rx_enable_o goes low
   property p_errors_fall_with_enable;
      @(posedge clk_i) disable iff (!rst_n_i) $fell(
          rx_enable_o
      ) |-> ##1 (!crc_err_i && !faw_err_i);
   endproperty

   p_errors_fall_with_enable_A :
   assume property (p_errors_fall_with_enable);

   // Helper logic to track enable_i low duration
   logic [4:0] enable_low_cnt;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i || enable_i) begin
         enable_low_cnt <= 5'd0;
      end else if (!enable_i && enable_low_cnt < 5'd31) begin
         enable_low_cnt <= enable_low_cnt + 5'd1;
      end
   end

   // enable_i must stay low for at least 16 cycles whenever it falls
   property p_enable_minimum_low_duration;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          enable_i
      ) |-> (enable_low_cnt >= 5'd16);
   endproperty

   p_enable_minimum_low_duration_A :
   assume property (p_enable_minimum_low_duration);

endmodule
