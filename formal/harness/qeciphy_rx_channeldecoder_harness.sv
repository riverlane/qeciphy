// SPDX-License-Identifier: BSD-2-Clause
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

module qeciphy_rx_channeldecoder_harness;

   logic        clk_i;
   logic        rst_n_i;
   logic [63:0] tdata_i;
   logic [63:0] tdata_o;
   logic        tvalid_o;
   logic        enable_i;
   logic        rx_fault_fatal_o;
   logic [ 3:0] rx_error_code_o;
   logic        rx_rdy_o;
   logic        remote_rx_rdy_o;

   qeciphy_rx_channeldecoder dut (.*);

   // Input Assumptions

   // Helper logic to track enable_i low duration
   logic [4:0] enable_low_cnt;

   always_ff @(posedge clk_i) begin
      if (!rst_n_i || enable_i) begin
         enable_low_cnt <= 5'd0;
      end else if (!enable_i && enable_low_cnt < 5'd31) begin
         enable_low_cnt <= enable_low_cnt + 5'd1;
      end
   end

   // enable_i must stay low for at least 16 cycles whenever it's low
   property p_enable_minimum_low_duration;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          enable_i
      ) |-> (enable_low_cnt >= 5'd16);
   endproperty

   p_enable_minimum_low_duration_A :
   assume property (p_enable_minimum_low_duration);

endmodule
