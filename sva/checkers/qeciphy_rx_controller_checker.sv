// SPDX-License-Identifier: LicenseRef-LICENSE
// Copyright (c) 2026 Riverlane Ltd.
// Original authors: Aniket Datta

`include "qeciphy_pkg.sv"

module qeciphy_rx_controller_checker (
    input logic clk_i,
    input logic rst_n_i,
    input logic enable_i,
    input logic rx_locked_i,
    input logic crc_err_i,
    input logic faw_err_i,
    input logic rx_enable_o,
    input logic rx_rdy_o,
    input logic rx_fault_fatal_o,
    input logic [3:0] rx_error_code_o
);

   import qeciphy_pkg::*;

   assign any_error = crc_err_i || faw_err_i;

   // Ensure that rx_enable_o is reachable
   cover_rx_enable_high_C :
   cover property (@(posedge clk_i) rx_enable_o);

   // Ensure that rx_rdy_o is reachable
   cover_rx_rdy_high_C :
   cover property (@(posedge clk_i) rx_rdy_o);

   // Ensure that rx_fault_fatal_o is reachable
   cover_rx_fault_fatal_high_C :
   cover property (@(posedge clk_i) rx_fault_fatal_o);

   // rx_enable_o goes HIGH immediately on enable
   property p_rx_enable_rises_on_enable;
      @(posedge clk_i) disable iff (!rst_n_i) enable_i |-> ##1 rx_enable_o;
   endproperty

   p_rx_enable_rises_on_enable_A :
   assert property (p_rx_enable_rises_on_enable)
   else $fatal(1, "rx_enable_o should rise when enable_i is asserted at %m");

   // rx_enable_o goes LOW on reset or disable
   property p_rx_enable_falls_on_reset_or_disable;
      @(posedge clk_i) disable iff (!rst_n_i) !enable_i |-> ##1 !rx_enable_o;
   endproperty

   p_rx_enable_falls_on_reset_or_disable_A :
   assert property (p_rx_enable_falls_on_reset_or_disable)
   else $fatal(1, "rx_enable_o should be low when disabled at %m");

   // rx_enable_o stays HIGH when enabled and no errors
   property p_rx_enable_stable_when_enabled_no_errors;
      @(posedge clk_i) disable iff (!rst_n_i) enable_i && rx_enable_o && !any_error |-> ##1 rx_enable_o;
   endproperty

   p_rx_enable_stable_when_enabled_no_errors_A :
   assert property (p_rx_enable_stable_when_enabled_no_errors)
   else $fatal(1, "rx_enable_o should remain high when enabled and no errors at %m");

   // // rx_rdy_o goes HIGH when transitioning from TRAINING to READY (rx_locked_i && rx_enable_o && no errors)
   // property p_rx_rdy_rises_on_lock_and_no_errors;
   //    @(posedge clk_i) disable iff (!rst_n_i || !enable_i) !$past(rx_rdy_o) && rx_enable_o && rx_locked_i && !any_error && !$past(rx_fault_fatal_o) |-> ##1 rx_rdy_o;
   // endproperty

   // p_rx_rdy_rises_on_lock_and_no_errors_A :
   // assert property (p_rx_rdy_rises_on_lock_and_no_errors)
   // else $fatal(1, "rx_rdy_o should rise when locked and no errors at %m");

   // rx_rdy_o goes LOW immediately on any error
   property p_rx_rdy_falls_on_error;
      @(posedge clk_i) disable iff (!rst_n_i) any_error |-> ##1 !rx_rdy_o;
   endproperty

   p_rx_rdy_falls_on_error_A :
   assert property (p_rx_rdy_falls_on_error)
   else $fatal(1, "rx_rdy_o should fall immediately on error at %m");

   // rx_rdy_o goes LOW on disable
   property p_rx_rdy_falls_on_disable;
      @(posedge clk_i) disable iff (!rst_n_i) !enable_i |-> ##1 !rx_rdy_o;
   endproperty

   p_rx_rdy_falls_on_disable_A :
   assert property (p_rx_rdy_falls_on_disable)
   else $fatal(1, "rx_rdy_o should be low when disabled at %m");

   // rx_rdy_o stays HIGH only in READY state (enabled, locked, no errors, no fault)
   property p_rx_rdy_stable_when_ready_conditions_met;
      @(posedge clk_i) disable iff (!rst_n_i) enable_i && rx_rdy_o && rx_locked_i && !any_error |-> ##1 rx_rdy_o;
   endproperty

   p_rx_rdy_stable_when_ready_conditions_met_A :
   assert property (p_rx_rdy_stable_when_ready_conditions_met)
   else $fatal(1, "rx_rdy_o should remain high when ready conditions are met at %m");

   // rx_rdy_o cannot be high when not locked
   property p_rx_rdy_not_high_when_not_locked;
      @(posedge clk_i) disable iff (!rst_n_i) !rx_locked_i |-> !rx_rdy_o;
   endproperty

   p_rx_rdy_not_high_when_not_locked_A :
   assert property (p_rx_rdy_not_high_when_not_locked)
   else $fatal(1, "rx_rdy_o should not be high when not locked at %m");

   // rx_fault_fatal_o goes HIGH when error occurs while in READY state
   property p_rx_fault_fatal_rises_on_error_in_ready;
      @(posedge clk_i) disable iff (!rst_n_i) enable_i && rx_rdy_o && any_error |-> ##1 rx_fault_fatal_o;
   endproperty

   p_rx_fault_fatal_rises_on_error_in_ready_A :
   assert property (p_rx_fault_fatal_rises_on_error_in_ready)
   else $fatal(1, "rx_fault_fatal_o should rise on error in ready state at %m");

   // rx_fault_fatal_o is sticky when enabled
   property p_rx_fault_fatal_sticky_when_enabled;
      @(posedge clk_i) disable iff (!rst_n_i) rx_fault_fatal_o && enable_i |-> ##1 rx_fault_fatal_o;
   endproperty

   p_rx_fault_fatal_sticky_when_enabled_A :
   assert property (p_rx_fault_fatal_sticky_when_enabled)
   else $fatal(1, "rx_fault_fatal_o should be sticky when enabled at %m");

   // rx_fault_fatal_o goes LOW on reset or disable
   property p_rx_fault_fatal_falls_on_reset_or_disable;
      @(posedge clk_i) disable iff (!rst_n_i) !enable_i |-> ##1 !rx_fault_fatal_o;
   endproperty

   p_rx_fault_fatal_falls_on_reset_or_disable_A :
   assert property (p_rx_fault_fatal_falls_on_reset_or_disable)
   else $fatal(1, "rx_fault_fatal_o should be low when disabled at %m");

   // rx_fault_fatal_o should only rise due to errors, not spuriously
   property p_rx_fault_fatal_no_spurious_rise;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          rx_fault_fatal_o
      ) |-> $past(
          any_error && enable_i
      );
   endproperty

   p_rx_fault_fatal_no_spurious_rise_A :
   assert property (p_rx_fault_fatal_no_spurious_rise)
   else $fatal(1, "rx_fault_fatal_o should only rise due to errors at %m");

   // Ensure correct error code is set on fault
   property p_correct_error_code_on_fault;
      @(posedge clk_i) disable iff (!rst_n_i) $rose(
          rx_fault_fatal_o
      ) |-> $past(
          crc_err_i
      ) ? (rx_error_code_o == CRC_ERROR) : $past(
          faw_err_i
      ) ? (rx_error_code_o == FAW_ERROR) : 1'b0;
   endproperty

   p_correct_error_code_on_fault_A :
   assert property (p_correct_error_code_on_fault)
   else $fatal(1, "rx_error_code_o does not match expected error code at %m");

   // Ensure error code is NO_ERROR when no fault
   property p_correct_error_code_when_no_fault;
      @(posedge clk_i) disable iff (!rst_n_i) !rx_fault_fatal_o |-> (rx_error_code_o == NO_ERROR);
   endproperty

   p_correct_error_code_when_no_fault_A :
   assert property (p_correct_error_code_when_no_fault)
   else $fatal(1, "rx_error_code_o should be NO_ERROR when no fault at %m");

   // rx_error_code_o is sticky when enabled
   property p_error_code_sticky;
      @(posedge clk_i) disable iff (!rst_n_i) (rx_error_code_o != NO_ERROR) && enable_i |-> ##1 rx_error_code_o;
   endproperty

   p_error_code_sticky_A :
   assert property (p_error_code_sticky)
   else $fatal(1, "rx_error_code_o should be sticky when enabled at %m");

   // rx_rdy_o and rx_fault_fatal_o are mutually exclusive
   property p_rx_rdy_and_fault_mutually_exclusive;
      @(posedge clk_i) disable iff (!rst_n_i) !(rx_rdy_o && rx_fault_fatal_o);
   endproperty

   p_rx_rdy_and_fault_mutually_exclusive_A :
   assert property (p_rx_rdy_and_fault_mutually_exclusive)
   else $fatal(1, "rx_rdy_o and rx_fault_fatal_o should be mutually exclusive at %m");

   // All outputs are low on reset
   property p_all_outputs_low_on_reset;
      @(posedge clk_i) $rose(
          rst_n_i
      ) |-> (!rx_enable_o && !rx_rdy_o && !rx_fault_fatal_o);
   endproperty

   p_all_outputs_low_on_reset_A :
   assert property (p_all_outputs_low_on_reset)
   else $fatal(1, "All outputs should be low after reset at %m");

   // rx_rdy_o can only be high when rx_enable_o is high
   property p_rx_rdy_requires_rx_enable;
      @(posedge clk_i) disable iff (!rst_n_i) rx_rdy_o |-> rx_enable_o;
   endproperty

   p_rx_rdy_requires_rx_enable_A :
   assert property (p_rx_rdy_requires_rx_enable)
   else $fatal(1, "rx_rdy_o requires rx_enable_o to be high at %m");

endmodule
