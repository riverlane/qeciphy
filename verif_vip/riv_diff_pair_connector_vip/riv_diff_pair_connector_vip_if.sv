// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane,ONDWARAKA


`ifndef RIV_DIFF_PAIR_CONNECTOR_VIP_IF_SV_
`define RIV_DIFF_PAIR_CONNECTOR_VIP_IF_SV_

`include "riv_diff_pair_connector_vip_globals.svh"

//------------------------------------------------------------------------------------------------------------------------------------------
// Interface: riv_diff_pair_connector_vip_if
//
// Interface to implement a connection between a differential-pair serial-data source and its sink.
// Allows the delays on the pairs to be independently set and for a range of error conditions to be generated.
//
// By default, this interface is passive (outputs are all Hi-Z) for use in environments inherited by higher-level TBs.
// Use the set_passive and set_active methods to change behaviour according to need.
//------------------------------------------------------------------------------------------------------------------------------------------
interface riv_diff_pair_connector_vip_if (
   input  logic rx_p,   // Positive receive data.
   input  logic rx_n,   // Inverted receive data.
   inout  wire logic tx_p,   // Positive transmitted data (normally forwarded from rx_p).
   inout  wire logic tx_n    // Inverted transmitted data (normally forwarded from rx_n).
);

   // HINT: Always declare time parameters as used by this module. MUST be done as first statements after interface declaration.
   timeunit      `RIV_DIFF_PAIR_CONNECTOR_VIP_TIMEUNIT;
   timeprecision `RIV_DIFF_PAIR_CONNECTOR_VIP_TIMEPRECISION;

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   bit is_active    = 1'b0;   // Set to 1 to enable outputs to drive, set to 0 (default) to set outputs to Hi-Z.

   int p_delay_ps   = 0;     // Transport delay (in ps) from rx_p to tx_p.
   int n_delay_ps   = 0;     // Transport delay (in ps) from rx_n to tx_n.
   bit swap         = 1'b0;  // 1 = rx_n -> tx_p and rx_p -> tx_n (delays as applied to the rx_* signal).
   bit short        = 1'b0;  // 1 = rx_p drives both tx_p and tx_n (delay as applied to the rx_p signal).
   bit disconnect_p = 1'b0;  // 1 = tx_p Hi-Z (no delay).
   bit disconnect_n = 1'b0;  // 1 = tx_n Hi-Z (no delay).
   bit force_en     = 1'b0;  // 1 = tx_* driven based on force_val (no delay).
   bit force_val    = 1'b0;  // When force_en == 1, tx_p = force_val, tx_n = ~force_val (no delay).

   logic dlyd_p;     // Locally delayed version of rx_p.
   logic dlyd_n;     // Locally delayed version of rx_n.

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Block: dly_rx_p, dly_rx_n
   //
   // Delay the two paths by the required amount of time use transport delays.
   //---------------------------------------------------------------------------------------------------------------------------------------
   always @(rx_p) begin : dly_rx_p
      dlyd_p <= #(p_delay_ps * 1.0ps) rx_p;
   end : dly_rx_p

   always @(rx_n) begin : dly_rx_n
      dlyd_n <= #(n_delay_ps * 1.0ps) rx_n;
   end : dly_rx_n
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Assign the outputs based on their configurations.
   //---------------------------------------------------------------------------------------------------------------------------------------
   assign tx_p = ( !is_active ? 1'bZ : (force_en ?  force_val : (disconnect_p ? 1'bZ : (short ? dlyd_p : (swap ? dlyd_n : dlyd_p)))) );
   assign tx_n = ( !is_active ? 1'bZ : (force_en ? ~force_val : (disconnect_n ? 1'bZ : (short ? dlyd_p : (swap ? dlyd_p : dlyd_n)))) );
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_active
   //
   // Allow tx_p and tx_n to be driven.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_active();
      const string msg_id = $sformatf("%m.set_active");

      is_active <= 1'b1;

   endtask : set_active
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_passive
   //
   // Set tx_p and tx_n to Hi-Z.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_passive();
      const string msg_id = $sformatf("%m.set_passive");

      is_active     <= 1'b0;

   endtask : set_passive
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_delay_ps
   //
   // Set the delay (in ps) for the "p", "n" or "both" connection paths (defaults to both).
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_delay_ps(int dly_ps, string path = "both");
      const string msg_id = $sformatf("%m.set_delay_ps");

      case (path)
         "p"      :  p_delay_ps = dly_ps;
         "n"      :  n_delay_ps = dly_ps;
         "both"   :  begin
                        p_delay_ps = dly_ps;
                        n_delay_ps = dly_ps;
                     end
         default  :  `uvm_fatal(msg_id, $sformatf("Invalid path : %0s", path))
      endcase

   endtask : set_delay_ps
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_connect_status
   //
   // Enable or disable the "p", "n" or "both" connection paths (defaults to enabling both).
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_connect_status(string path = "both", bit disconnect = 1'b0);
      const string msg_id = $sformatf("%m.set_connect_status");

      case (path)
         "p"      :  disconnect_p = disconnect;
         "n"      :  disconnect_n = disconnect;
         "both"   :  begin
                        disconnect_p = disconnect;
                        disconnect_n = disconnect;
                     end
         default  :  `uvm_fatal(msg_id, $sformatf("Invalid path : %0s", path))
      endcase

   endtask : set_connect_status
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_swap_status
   //
   // Swap or un-swap the "p" and "n" connection paths (defaults to swapping them).
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_swap_status(bit swap_paths = 1'b1);
      const string msg_id = $sformatf("%m.set_swap_status");

      swap = swap_paths;

   endtask : set_swap_status
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_short_status
   //
   // Enable or disable the short condition where tx_n will be driven from tx_p (defaults to enabling it).
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_short_status(bit short_paths = 1'b1);
      const string msg_id = $sformatf("%m.set_short_status");

      short = short_paths;

   endtask : set_short_status
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: release_short
   //
   // Release any existing short condition.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task release_short();
      const string msg_id = $sformatf("%m.release_short");

      short = 1'b0;

   endtask : release_short
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_force_status
   //
   // Enable or disable the forcing of the tx_* paths to the given value (defaults to enabling the force).
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_force_status(logic val, bit do_force = 1'b1);
      const string msg_id = $sformatf("%m.set_force_status");

      force_en  = do_force;
      force_val = val;

   endtask : set_force_status
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: release_force
   //
   // Release any existing force.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task release_force();
      const string msg_id = $sformatf("%m.release_force");

      force_en  = 1'b0;

   endtask : release_force
   //---------------------------------------------------------------------------------------------------------------------------------------


endinterface : riv_diff_pair_connector_vip_if
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_DIFF_PAIR_CONNECTOR_VIP_IF_SV_
