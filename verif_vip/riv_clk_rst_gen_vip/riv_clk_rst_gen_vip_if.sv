
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_CLK_RST_GEN_VIP_IF_SV_
`define RIV_CLK_RST_GEN_VIP_IF_SV_

`include "riv_clk_rst_gen_vip_globals.svh"

//------------------------------------------------------------------------------------------------------------------------------------------
// Interface: riv_clk_rst_gen_vip_if
//
// Interface to implement a programmable clock generator capable of producing multiple divided clocks (divisor >= 1).
// Clocks are all based on a single, free running master-clock and there are no delta-delay differences between clock outputs.
// Clocks are disabled whenever their clk_req input is low.
//    NOTE: Disabling a clock will keep it low once it goes low. Re-enabling it will cause a rising edge as if it had been free-running.
// Access the master-clock period using the set_master_period_ns and get_master_period_ns methods.
//    NOTE: Setting the master-clock period to 0 will stop all clocks (drive them to 0) and reset their division-periods.
// Access the divisor for any one clock output using the set_divisor and get_divisor methods.
//    NOTE: Setting a divisor to 0 will cause clock to go low on next rising master-clock edge and its division-period to reset.
//
// Each clock has its own programmable polarity reset (asynchronous assertion, asynchronous or synchronous release).
// Access the reset polarity for any one clock domain using the set_reset_level and get_reset_level methods.
// Assert/release a reset using the assert_reset and release_reset methods.
// Pulse a reset using the pulse_reset method.
//
// By default, this interface is passive (outputs are all Hi-Z) for use in environments inherited by higher-level TBs.
// Use the set_passive and set_active methods to change behaviour according to need.
//------------------------------------------------------------------------------------------------------------------------------------------
interface riv_clk_rst_gen_vip_if #(int NUM_CLKS = 1) (
   input  logic clk_reqs  [NUM_CLKS],     // Clock request for each clock.
   output logic clks      [NUM_CLKS],     // Clocks.
   output logic resets    [NUM_CLKS]      // Resets with release synchronized to associated clock.
);

   // HINT: Always declare time parameters as used by this module. MUST be done as first statements after interface declaration.
   timeunit      `RIV_CLK_RST_GEN_VIP_TIMEUNIT;
   timeprecision `RIV_CLK_RST_GEN_VIP_TIMEPRECISION;

   import uvm_pkg::*;
   `include "uvm_macros.svh"

   bit       is_active;                   // Set to 1 to enable outputs to drive, set to 0 (default) to set outputs to Hi-Z.

   bit       master_clk;                  // Internal, free-running master clock, from which all output clocks are divided.
   bit       master_clk_running;          // High when master clock is running.
   realtime  master_period;               // Period of free-running master-clock.
   int       divisors      [NUM_CLKS];    // Divisors (of master-clock period) to be used for each output clock.
   bit       reset_levels  [NUM_CLKS];    // Active reset levels for each domain (1 = active high, 0 = active low).
   int       clk_cntrs     [NUM_CLKS];    // Counters used for dividing of master-clock.
   bit       clks_intrnl   [NUM_CLKS];    // Clocks.
   bit       resets_intrnl [NUM_CLKS];    // Resets with release synchronized to associated clock.

   assign clks   = (is_active ? clks_intrnl   : '{default : 1'bZ});
   assign resets = (is_active ? resets_intrnl : '{default : 1'bZ});

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Block: master_clk_gen_blk
   //
   // Generates free running master clock whenever period is defined as > 0.
   //---------------------------------------------------------------------------------------------------------------------------------------
   initial forever begin : master_clk_gen_blk
      const string msg_id = $sformatf("%m.master_clk_gen_blk");

      `uvm_info(msg_id, $sformatf("Master-clock is disabled."), UVM_MEDIUM)
      master_clk         <= 1'b0;
      master_clk_running <= 1'b0;
      wait (master_period > 0.0);

      `uvm_info(msg_id, $sformatf("Starting master-clock with %0.3fns period...", master_period / 1.0ns), UVM_MEDIUM)
      master_clk_running <= 1'b1;
      fork
         wait (master_period <= 0.0);
         forever begin
            #(master_period / 2.0);
            master_clk <= ~master_clk;
         end
      join_any
      disable fork;

   end : master_clk_gen_blk
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Block: divided_clks_gen_blk
   //
   // Generates all the divided clocks whenever their divisor is > 0, master-clock is running and the clock is requested.
   //---------------------------------------------------------------------------------------------------------------------------------------
   initial forever begin : divided_clks_gen_blk

      clks_intrnl <= '{default : 1'b0};
      clk_cntrs   <= '{default : 0};
      wait (master_clk_running);

      fork

         wait (! master_clk_running);

         forever begin
            @(posedge master_clk);
            foreach (clks[i]) begin
               clk_cntrs[i] = (divisors[i] < 2) ? 0 : (clk_cntrs[i] + 1) % divisors[i];
               case (divisors[i])
                  0       : clks_intrnl[i] <= 1'b0;
                  1       : clks_intrnl[i] <= clk_reqs[i];
                  default :
                     begin
                        if (clk_cntrs[i] == 0)                 clks_intrnl[i] <= clk_reqs[i];
                        if (clk_cntrs[i] == (divisors[i] / 2)) clks_intrnl[i] <= 1'b0;
                     end
               endcase
            end
         end

         forever begin
            @(negedge master_clk);
            foreach (clks[i]) begin
               if (divisors[i] == 1) clks_intrnl[i] <= 1'b0;
            end
         end

      join_any
      disable fork;

   end : divided_clks_gen_blk
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_master_period_ns, get_master_period_ns
   //
   // Set or get the master-clock period (in ns).
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_master_period_ns(real period_ns);
      master_period = period_ns * 1.0ns;
   endtask : set_master_period_ns

   function real get_master_period_ns();
      return (master_period / 1.0ns);
   endfunction : get_master_period_ns
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_divisor, get_divisor
   //
   // Set or get the divisor for the specified clock.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_divisor(int clk_idx, int divisor);
      const string msg_id = $sformatf("%m.set_divisor");

      if (! clk_idx inside {[0 : NUM_CLKS-1]} ) begin
         `uvm_fatal(msg_id, $sformatf("clk_idx %0d not in range 0:%0d", clk_idx, NUM_CLKS))
         return;
      end

      if (divisor < 0) begin
         `uvm_fatal(msg_id, $sformatf("divisor %0d must be >= 0", divisor))
         return;
      end

      divisors[clk_idx] = divisor;

   endtask : set_divisor

   function int get_divisor(int clk_idx);
      const string msg_id = $sformatf("%m.get_divisor");

      if (! clk_idx inside {[0 : NUM_CLKS-1]} ) begin
         `uvm_fatal(msg_id, $sformatf("clk_idx %0d not in range 0:%0d", clk_idx, NUM_CLKS))
         return 0;
      end

      return (divisors[clk_idx]);

   endfunction : get_divisor
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_reset_level, get_reset_level
   //
   // Set or get the reset-level for the reset  belonging to the specified clock.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_reset_level(int clk_idx, bit level);
      const string msg_id = $sformatf("%m.set_reset_level");

      if (! clk_idx inside {[0 : NUM_CLKS-1]} ) begin
         `uvm_fatal(msg_id, $sformatf("clk_idx %0d not in range 0:%0d", clk_idx, NUM_CLKS))
         return;
      end

      reset_levels[clk_idx] = level;

   endtask : set_reset_level

   function bit get_reset_level(int clk_idx);
      const string msg_id = $sformatf("%m.get_reset_level");

      if (! clk_idx inside {[0 : NUM_CLKS-1]} ) begin
         `uvm_fatal(msg_id, $sformatf("clk_idx %0d not in range 0:%0d", clk_idx, NUM_CLKS))
         return 0;
      end

      return (reset_levels[clk_idx]);

   endfunction : get_reset_level
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: assert_reset
   //
   // Assert the required reset immediately.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task assert_reset(int clk_idx);
      const string msg_id = $sformatf("%m.assert_reset");

      if (! clk_idx inside {[0 : NUM_CLKS-1]} ) begin
         `uvm_fatal(msg_id, $sformatf("clk_idx %0d not in range 0:%0d", clk_idx, NUM_CLKS))
         return;
      end

      `uvm_info(msg_id, $sformatf("Asserting reset %0d (drive %0b)", clk_idx, reset_levels[clk_idx]), UVM_MEDIUM)
      resets_intrnl[clk_idx] = reset_levels[clk_idx];

   endtask : assert_reset
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: release_reset
   //
   // Release the required reset.
   // If synchronize = 0, release is immediate, otherwise will wait for next rising edge of associated clock.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task release_reset(int clk_idx, bit synchronize = 1'b0);
      const string msg_id = $sformatf("%m.release_reset");

      if (! clk_idx inside {[0 : NUM_CLKS-1]} ) begin
         `uvm_fatal(msg_id, $sformatf("clk_idx %0d not in range 0:%0d", clk_idx, NUM_CLKS))
         return;
      end

      if (synchronize) @(posedge clks[clk_idx]);
      `uvm_info(msg_id, $sformatf("Releasing reset %0d (drive %0b)", clk_idx, ~reset_levels[clk_idx]), UVM_MEDIUM)
      resets_intrnl[clk_idx] = ~reset_levels[clk_idx];

   endtask : release_reset
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: pulse_reset
   //
   // Pulse the required reset for the given number of clocks.
   // If wait_for_release = 1, task will only return after the release, otherwise it will return immediately leaving the pulse running.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task pulse_reset(int clk_idx, int num_clks = 1, wait_for_release = 1'b0);
      const string msg_id = $sformatf("%m.release_reset");

      if (! clk_idx inside {[0 : NUM_CLKS-1]} ) begin
         `uvm_fatal(msg_id, $sformatf("clk_idx %0d not in range 0:%0d", clk_idx, NUM_CLKS))
         return;
      end

      assert_reset(clk_idx);
      fork
         begin
            repeat(num_clks) @(posedge clks[clk_idx]);
            release_reset(clk_idx);
         end
      join_none

      if (wait_for_release) wait fork;

   endtask : pulse_reset
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_active
   //
   // Allow clocks and resets to be driven.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_active();
      const string msg_id = $sformatf("%m.set_active");

      is_active <= 1'b1;

   endtask : set_active
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_passive
   //
   // Set all outputs to Hi-Z and stop all clocks.
   //---------------------------------------------------------------------------------------------------------------------------------------
   task set_passive();
      const string msg_id = $sformatf("%m.set_passive");

      is_active     <= 1'b0;
      master_period <= 0.0;

   endtask : set_passive
   //---------------------------------------------------------------------------------------------------------------------------------------


endinterface : riv_clk_rst_gen_vip_if
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_CLK_RST_GEN_VIP_IF_SV_
