
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_POWER_STATE_TEST_SVH_
`define QECIPHY_POWER_STATE_TEST_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_power_state_test
//
// Abstract:
// Randomly cycles the DUT between low- and active-power states whilst data is being xferred.
// See qeciphy_power_state_test_seq and qeciphy_txrx_test_seq for more details.
// Test can be configured with the following options on the simulator command-line (see field descriptors for more details):
//    +DUT_CYCLES=n              // Specify m_num_dut_cycles (n = decimal integer >= 0).
//    +TBPHY_CYCLES=n            // Specify m_num_tbphy_cycles (n = decimal integer >= 0).
//    +MIN_GAP_NS=n              // Specify m_min_cycle_gap_ns (n = decimal integer > 0).
//    +MAX_GAP_NS=n              // Specify m_max_cycle_gap_ns (n = decimal integer > 0).
//    +MIN_DURATION_NS=n         // Specify m_min_cycle_duration_ns (n = decimal integer > 0).
//    +MAX_DURATION_NS=n         // Specify m_max_cycle_duration_ns (n = decimal integer > 0).
//    +MIN_AXIS_DELAY_CLKS=n     // Specify m_min_axis_delay_clks (n = decimal integer > 0).
//    +MAX_AXIS_DELAY_CLKS=n     // Specify m_max_axis_delay_clks (n = decimal integer > 0).
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_power_state_test extends qeciphy_base_test;

   // Control/status variables.
   int m_num_dut_cycles           =      -1;    // Number of DUT-iniitated cycles to do (default -1 = leave it random).
   int m_num_tbphy_cycles         =      -1;    // Number of TB-Phy-iniitated cycles to do (default -1 = leave it random).
   int m_min_cycle_gap_ns         =       0;    // Minimum time (in ns) from link up before each power cycle (default 0us).
   int m_max_cycle_gap_ns         = 100_000;    // Maximum time (in ns) from link up before each power cycle (default 200us).
   int m_min_cycle_duration_ns    =  30_000;    // Minimum time (in ns) before powered-down device powers back up (default 30us).
   int m_max_cycle_duration_ns    =  60_000;    // Maximum time (in ns) before powered-down device powers back up (default 60us).
   int m_min_axis_delay_clks      =       0;    // Minimum number of clocks between AXI-S xfers (default 0).
   int m_max_axis_delay_clks      =       5;    // Maximum number of clocks between AXI-S xfers (default 5).

   `uvm_component_utils_begin(qeciphy_power_state_test)
   `uvm_component_utils_end


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function new (string name = "", uvm_component parent);
      super.new(name, parent);
   endfunction
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: run_main_test_sequence
   //
   // Create, randomize and execute the main test sequence.
   // In this case, it makes sense to run traffic at the same time hence a txrx test is also run.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_main_test_sequence();
      const string  msg_id = { get_type_name(), ".run_main_test_sequence" };
      int           rand_ok;
      int           max_dut_clks;
      int           max_tbphy_clks;

      qeciphy_power_state_test_seq  power_state_test_seq;
      qeciphy_txrx_test_seq         txrx_test_seq;

      // Randomize the power-state sequence first.
      power_state_test_seq = qeciphy_power_state_test_seq::type_id::create("power_state_test_seq", .contxt(get_full_name()));
      rand_ok = power_state_test_seq.randomize() with {
         if (local::m_num_dut_cycles   >= 0) m_num_dut_cycles   == local::m_num_dut_cycles;
         if (local::m_num_tbphy_cycles >= 0) m_num_tbphy_cycles == local::m_num_tbphy_cycles;
         m_min_cycle_gap_ns      == local::m_min_cycle_gap_ns;
         m_max_cycle_gap_ns      == local::m_max_cycle_gap_ns;
         m_min_cycle_duration_ns == local::m_min_cycle_duration_ns;
         m_max_cycle_duration_ns == local::m_max_cycle_duration_ns;
      };
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize power_state_test_seq")

      // Randomize the txrx sequence such that enough xfers take place to allow the power-cycles to happen during QECi-Phy activity.
      // The max_*_clks values are the worst-case number of clocks needed to initiate all power-cycles (ignoring time when link is down).
      // The number of xfers needed is then based on this number of clocks assuming an average delay (rounded up, > 0) for each xfer.
      txrx_test_seq  = qeciphy_txrx_test_seq::type_id::create("txrx_test_seq", .contxt(get_full_name()));
      max_dut_clks   = 100 + ((power_state_test_seq.m_num_dut_cycles   * m_max_cycle_gap_ns) / m_env_config.m_dut_aclk_period_ns);
      max_tbphy_clks = 100 + ((power_state_test_seq.m_num_tbphy_cycles * m_max_cycle_gap_ns) / m_env_config.m_tbphy_aclk_period_ns);
      rand_ok = txrx_test_seq.randomize() with {
         m_num_dut_xfers        == local::max_dut_clks / ((m_max_dut_delay_clks + m_min_dut_delay_clks + 3) / 2);
         m_min_dut_delay_clks   == local::m_min_axis_delay_clks;
         m_max_dut_delay_clks   == local::m_max_axis_delay_clks;
         m_num_tbphy_xfers      == local::max_tbphy_clks / ((m_max_tbphy_delay_clks + m_min_tbphy_delay_clks + 3) / 2);
         m_min_tbphy_delay_clks == local::m_min_axis_delay_clks;
         m_max_tbphy_delay_clks == local::m_max_axis_delay_clks;
      };
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize txrx_test_seq")

      fork
         power_state_test_seq.start(m_env.m_sequencer);
         txrx_test_seq.start(m_env.m_sequencer);
      join

   endtask : run_main_test_sequence
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: process_command_line
   //
   // Process any command lines options that affect the environment.
   // Note that this is called after configure_environment() so will override any settings it created.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void process_command_line();
      const string          msg_id = { get_type_name(), ".process_command_line" };
      uvm_cmdline_processor clp;
      string                opt_str;

      clp = uvm_cmdline_processor::get_inst();
      if (clp.get_arg_value("+DUT_CYCLES=", opt_str))          m_num_dut_cycles        = opt_str.atoi();
      if (clp.get_arg_value("+TBPHY_CYCLES=", opt_str))        m_num_tbphy_cycles      = opt_str.atoi();
      if (clp.get_arg_value("+MIN_GAP_NS=", opt_str))          m_min_cycle_gap_ns      = opt_str.atoi();
      if (clp.get_arg_value("+MAX_GAP_NS=", opt_str))          m_max_cycle_gap_ns      = opt_str.atoi();
      if (clp.get_arg_value("+MIN_DURATION_NS=", opt_str))     m_min_cycle_duration_ns = opt_str.atoi();
      if (clp.get_arg_value("+MAX_DURATION_NS=", opt_str))     m_max_cycle_duration_ns = opt_str.atoi();
      if (clp.get_arg_value("+MIN_AXIS_DELAY_CLKS=", opt_str)) m_min_axis_delay_clks   = opt_str.atoi();
      if (clp.get_arg_value("+MAX_AXIS_DELAY_CLKS=", opt_str)) m_max_axis_delay_clks   = opt_str.atoi();

   endfunction : process_command_line
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_power_state_test
//------------------------------------------------------------------------------------------------------------------------------------------

`endif // QECIPHY_POWER_STATE_TEST_SVH_

