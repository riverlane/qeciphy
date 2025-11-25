
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_SLEEP_TO_RESET_TEST_SVH_
`define QECIPHY_SLEEP_TO_RESET_TEST_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_sleep_to_reset_test
//
// Abstract:
// Whilst sending bursts (max-speed or stuttery) of data, momentarily introduce a bit error to the DUT serial receive-stream.
// See the qeciphy_sleep_to_reset_test_seq for more details.
//
// Test can be configured with the following options on the simulator command-line:
//    +NUM_ERRORS=n           // Specify m_num_errors (n = decimal integer > 0).
//    +MIN_DELAY_PS=n         // Specify m_min_delay_ps (n = decimal integer > 0).
//    +MAX_DELAY_PS=n         // Specify m_max_delay_ps (n = decimal integer >= m_min_delay_ps).
//    +ERROR_WIDTH_PS=n       // Specify m_error_width_ps (n = decimal integer > 0).
//    +MIN_STUTTER_CLKS=n     // Specify m_min_stutter_clks (n = decimal integer > 0).
//    +MAX_STUTTER_CLKS=n     // Specify m_max_stutter_clks (n = decimal integer >= m_min_stutter_clks).
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_sleep_to_reset_test extends qeciphy_base_test;

   // Control/status variables.
   int m_num_errors       =          5;    // Number of errors to generate in the test run (default = 5 errors).
   int m_min_delay_ps     =          1;    // Minimum time (in ps) from link becoming ready to error occurring (default = 0ps).
   int m_max_delay_ps     = 10_000_000;    // Maximum time (in ps) from link becoming ready to error occurring (default = 10us).
   int m_error_width_ps   =        120;    // Duration (in ps) that error condition will persist (default = 120ps).
   int m_min_stutter_clks =          1;    // Minimum time (number of clks) between "stuttery" AXI-S data transfers (default = 1 clk).
   int m_max_stutter_clks =         40;    // Maximum time (number of clks) between "stuttery" AXI-S data transfers (default = 40 clks).

   `uvm_component_utils_begin(qeciphy_sleep_to_reset_test)
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
   // Task: run_reset_sequence
   //
   // Run sequence to initialize TB. apply reset, start clocks running etc.
   // Tests may override this task to run their own reset_phase sequence, but this should be OK by default.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_reset_sequence();
      const string  msg_id = { get_type_name(), ".run_reset_sequence" };

      // TODO: Replace the following line with test-specific code if needed, or delete this task.
      super.run_reset_sequence();

   endtask : run_reset_sequence
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: run_main_test_sequence
   //
   // Create, randomize and execute the main test sequence.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_main_test_sequence();
      const string  msg_id = { get_type_name(), ".run_main_test_sequence" };
      int           rand_ok;

      qeciphy_sleep_to_reset_test_seq  test_seq;

      test_seq = qeciphy_sleep_to_reset_test_seq::type_id::create("test_seq", .contxt(get_full_name()));
      rand_ok = test_seq.randomize() with {
         m_num_errors       == local::m_num_errors;
         m_min_delay_ps     == local::m_min_delay_ps;
         m_max_delay_ps     == local::m_max_delay_ps;
         m_error_width_ps   == local::m_error_width_ps;
         m_min_stutter_clks == local::m_min_stutter_clks;
         m_max_stutter_clks == local::m_max_stutter_clks;
      };
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize test_seq")

      test_seq.start(m_env.m_sequencer);

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
      if (clp.get_arg_value("+NUM_ERRORS=",       opt_str)) m_num_errors       = opt_str.atoi();
      if (clp.get_arg_value("+MIN_DELAY_PS=",     opt_str)) m_min_delay_ps     = opt_str.atoi();
      if (clp.get_arg_value("+MAX_DELAY_PS=",     opt_str)) m_max_delay_ps     = opt_str.atoi();
      if (clp.get_arg_value("+ERROR_WIDTH_PS=",   opt_str)) m_error_width_ps   = opt_str.atoi();
      if (clp.get_arg_value("+MIN_STUTTER_CLKS=", opt_str)) m_min_stutter_clks = opt_str.atoi();
      if (clp.get_arg_value("+MAX_STUTTER_CLKS=", opt_str)) m_max_stutter_clks = opt_str.atoi();

   endfunction : process_command_line
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_sleep_to_reset_test
//------------------------------------------------------------------------------------------------------------------------------------------

`endif // QECIPHY_SLEEP_TO_RESET_TEST_SVH_