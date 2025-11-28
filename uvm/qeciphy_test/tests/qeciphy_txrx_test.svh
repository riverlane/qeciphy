
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_TXRX_TEST_SVH_
`define QECIPHY_TXRX_TEST_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_txrx_test
//
// Abstract:
// Run a stream of data in both directions through the DUT (using a TB instance of the PHY to receive/generate DUT Tx/Rx data).
// See the qeciphy_txrx_test_seq for more details.
// Test can be configured with the following options on the simulator command-line:
//    +DUT_XFERS=n               // Specify number of words to sent to DUT Tx AXI-S Port (n = decimal integer > 0)
//    +MIN_DUT_DELAY_CLKS=n      // Specify min. delay between words sent over DUT Tx AXI-S Port (n = decimal integer >= 0)
//    +MAX_DUT_DELAY_CLKS=n      // Specify max. delay between words sent over DUT Tx AXI-S Port (n = decimal integer <= min. delay)
//    +TBPHY_XFERS=n             // Specify number of words to sent to TB-Phy Tx AXI-S Port (n = decimal integer > 0)
//    +MIN_TBPHY_DELAY_CLKS=n    // Specify min. delay between words sent over TB-Phy Tx AXI-S Port (n = decimal integer >= 0)
//    +MAX_TBPHY_DELAY_CLKS=n    // Specify max. delay between words sent over TB-Phy Tx AXI-S Port (n = decimal integer <= min. delay)
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_txrx_test extends qeciphy_base_test;

   // Control/status variables.
   int  m_num_dut_xfers               =  20_000;
   int  m_min_dut_delay_clks          =       0;
   int  m_max_dut_delay_clks          =      10;
   int  m_num_tbphy_xfers             =  20_000;
   int  m_min_tbphy_delay_clks        =       0;
   int  m_max_tbphy_delay_clks        =      10;

   `uvm_component_utils_begin(qeciphy_txrx_test)
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
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_main_test_sequence();
      const string  msg_id = { get_type_name(), ".run_main_test_sequence" };
      int           rand_ok;

      qeciphy_txrx_test_seq  test_seq;

      test_seq = qeciphy_txrx_test_seq::type_id::create("test_seq", .contxt(get_full_name()));
      rand_ok = test_seq.randomize() with {
         m_num_dut_xfers              == local::m_num_dut_xfers;
         m_min_dut_delay_clks         == local::m_min_dut_delay_clks;
         m_max_dut_delay_clks         == local::m_max_dut_delay_clks;
         m_num_tbphy_xfers            == local::m_num_tbphy_xfers;
         m_min_tbphy_delay_clks       == local::m_min_tbphy_delay_clks;
         m_max_tbphy_delay_clks       == local::m_max_tbphy_delay_clks;
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
      if (clp.get_arg_value("+DUT_XFERS=", opt_str))             m_num_dut_xfers        = opt_str.atoi();
      if (clp.get_arg_value("+MIN_DUT_DELAY_CLKS=", opt_str))    m_min_dut_delay_clks   = opt_str.atoi();
      if (clp.get_arg_value("+MAX_DUT_DELAY_CLKS=", opt_str))    m_max_dut_delay_clks   = opt_str.atoi();
      if (clp.get_arg_value("+TBPHY_XFERS=", opt_str))           m_num_tbphy_xfers      = opt_str.atoi();
      if (clp.get_arg_value("+MIN_TBPHY_DELAY_CLKS=", opt_str))  m_min_tbphy_delay_clks = opt_str.atoi();
      if (clp.get_arg_value("+MAX_TBPHY_DELAY_CLKS=", opt_str))  m_max_tbphy_delay_clks = opt_str.atoi();


   endfunction : process_command_line
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_txrx_test
//------------------------------------------------------------------------------------------------------------------------------------------

`endif // QECIPHY_TXRX_TEST_SVH_

