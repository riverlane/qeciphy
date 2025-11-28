
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_TXN_SVH_
`define RIV_RDY_VLD_SINK_TXN_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_sink_txn
//
// This is the base class for all dummy transactions.
// A transaction is defined as the tranmission of a list of data-words (m_data[] queue).
// Sink is ready for each word-xfer after a randomized amount of time (m_delays_clks[] array) which defaults to 0 (back-to-back xfers).
// The ready delay can be set to start immediately or only after valid has gone high (m_delay_from_valid = 0 or 1). Default is 0.
// The number of words can be constrained using m_delays_clks.size().
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_sink_txn extends uvm_sequence_item;

   // Control/status variables - not randomized.
   int    unsigned      m_item_num;    // Number of transactions, including this one, transmitted by driver or received by monitor.
   string               m_src;         // Identifies transaction source (e.g. driver instance name).
   int                  m_idle_clks;   // Monitor only: Number of clocks before either source or sink were ready to send/receive.
   int                  m_ready_clks;  // Monitor only: Number of clocks after valid that ready was low (sink delayed xfer).
   int                  m_valid_clks;  // Monitor only: Number of clocks after ready that valid was low (source delayed xfer).
   rdy_vld_sink_data_t  m_data [$];    // List of words that were transferred (monitor only returns 1 word).

   // Randomized variables.
   rand bit m_delay_from_valid;  // Driver only: Ready is delayed from: 0 = end of previous xfer, 1 = valid rising. Default = 0.
   rand int m_delays_clks [];    // Driver only: Numbers of clocks before ready goes high (see m_delay_from_valid). -ve vals treated as 0.

   `uvm_object_utils_begin(riv_rdy_vld_sink_txn)
      `uvm_field_int   (m_item_num, UVM_DEFAULT | UVM_UNSIGNED)
      `uvm_field_sarray_int(m_data, UVM_DEFAULT | UVM_NOPACK)
      `uvm_field_string(m_src,      UVM_DEFAULT               )
   `uvm_object_utils_end

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //---------------------------------------------------------------------------------------------------------------------------------------
   // By default, delays are measured from the end of the previous xfer.
   constraint c_dflt_delay_from_valid { soft m_delay_from_valid == 1'b0; }

   // By default, sink is ready to xfer data after 0 clocks (-1 is used so soft constraint can be overridden by ranges starting at 0).
   constraint c_dflt_delays {
      foreach (m_delays_clks[i]) { soft m_delays_clks[i] == -1; }
   }
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name = "riv_rdy_vld_sink_txn");
      super.new(name);
   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_sink_txn
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SINK_TXN_SVH_
