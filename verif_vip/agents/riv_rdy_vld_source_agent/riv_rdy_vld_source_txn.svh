
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SOURCE_TXN_SVH_
`define RIV_RDY_VLD_SOURCE_TXN_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_source_txn
//
// This is the base class for all dummy transactions.
// A transaction is defined as the tranmission of a list of data-words (m_data[] array).
// Each word-xfer is started after a randomized amount of time (m_delays_clks[] array) which defaults to 0 (back-to-back xfers).
// The number of words can be constrained using m_data.size().
// The valid bits in each data word can be constrained by constraining m_data_mask to match the actual data-width used by the DUT.
// The number of clocks before each word-xfer starts can be set by constraining the elements of the m_delays_clks[] array.
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_source_txn extends uvm_sequence_item;

   // Control/status variables - not randomized.
   int    unsigned  m_item_num;   // Records the Number of transactions, including this one, transmitted by driver or received by monitor.
   string           m_src;        // Identifies transaction source (e.g. driver instance name).
   int              m_idle_clks;  // Monitor only: Number of clocks before either source or sink were ready to send/receive.
   int              m_ready_clks; // Monitor only: Number of clocks for which ready was low after valid was high (sink delayed xfer).
   int              m_valid_clks; // Monitor only: Number of clocks for which valid was low after ready was high (source delayed xfer).

   // Randomized variables.
   rand logic [MAX_WIDTH - 1 : 0]  m_data [];         // List of words to be transferred / monitored (monitor only returns 1 word).
   rand logic [MAX_WIDTH - 1 : 0]  m_data_mask;       // Mask of all bits that are in use by the interface.
   rand int                        m_delays_clks [];  // Driver only: Number of clocks before each word is driven out (-ve treated as 0).

   `uvm_object_utils_begin(riv_rdy_vld_source_txn)
      `uvm_field_int   (m_item_num, UVM_DEFAULT | UVM_UNSIGNED)
      `uvm_field_sarray_int(m_data, UVM_DEFAULT | UVM_NOPACK)
      `uvm_field_string(m_src,      UVM_DEFAULT               )
   `uvm_object_utils_end

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //---------------------------------------------------------------------------------------------------------------------------------------
   // Number of delays must match number of data words.
   constraint c_delays_size {
      solve m_data before m_delays_clks;
      m_delays_clks.size() == m_data.size();
   }

   // All possible bits are used by default.
   constraint c_dflt_data_mask { soft m_data_mask == '1; }

   // Constrain data to only use valid bits.
   constraint c_valid_data {
      solve m_data_mask before m_data;
      foreach (m_data[i]) { m_data[i] == m_data[i] & m_data_mask; }
   }

   // All word-xfers start after 0 clocks by default (-1 is used so soft constraint can be overridden by ranges starting at 0).
   constraint c_dflt_delays {
      foreach (m_delays_clks[i]) { soft m_delays_clks[i] == -1; }
   }
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name = "riv_rdy_vld_source_txn");
      super.new(name);
   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_source_txn
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SOURCE_TXN_SVH_
