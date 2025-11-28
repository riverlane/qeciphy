
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_MULTI_WORD_SEQ_SVH_
`define RIV_RDY_VLD_SINK_MULTI_WORD_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_sink_multi_word_seq
//
// Issue a number of consecutive ready's, with random delays (in specified min/max range) and return all xferred data in m_data field.
// Delays are timed from end of previous xfer unless m_delay_from_valid is constrained to 1, in which case they're timed from valid rising.
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_sink_multi_word_seq extends riv_rdy_vld_sink_seq;

   // Control/status variables - not randomized.
   rdy_vld_sink_data_t  m_data[];   // Data that was transferred from source.

   // Randomized variables.
   rand bit m_delay_from_valid;  // Ready is delayed from: 0 = end of previous xfer, 1 = valid rising. Default = 0.
   rand int m_num_xfers;         // Number of transfers to do.
   rand int m_min_delay_clks;    // Minimum number of clocks before ready goes high (see m_delay_from_valid). Defaults to -1.
   rand int m_max_delay_clks;    // Maximum number of clocks before ready goes high (see m_delay_from_valid). Defaults to -1.

   `uvm_object_utils_begin(riv_rdy_vld_sink_multi_word_seq)
   `uvm_object_utils_end

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //---------------------------------------------------------------------------------------------------------------------------------------
   constraint c_valid_num_xfers { m_num_xfers > 0; }

   constraint c_dflt_delay_from_valid { soft m_delay_from_valid == 1'b0; }

   constraint c_vld_min_delay  {      m_min_delay_clks >= 0; }
   constraint c_dflt_min_delay { soft m_min_delay_clks == 0; }

   constraint c_vld_max_delay  {      m_max_delay_clks >= m_min_delay_clks; }
   constraint c_dflt_max_delay { soft m_max_delay_clks == m_min_delay_clks; }
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name = "");
      super.new(name);
   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: randomize_req
   //
   // Randomize transaction item "req".
   // HINT: Randomize/set transaction item fields here (only needed if not overriding body() method).
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void randomize_req ();
      const string  msg_id = { get_type_name(), ".randomize_req" };
      int           rand_ok;

      // Randomize req with single word (faster)
      rand_ok = req.randomize() with {
         req.m_delay_from_valid   == local::m_delay_from_valid;
         req.m_delays_clks.size() == local::m_num_xfers;
         foreach (req.m_delays_clks[i]) {
            req.m_delays_clks[i] inside {[local::m_min_delay_clks : local::m_max_delay_clks]};
         }
      };
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize req")

   endfunction: randomize_req
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: finalize
   //
   // Update data with that transferred.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void finalize ();
      const string msg_id = { get_type_name(), ".finalize" };

      m_data = new[m_num_xfers];
      foreach (m_data[i]) m_data[i] = req.m_data[i];

   endfunction: finalize
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_sink_multi_word_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SINK_MULTI_WORD_SEQ_SVH_
