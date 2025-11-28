
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_1_WORD_SEQ_SVH_
`define RIV_RDY_VLD_SINK_1_WORD_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_sink_1_word_seq
//
// Issue a a single ready, with random delay and return xferred data in m_data field.
// Delay is timed from end of previous xfer unless m_delay_from_valid is constrained to 1, in which case they're timed from valid rising.
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_sink_1_word_seq extends riv_rdy_vld_sink_seq;

   // Control/status variables - not randomized.
   rdy_vld_sink_data_t  m_data;     // Data that was transferred from source.

   // Randomized variables.
   rand bit m_delay_from_valid;  // Ready is delayed from: 0 = end of previous xfer, 1 = valid rising. Default = 0.
   rand int m_delay_clks;        // Numbers of clocks before ready goes high (see m_delay_from_valid). Defaults to 0.

   `uvm_object_utils_begin(riv_rdy_vld_sink_1_word_seq)
   `uvm_object_utils_end

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //---------------------------------------------------------------------------------------------------------------------------------------
   constraint c_dflt_delay_from_valid { soft m_delay_from_valid == 1'b0; }

   constraint c_dflt_delay { soft m_delay_clks == -1; }     // Negative default results in 0 but can be overridden with range.
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

      rand_ok = req.randomize() with {
         m_delays_clks.size == 1;
         m_delays_clks[0]   == (local::m_delay_clks < 0) ? 0 : local::m_delay_clks;
         m_delay_from_valid == local::m_delay_from_valid;
      };

      if (! rand_ok ) `uvm_fatal(msg_id, "Failed to randomize req")

   endfunction: randomize_req
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: finalize
   //
   // Update data with that transferred.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void finalize ();
      const string msg_id = { get_type_name(), ".finalize" };

      m_data = req.m_data[0];

   endfunction: finalize
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_sink_1_word_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SINK_1_WORD_SEQ_SVH_
