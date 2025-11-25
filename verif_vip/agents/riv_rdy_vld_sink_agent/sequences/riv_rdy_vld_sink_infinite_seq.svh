
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_INFINITE_SEQ_SVH_
`define RIV_RDY_VLD_SINK_INFINITE_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_sink_infinite_seq
//
// Continually issue ready's, with random delays (in specified min/max range) but with no data returned.
// Delays are timed from end of previous xfer unless m_delay_from_valid is constrained to 1, in which case they're timed from valid rising.
// WARN: Once running, this sequence never ends and will have to be killed, but may be useful to allow continuous xfers.
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_sink_infinite_seq extends riv_rdy_vld_sink_seq;

   // Control/status variables - not randomized.

   // Randomized variables.
   rand bit m_delay_from_valid;  // Ready is delayed from: 0 = end of previous xfer, 1 = valid rising. Default = 0.
   rand int m_min_delay_clks;    // Minimum number of clocks before ready goes high (see m_delay_from_valid). Defaults to -1.
   rand int m_max_delay_clks;    // Maximum number of clocks before ready goes high (see m_delay_from_valid). Defaults to -1.

   `uvm_object_utils_begin(riv_rdy_vld_sink_infinite_seq)
   `uvm_object_utils_end

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //---------------------------------------------------------------------------------------------------------------------------------------
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
   // Task: body
   //
   // Continually send a single ready with no end.  Overrides default body in order to send continuous stream of transactions.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task body ();
      const string msg_id = { get_type_name(), ".body" };

      forever begin

         // Ensure that a valid transaction item has been created.
         req = riv_rdy_vld_sink_txn::type_id::create("req", .contxt(get_full_name()));

         // Request permission to send the item, randomize it and then send it.
         start_item(req, .sequencer(m_sequencer));
         if (! do_not_randomize) randomize_req();
         `uvm_info(msg_id, $sformatf("Generated %0s transaction.", req.get_type_name()), UVM_HIGH)
         `uvm_info(msg_id, $sformatf("Transaction details:\n%0s", req.sprint()), UVM_FULL)
         finish_item(req);
         `uvm_info(msg_id, $sformatf("Sent %0s transaction.", req.get_type_name()), UVM_HIGH)
         `uvm_info(msg_id, $sformatf("Final transaction details:\n%0s", req.sprint()), UVM_FULL)

      end

   endtask: body
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: randomize_req
   //
   // Randomize transaction item "req".
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void randomize_req ();
      const string  msg_id = { get_type_name(), ".randomize_req" };
      int           rand_ok;

      // Randomize req with single word (faster)
      rand_ok = req.randomize() with {
         req.m_delay_from_valid == local::m_delay_from_valid;
         req.m_delays_clks.size == 1;
         req.m_delays_clks[0] inside {[local::m_min_delay_clks : local::m_max_delay_clks]};
      };
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize req")

   endfunction: randomize_req
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_sink_infinite_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SINK_INFINITE_SEQ_SVH_
