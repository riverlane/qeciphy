
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_SCOREBOARD_SVH_
`define RIV_RDY_VLD_SINK_SCOREBOARD_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_sink_scoreboard
//
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_sink_scoreboard extends uvm_scoreboard;

   riv_rdy_vld_sink_txn     m_item;         // Most recently collected transaction item from the monitor.
   riv_rdy_vld_sink_config  m_config;       // Config object for the agent (fetched from ConfigDB).
   int               m_num_errors;   // Number of scoreboard errors detected.

   `uvm_component_utils_begin(riv_rdy_vld_sink_scoreboard)
      `uvm_field_int(m_num_errors, UVM_DEFAULT | UVM_UNSIGNED)
   `uvm_component_utils_end

   virtual riv_rdy_vld_sink_agent_if  m_vif;   // Handle to TB interface (for covering timing etc.).

   uvm_analysis_imp_riv_rdy_vld_sink_mon_ap#(riv_rdy_vld_sink_txn, riv_rdy_vld_sink_scoreboard) mon_ap_imp;

   event  new_item_event;   // Triggered when new transaction is received.
   event  interface_event;  // Triggered when interface changes occur.


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);

      super.new(name, parent);

      // Create analysis port implementation to receive monitored transactions.
      mon_ap_imp = new("mon_ap_imp", this);

   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_phase
   //
   // Get the config object from ConfigDB and create any other objects needed by this monitor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".build_phase"};

      if (! uvm_config_db#(riv_rdy_vld_sink_config)::get(this, "", "config", m_config) ) begin
         `uvm_fatal(msg_id, "Can't find field 'config' in ConfigDB")
      end

   endfunction : build_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: connect_phase
   //
   // Connect the interface (m_vif) to that passed in the config object m_vif field (if it's defined).
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void connect_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".connect_phase"};

      super.connect_phase(phase);

      if (m_config.m_vif != null) m_vif = m_config.m_vif;

   endfunction : connect_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: end_of_elaboration_phase
   //
   // Check that all required configurations and connections are complete.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void end_of_elaboration_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".end_of_elaboration_phase"};

      super.end_of_elaboration_phase(phase);

      if (m_vif == null) `uvm_fatal(msg_id, "Virtual interface (m_vif) is null")   // Can't continue if no interface is available.

   endfunction : end_of_elaboration_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: run_phase
   //
   // Wait for new transactions (or any other events, such as signal changes on the interface) and act upon them.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".run_phase"};

      // HINT: Put any code here

   endtask : run_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: write_riv_rdy_vld_sink_mon_ap
   //
   // Receive transactions from the analysis port and process it for coverage collection.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void write_riv_rdy_vld_sink_mon_ap(riv_rdy_vld_sink_txn t);
      const string msg_id = {get_type_name(), ".write_riv_rdy_vld_sink_mon_ap"};

      m_item = t;
      -> new_item_event;

   endfunction : write_riv_rdy_vld_sink_mon_ap
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_sink_scoreboard
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SINK_SCOREBOARD_SVH_
