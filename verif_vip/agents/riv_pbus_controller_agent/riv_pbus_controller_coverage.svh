
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_COVERAGE_SVH_
`define RIV_PBUS_CONTROLLER_COVERAGE_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_pbus_controller_coverage
//
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_pbus_controller_coverage extends uvm_component;

   virtual riv_pbus_controller_agent_if  m_vif;   // Handle to TB interface (for covering timing etc.).

   uvm_analysis_imp_riv_pbus_controller_mon_ap#(riv_pbus_controller_txn, riv_pbus_controller_coverage) mon_ap_imp;

   riv_pbus_controller_txn     m_item;      // Most recently collected transaction item from the monitor.
   riv_pbus_controller_config  m_config;    // Config object for the agent (fetched from ConfigDB).

   `uvm_component_utils_begin(riv_pbus_controller_coverage)
   `uvm_component_utils_end

   event  new_item_event;   // Triggered when new transaction is received.
   event  interface_event;  // Triggered when interface changes occur.


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Covergroup: riv_pbus_controller_txn_cg
   //
   // Collect coverage of transaction-item fields.
   // HINT: Remember - all fields of the coverage class, including the interface, are available, not just the most recent transaction.
   //---------------------------------------------------------------------------------------------------------------------------------------
   covergroup riv_pbus_controller_txn_cg;
      option.per_instance = 1;

      // HINT: my_cp: coverpoint m_item {}
      // HINT: my_cx: cross m_item, m_cfg {}

   endgroup : riv_pbus_controller_txn_cg
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Covergroup: riv_pbus_controller_if_cg
   //
   // Collect coverage of signals in the interface (e.g. for timing etc.).
   // HINT: Remember - all fields of the coverage class, including most recent transactions, are available, not just the interface signals.
   //---------------------------------------------------------------------------------------------------------------------------------------
   covergroup riv_pbus_controller_if_cg;
      option.per_instance = 1;

      // HINT: my_if_cp: coverpoint m_vif.sig1 {}
      // HINT: my_if_cx: cross m_vif.sig1, m_vif.sig2 {}

   endgroup : riv_pbus_controller_if_cg
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);

      super.new(name, parent);

      // Create analysis port implementation to receive monitored transactions.
      mon_ap_imp = new("mon_ap_imp", this);

      // Create covergroups.
      riv_pbus_controller_txn_cg  = new();
      riv_pbus_controller_if_cg   = new();

   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_phase
   //
   // Get the config object from ConfigDB and create any other objects needed by this monitor.
   // NOTE: Do NOT call super.build_phase for components extending uvm_* base classes.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".build_phase"};

      if (! uvm_config_db#(riv_pbus_controller_config)::get(this, "", "config", m_config) ) begin
         `uvm_fatal(msg_id, "Can't find field 'config' in ConfigDB")
      end

      riv_pbus_controller_txn_cg.set_inst_name({get_full_name(), ".", "riv_pbus_controller_txn_cg"});
      riv_pbus_controller_txn_cg.option.comment = {"Coverage for riv_pbus_controller_txn items in agent ", get_name()};

      riv_pbus_controller_if_cg.set_inst_name({get_full_name(), ".", "riv_pbus_controller_if_cg"});
      riv_pbus_controller_if_cg.option.comment = {"Coverage for riv_pbus_controller_if signals as recorded by agent ", get_name()};

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
   // Wait for new transactions (or any other events, such as signal changes on the interface)
   // HINT: This is a simple example only. May need to be completely rewritten depending on application.
   // HINT: For simple extensions, override the process_txn() & process_if_signals() methods rather than run_phase().
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".run_phase"};

      fork

         // Continually-running task to detect interface changes that need processing.
         detect_if_events();

         // Wait for interface changes, process them and then sample the processed data.
         forever begin
            @interface_event;
            process_if_signals();
            riv_pbus_controller_if_cg.sample();
         end

         // Wait for and process new transactions and then sample the processed data.
         forever begin
            @new_item_event;
            process_txn();
            riv_pbus_controller_txn_cg.sample();
         end

      join

   endtask : run_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: detect_if_events
   //
   // Continually wait for changes on interface signals raising event when a change has happened.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task detect_if_events();
      const string msg_id = {get_type_name(), ".detect_if_events"};

      forever begin

         // HINT: Remove the following line and add code to actually wait for changes.
         wait (0);

         ->interface_event;

      end

   endtask : detect_if_events
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: process_if_signals
   //
   // Process interface signals and update local fields prior to sampling.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task process_if_signals();
      const string msg_id = {get_type_name(), ".process_if_signals"};


   endtask : process_if_signals
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: process_txn
   //
   // Process new m_current_txn and update local fields prior to sampling.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task process_txn();
      const string msg_id = {get_type_name(), ".process_txn"};


   endtask : process_txn
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: write_riv_pbus_controller_mon_ap
   //
   // Receive transactions from the analysis port and process it for coverage collection.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void write_riv_pbus_controller_mon_ap(riv_pbus_controller_txn t);
      const string msg_id = {get_type_name(), ".write_riv_pbus_controller_mon_ap"};

      m_item = t;
      -> new_item_event;

   endfunction : write_riv_pbus_controller_mon_ap
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_pbus_controller_coverage
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_COVERAGE_SVH_
