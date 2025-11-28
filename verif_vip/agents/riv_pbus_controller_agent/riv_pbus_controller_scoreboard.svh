
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_SCOREBOARD_SVH_
`define RIV_PBUS_CONTROLLER_SCOREBOARD_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_pbus_controller_scoreboard
//
// Check that P-Channel signals obey the protocol.
// NOTE: Can't do this as SVAs in interface because P-Channel is asynchronous and SVA requires a clocked protocol.
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_pbus_controller_scoreboard extends uvm_scoreboard;

   riv_pbus_controller_txn     m_item;         // Most recently collected transaction item from the monitor.
   riv_pbus_controller_config  m_config;       // Config object for the agent (fetched from ConfigDB).
   int                         m_num_errors;   // Number of scoreboard errors detected.

   `uvm_component_utils_begin(riv_pbus_controller_scoreboard)
      `uvm_field_int(m_num_errors, UVM_DEFAULT | UVM_UNSIGNED)
   `uvm_component_utils_end

   virtual riv_pbus_controller_agent_if  m_vif;   // Handle to TB interface (for covering timing etc.).

   uvm_analysis_imp_riv_pbus_controller_mon_ap#(riv_pbus_controller_txn, riv_pbus_controller_scoreboard) mon_ap_imp;

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

      if (! uvm_config_db#(riv_pbus_controller_config)::get(this, "", "config", m_config) ) begin
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
   // Run all checks concurrently (each check is a forever loop and will run until phase is terminated).
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".run_phase"};

      forever begin

         wait (m_vif.rst_n === 1'b1);

         fork
            @(negedge m_vif.rst_n);
            fork
               check_preq_rise();
               check_preq_fall();
               check_accept_rise();
               check_accept_fall();
               check_state_stable();
               check_command_completion();
            join
         join_any
         disable fork;

      end

   endtask : run_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: report_phase
   //
   // Report summary of data transferred.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void report_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".report_phase"};

      super.report_phase(phase);

      `uvm_info(msg_id, $sformatf("Number of errors = %0d", m_num_errors), UVM_LOW)

   endfunction : report_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_preq_rise
   //
   // Rule: PREQ can only rise whilst PACCEPT is low.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task check_preq_rise();
      const string msg_id = {get_type_name(), ".check_preq_rise"};

      forever begin
         @(posedge m_vif.preq);
         if (m_vif.paccept !== 1'b0) begin
            `uvm_error(msg_id, $sformatf("PREQ rose when PACCEPT != 0 (%0b)", m_vif.paccept))
            m_num_errors++;
         end
      end

   endtask : check_preq_rise
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_preq_fall
   //
   // Rule: PREQ can only fall once PACCEPT is high.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task check_preq_fall();
      const string msg_id = {get_type_name(), ".check_preq_fall"};

      forever begin
         @(negedge m_vif.preq);
         if (m_vif.paccept !== 1'b1) begin
            `uvm_error(msg_id, $sformatf("PREQ fell when PACCEPT != 1 (%0b)", m_vif.paccept))
            m_num_errors++;
         end
      end

   endtask : check_preq_fall
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_accept_rise
   //
   // Rule: PACCEPT can only rise whilst PREQ is high.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task check_accept_rise();
      const string msg_id = {get_type_name(), ".check_accept_rise"};

      forever begin
         @(posedge m_vif.paccept);
         if (m_vif.preq !== 1'b1) begin
            `uvm_error(msg_id, $sformatf("PACCEPT rose when PREQ != 1 (%0b)", m_vif.preq))
            m_num_errors++;
         end
      end

   endtask : check_accept_rise
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_accept_fall
   //
   // Rule: PACCEPT can only fall whilst PREQ is low.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task check_accept_fall();
      const string msg_id = {get_type_name(), ".check_accept_fall"};

      forever begin
         @(negedge m_vif.paccept);
         if (m_vif.preq !== 1'b0) begin
            `uvm_error(msg_id, $sformatf("PACCEPT fell when PREQ != 0 (%0b)", m_vif.preq))
            m_num_errors++;
         end
      end

   endtask : check_accept_fall
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_state_stable
   //
   // Rule: PSTATE can only change whilst PREQ is low.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task check_state_stable();
      const string msg_id = {get_type_name(), ".check_state_stable"};

      forever begin
         @(m_vif.pstate);
         if (m_vif.preq !== 1'b0) begin
            `uvm_error(msg_id, $sformatf("PSTATE changed (%0b) when PREQ != 0 (%0b)", m_vif.pstate, m_vif.preq))
            m_num_errors++;
         end
      end


   endtask : check_state_stable
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_command_completion
   //
   // Rule: Check that whole command sequence completes within allowed time (timeout results in command-cycle-checking being aborted).
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task check_command_completion();
      const string msg_id = {get_type_name(), ".check_command_completion"};

      forever begin

         @(posedge m_vif.preq);

         fork
            @(posedge m_vif.paccept);
            begin
               #(m_config.m_accept_timeout_us * 1.0us);
               `uvm_error(msg_id, $sformatf("Timeout (%0.3fus) waiting for PACCEPT to rise - aborting", m_config.m_accept_timeout_us))
            end
         join_any
         disable fork;
         if (m_vif.paccept !== 1'b1) continue;

         fork
            @(negedge m_vif.preq);
            begin
               #(m_config.m_accept_timeout_us * 1.0us);
               `uvm_error(msg_id, $sformatf("Timeout (%0.3fus) waiting for PREQ to fall - aborting", m_config.m_accept_timeout_us))
            end
         join_any
         disable fork;
         if (m_vif.preq !== 1'b0) continue;

         fork
            @(negedge m_vif.paccept);
            begin
               #(m_config.m_accept_timeout_us * 1.0us);
               `uvm_error(msg_id, $sformatf("Timeout (%0.3fus) waiting for PACCEPT to fall - aborting", m_config.m_accept_timeout_us))
            end
         join_any
         disable fork;

      end

   endtask : check_command_completion
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


endclass : riv_pbus_controller_scoreboard
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_SCOREBOARD_SVH_
