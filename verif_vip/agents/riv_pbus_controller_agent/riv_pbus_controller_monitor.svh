
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_MONITOR_SVH_
`define RIV_PBUS_CONTROLLER_MONITOR_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_pbus_controller_monitor
//
// Monitor and publish transactions on the P-Channel bus.
// Protocol is:
//    PREQ rises.
//    Sample requested PSTATE.
//    PREQ falls.
//    Sample final PSTATE.
//    Wait for PACCEPT to fall (or timeout).
// End of Protocol - publish transaction
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_pbus_controller_monitor extends uvm_monitor;

   riv_pbus_controller_config  m_config;              // Config object for the agent (fetched from ConfigDB).
   int unsigned                m_num_items = 0;       // Number of bus transfers started by this driver.
   riv_pbus_controller_txn     m_collected_item;      // Completed transaction item (new one created for each completed P-Bus command).
   riv_pbus_controller_txn     m_change_request_item; // New-request transaction item (new one created for each new P-Bus command).

   `uvm_component_utils_begin(riv_pbus_controller_monitor)
      `uvm_field_int(m_num_items, UVM_DEFAULT | UVM_UNSIGNED)
   `uvm_component_utils_end

   virtual riv_pbus_controller_agent_if  m_vif;           // Handle to TB interface (for covering timing etc.).

   uvm_analysis_port#(riv_pbus_controller_txn) collected_item_ap;    // Analysis port sending out completed transactions.
   uvm_analysis_port#(riv_pbus_controller_txn) change_request_ap;    // Analysis port sending out transactions as soon as requested.

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);
      super.new(name, parent);
      collected_item_ap = new("collected_item_ap", this);
      change_request_ap = new("change_request_ap", this);
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
   // Connect the interface (m_vif) to the appropriate modport of the VIF in the config object m_vif field (if it's defined).
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
   // Initialize any variables and start collecting transactions.
   // HINT: This is an example only. May need to be completely rewritten depending on application.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".run_phase"};

      initialize();

      collect_items();

   endtask : run_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: initialize
   //
   // Initialize this monitor prior to starting transaction collection.
   // Extending classes that override this task should call super.initialize().
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task initialize();
      const string msg_id = {get_type_name(), ".initialize"};

      m_num_items = 0;

   endtask : initialize
   //---------------------------------------------------------------------------------------------------------------------------------------


    //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: collect_items
   //
   // Repeatedly collect and emit individual transaction items.
   // Extending classes that override this task would normally NOT call super.collect_items() (it's an infinite loop).
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task collect_items();
      const string msg_id = {get_type_name(), ".collect_items"};

      forever begin

         // Create new transaction objects and initialize the transaction numbers (incrementing this monitor's count).
         m_change_request_item            = riv_pbus_controller_txn::type_id::create("m_collected_item");
         m_change_request_item.m_item_num = ++m_num_items;
         m_collected_item                 = riv_pbus_controller_txn::type_id::create("m_collected_item");
         m_collected_item.m_item_num      = m_num_items;

         // Collect all the details.
         wait_for_start();                     // Wait for activity to start.

         fork

            begin
               // Collect and publish start of new request.
               void'(begin_tr(m_change_request_item));
               collect_new_request_item();
               end_tr(m_change_request_item);
               change_request_ap.write(m_change_request_item);
            end

            begin
               // Collect and publish the whole P-Bus transaction.
               void'(begin_tr(m_collected_item));
               collect_item();
               end_tr(m_collected_item);
               collected_item_ap.write(m_collected_item);
            end

         join

         `uvm_info(msg_id, $sformatf("Collected %0s item number %0d", m_collected_item.get_type_name(), m_num_items), UVM_HIGH)
         `uvm_info(msg_id, $sformatf("Item #%0d details:\n%0s", m_num_items, m_collected_item.sprint()), UVM_FULL)

      end

   endtask : collect_items
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: wait_for_start
   //
   // Wait for a transaction item to start coming in.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task wait_for_start();
      const string msg_id = {get_type_name(), ".wait_for_start"};

      @(posedge m_vif.preq);

   endtask : wait_for_start
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: collect_new_request_item
   //
   // Collect the data from a new request.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task collect_new_request_item();
      const string msg_id = {get_type_name(), ".collect_new_request_item"};

      m_change_request_item.new_state = m_vif.pstate;
      m_change_request_item.state     = m_vif.pstate;
      m_change_request_item.active    = m_vif.pactive;

   endtask : collect_new_request_item
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: collect_item
   //
   // Wait for the start of a single transaction item and collect all the details.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task collect_item();
      const string msg_id = {get_type_name(), ".collect_item"};
      bit          xfer_running;

      m_collected_item.new_state = m_vif.pstate;

      xfer_running = 1'b1;
      fork
         #(m_config.m_accept_timeout_us * 1.0us);
         begin
            wait (m_vif.paccept === 1'b1);
            m_collected_item.state  = m_vif.pstate;
            m_collected_item.active = m_vif.pactive;
            wait (m_vif.preq    === 1'b0);
            wait (m_vif.paccept === 1'b0);
            xfer_running = 1'b0;
         end
      join_any
      disable fork;

      if (xfer_running) `uvm_error(msg_id, $sformatf("Timed out waiting for PACCEPT to fall - transaction ending anyway"))

   endtask : collect_item
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_pbus_controller_monitor
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_MONITOR_SVH_
