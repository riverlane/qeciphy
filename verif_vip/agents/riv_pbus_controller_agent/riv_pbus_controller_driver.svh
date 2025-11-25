
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_PBUS_CONTROLLER_DRIVER_SVH_
`define RIV_PBUS_CONTROLLER_DRIVER_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_pbus_controller_driver
//
// Drive a single transaction onto the P-Channel bus.
// Protocol is:
//    PSTATE set to requested state.
//    PREQ rises
//    Wait for PACCEPT to rise (or timeout).
//    PREQ falls.
//    PSTATE may change (randomized).
//    Wait for PACCEPT to fall (or timeout).
// End of Protocol
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_pbus_controller_driver extends uvm_driver#(.REQ(riv_pbus_controller_txn), .RSP(riv_pbus_controller_txn));

   riv_pbus_controller_config  m_config;                // Config object for the agent (fetched from ConfigDB).
   int unsigned      m_num_items = 0;         // Number of bus transfers started by this driver.

   `uvm_component_utils_begin(riv_pbus_controller_driver)
      `uvm_field_int(m_num_items, UVM_DEFAULT | UVM_UNSIGNED)
   `uvm_component_utils_end

   virtual riv_pbus_controller_agent_if  m_vif;  // Handle to TB interface (for covering timing etc.).


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_phase
   //
   // Get the config object from ConfigDB and create any other objects needed by this driver.
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
   // Initialize any variables and then repeatedly fetch transactions from the sequencer and process them.
   // HINT: This is a simple, non-pipelined example only - may need to be completely rewritten depending on application.
   // HINT: For simple extensions, override the wait_until_ready(), drive_item() & finalize_item methods() rather than run_phase().
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".run_phase"};

      initialize();

      forever begin

         m_vif.preq = 1'b0;
         wait (m_vif.rst_n === 1'b1);

         while (m_vif.rst_n === 1'b1) begin
            seq_item_port.get_next_item(req);   // Fetch the next item.
            accept_tr(req);                     // Set the transaction's accept-time
            req.m_item_num = ++m_num_items;     // Record this driver's count in the transaction item.
            req.m_src      = get_name();        // Record this driver's instance name in the transaction item.
            void'(begin_tr(req));               // Set the transaction item's start_time and begin recording.

            fork                                // Drive the transaction item over the interface (abort if reset happens).
               wait (m_vif.rst_n !== 1'b1);
               drive_item(req);
            join_any
            disable fork;

            end_tr(req);                        // Set the transaction item's end_time and stop recording.
            finalize_item(req);                 // Do any post-processing
            seq_item_port.item_done();          // Hand control back to the originating sequence
         end

      end

   endtask : run_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: initialize
   //
   // Initialize this driver prior to starting transaction collection.
   // Extending classes that override this task should call super.initialize().
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task initialize();
      const string msg_id = {get_type_name(), ".initialize"};

      m_num_items = 0;

   endtask : initialize
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: drive_item
   //
   // Drive a single item over the interface.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task drive_item(riv_pbus_controller_txn item);
      const string  msg_id = {get_type_name(), ".drive_item"};
      bit           final_state;

      if (m_vif.paccept !== 1'b0) begin
         `uvm_error(msg_id, $sformatf("PACCEPT != 0 (%0b) - transaction aborted", m_vif.paccept))
         return;
      end

      m_vif.pstate = req.new_state;
      #(req.tsu_state2req_ns * 1.0ns);
      m_vif.preq = 1'b1;

      fork
         #(m_config.m_accept_timeout_us * 1.0us);
         wait (m_vif.paccept === 1'b1);
      join_any
      disable fork;
      if (m_vif.paccept !== 1'b1) `uvm_error(msg_id, $sformatf("Timed out waiting for PACCEPT to rise - transaction ending anyway"))

      m_vif.preq = 1'b0;
      #(req.th_req2state_ns * 1.0ns);
      std::randomize(final_state);
      m_vif.pstate = final_state;

      fork
         #(m_config.m_accept_timeout_us * 1.0us);
         wait (m_vif.paccept === 1'b0);
      join_any
      disable fork;
      if (m_vif.paccept !== 1'b0) `uvm_error(msg_id, $sformatf("Timed out waiting for PACCEPT to fall - transaction ending anyway"))

   endtask : drive_item
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: finalize_item
   //
   // Do any final post-transmission processing and updates to the transmitted item.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task finalize_item(riv_pbus_controller_txn item);
      const string msg_id = {get_type_name(), ".finalize_item"};

      req.state  = m_vif.pstate;
      req.active = m_vif.pactive;

   endtask : finalize_item
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_pbus_controller_driver
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_PBUS_CONTROLLER_DRIVER_SVH_
