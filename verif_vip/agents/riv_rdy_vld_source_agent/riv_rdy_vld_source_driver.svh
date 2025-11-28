
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SOURCE_DRIVER_SVH_
`define RIV_RDY_VLD_SOURCE_DRIVER_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_source_driver
//
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_source_driver extends uvm_driver#(.REQ(riv_rdy_vld_source_txn), .RSP(riv_rdy_vld_source_txn));

   riv_rdy_vld_source_config  m_config;                // Config object for the agent (fetched from ConfigDB).
   int unsigned      m_num_items = 0;         // Number of bus transfers started by this driver.

   `uvm_component_utils_begin(riv_rdy_vld_source_driver)
      `uvm_field_int(m_num_items, UVM_DEFAULT | UVM_UNSIGNED)
   `uvm_component_utils_end

   virtual riv_rdy_vld_source_agent_if  m_vif;  // Handle to TB interface (for covering timing etc.).


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

      if (! uvm_config_db#(riv_rdy_vld_source_config)::get(this, "", "config", m_config) ) begin
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

         reset();
         wait (m_vif.rst_n === 1'b1);

         while (m_vif.rst_n === 1'b1) begin

            seq_item_port.get_next_item(req);   // Fetch the next item.
            accept_tr(req);                     // Set the transaction's accept-time
            req.m_item_num = ++m_num_items;     // Record this driver's count in the transaction item.
            req.m_src      = get_name();        // Record this driver's instance name in the transaction item.
            void'(begin_tr(req));               // Set the transaction item's start_time and begin recording.

            // Drive the transaction item over the interface, aborting if reset occurs by completing UVM transaction cleanly.
            fork
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
      const string               msg_id = {get_type_name(), ".initialize"};

      m_num_items = 0;

   endtask : initialize
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: reset
   //
   // Reset the interface and any agent state.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task reset();
      const string               msg_id = {get_type_name(), ".reset"};
      logic [MAX_WIDTH - 1 : 0]  initial_data;

      m_vif.valid = 1'b0;
      std::randomize(initial_data);
      m_vif.data  = initial_data & m_vif.data_mask;

   endtask : reset
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: drive_item
   //
   // Drive a single item over the interface.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task drive_item(riv_rdy_vld_source_txn item);
      const string               msg_id = {get_type_name(), ".drive_item"};
      logic [MAX_WIDTH - 1 : 0]  final_data;

      // For each word to be xferred...
      foreach (item.m_data[i]) begin

         // Wait for required number of clocks before starting the next word xfer.
         if (item.m_delays_clks[i] > 0) begin
            repeat(item.m_delays_clks[i]) @(posedge m_vif.clk);
         end

         // Drive next word & wait for the xfer to finish (valid == ready == 1) or until xfer times out.
         #0ps;    // Avoids delta-cycle issues in VCS
         m_vif.data  = item.m_data[i];
         m_vif.valid = 1'b1;
         fork
            #(m_config.m_xfer_timeout_us * 1.0us);
            do begin
               @(posedge m_vif.clk);
            end while ((m_vif.valid !== 1'b1) || (m_vif.ready !== 1'b1));
         join_any
         disable fork;
         if ((m_vif.valid !== 1'b1) || (m_vif.ready !== 1'b1)) begin
            `uvm_error(
               msg_id,
               $sformatf("Timed out after %0.3fus (valid = %0b, ready = %0b)", m_config.m_xfer_timeout_us, m_vif.valid, m_vif.ready)
            )
         end

         // Finally, end the word xfer and randomize the data on the interface.
         #0ps;    // Avoids delta-cycle issues in VCS
         m_vif.valid = 1'b0;
         std::randomize(final_data);
         m_vif.data  = final_data & m_vif.data_mask;

      end

   endtask : drive_item
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: finalize_item
   //
   // Do any final post-transmission processing and updates to the transmitted item.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task finalize_item(riv_rdy_vld_source_txn item);
      const string msg_id = {get_type_name(), ".finalize_item"};

      // HINT: This template method exits immediately - add suitable code here (e.g. setting any return/"read" data in req).

   endtask : finalize_item
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_source_driver
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SOURCE_DRIVER_SVH_
