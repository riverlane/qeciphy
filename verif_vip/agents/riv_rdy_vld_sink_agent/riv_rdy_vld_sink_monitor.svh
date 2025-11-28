
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SINK_MONITOR_SVH_
`define RIV_RDY_VLD_SINK_MONITOR_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_sink_monitor
//
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_sink_monitor extends uvm_monitor;

   riv_rdy_vld_sink_config  m_config;              // Config object for the agent (fetched from ConfigDB).
   int unsigned             m_num_items = 0;       // Number of bus transfers started by this driver.
   riv_rdy_vld_sink_txn     m_collected_item;      // Collected transaction item (new one created for each bus transaction).
   int                      m_idle_period_clks;
   int                      m_ready_cnt_clks;
   int                      m_valid_cnt_clks;

   `uvm_component_utils_begin(riv_rdy_vld_sink_monitor)
      `uvm_field_int(m_num_items, UVM_DEFAULT | UVM_UNSIGNED)
   `uvm_component_utils_end

   virtual riv_rdy_vld_sink_agent_if  m_vif;           // Handle to TB interface (for covering timing etc.).

   uvm_analysis_port#(riv_rdy_vld_sink_txn) collected_item_ap;    // Analysis port sending out collected transactions.

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);
      super.new(name, parent);
      collected_item_ap = new("collected_item_ap", this);
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

         // Create a new transaction object and initialize the transaction number (incrementing this monitor's count).
         m_collected_item            = riv_rdy_vld_sink_txn::type_id::create("m_collected_item");
         m_collected_item.m_item_num = ++m_num_items;

         // Collect all the details.
         wait_for_start();                     // Wait for activity to start.
         void'(begin_tr(m_collected_item));    // Set the transaction item's start_time and begin recording.
         collect_item();                       // Collect all the transaction item's information.
         end_tr(m_collected_item);             // Set the transaction item's end_time and stop recording.

         // Print some debug info before emitting the collected transaction item through the analysis port.
         `uvm_info(msg_id, $sformatf("Collected %0s item number %0d", m_collected_item.get_type_name(), m_num_items), UVM_HIGH)
         `uvm_info(msg_id, $sformatf("Item #%0d details:\n%0s", m_num_items, m_collected_item.sprint()), UVM_FULL)
         collected_item_ap.write(m_collected_item);

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

      m_idle_period_clks = 0;
      @(posedge m_vif.clk);
      while ((m_vif.valid !== 1'b1) && (m_vif.ready !== 1'b1)) begin
         m_idle_period_clks++;
         @(posedge m_vif.clk);
      end

   endtask : wait_for_start
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: collect_item
   //
   // Wait for the start of a single transaction item and collect all the details.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task collect_item();
      const string msg_id = {get_type_name(), ".collect_item"};

      // Count how many clocks until xfer completes (abort collection if xfer is aborted).
      m_ready_cnt_clks = 0;
      m_valid_cnt_clks = 0;
      while ((m_vif.valid !== 1'b1) || (m_vif.ready !== 1'b1)) begin
         if (m_vif.valid !== 1'b1) m_ready_cnt_clks++;
         if (m_vif.ready !== 1'b1) m_valid_cnt_clks++;
         if ((m_vif.valid !== 1'b1) && (m_vif.ready !== 1'b1)) break;
         @(posedge m_vif.clk);
      end

      // Collect the xfer information.
      if ((m_vif.valid === 1'b1) && (m_vif.ready === 1'b1)) begin
         m_collected_item.m_data.delete();
         m_collected_item.m_data.push_back(rdy_vld_sink_data_t'(m_vif.data & m_vif.data_mask));
      end else if ((m_vif.valid !== 1'b1) && (m_vif.ready === 1'b1)) begin
         `uvm_error(msg_id, $sformatf("Transfer aborted (valid fell, no ready) - no data will be reported (m_data will be null)"))
      end else if (m_vif.ready !== 1'b1) begin
         `uvm_info(msg_id, $sformatf("Transfer aborted (ready fell, no valid) - no data will be reported (m_data will be null)"), UVM_LOW)
      end
      m_collected_item.m_ready_clks  = m_ready_cnt_clks;
      m_collected_item.m_valid_clks  = m_valid_cnt_clks;

   endtask : collect_item
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_sink_monitor
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SINK_MONITOR_SVH_
