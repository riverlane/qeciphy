
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SOURCE_AGENT_SVH_
`define RIV_RDY_VLD_SOURCE_AGENT_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_source_agent
//
// Top level of dummy agent.
// The agent consists of a driver, sequencer and monitor along with generic checker and coverage collector components.
// The agent uses a config object which is fetched from the ConfigDB and is shared with the sub-components.
// The config object contains a handle to a top-level interface and fields to enable/disable the use of the sub-components.
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_source_agent extends uvm_agent;

   `uvm_component_utils_begin(riv_rdy_vld_source_agent)
   `uvm_component_utils_end

   riv_rdy_vld_source_config      m_config;      // Agent configuration object, passed to all child components by default.
   riv_rdy_vld_source_sequencer   m_sequencer;   // Agent sequencer (not built in passive mode).
   riv_rdy_vld_source_driver      m_driver;      // Agent driver (not built in passive mode).
   riv_rdy_vld_source_monitor     m_monitor;     // Agent monitor.
   riv_rdy_vld_source_coverage    m_cov;         // Agent-local coverage collector.
   riv_rdy_vld_source_scoreboard  m_scbd;        // Agent-local scoreboard/checker.

   uvm_analysis_port#(riv_rdy_vld_source_txn)  collected_item_ap;  // Analysis port forwarding collected transactions from monitor.


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
   // Get the config object from ConfigDB and create child objects needed by this agent.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function void build_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".build_phase"};

      // Fetch config object from ConfigDB and share with sub-components.
      if (! uvm_config_db#(riv_rdy_vld_source_config)::get(this, "", "config", m_config) ) begin
         `uvm_fatal(msg_id, "Can't find field 'config' in ConfigDB")
      end
      uvm_config_db#(riv_rdy_vld_source_config)::set(this, "m_sequencer", "config", m_config);
      uvm_config_db#(riv_rdy_vld_source_config)::set(this, "m_driver",    "config", m_config);
      uvm_config_db#(riv_rdy_vld_source_config)::set(this, "m_monitor",   "config", m_config);
      uvm_config_db#(riv_rdy_vld_source_config)::set(this, "m_cov",       "config", m_config);
      uvm_config_db#(riv_rdy_vld_source_config)::set(this, "m_scbd",      "config", m_config);

      // Create the monitor if requried.
      if (m_config.m_enable_monitor) begin
         m_monitor = riv_rdy_vld_source_monitor::type_id::create("m_monitor", this);
      end

      // Set the UVM "standard" variable from the agent's config object and, if the agent is active, create the sequencer and driver.
      is_active = m_config.m_is_active;
      if (is_active == UVM_ACTIVE) begin
         m_sequencer = riv_rdy_vld_source_sequencer::type_id::create("m_sequencer", this);
         m_driver    = riv_rdy_vld_source_driver::type_id::create("m_driver", this);
      end

      // Create the local coverage collector if required.
      if (m_config.m_enable_coverage) begin
         m_cov = riv_rdy_vld_source_coverage::type_id::create("m_cov", this);
      end

      // Create the local coverage collector if required.
      if (m_config.m_enable_scoreboard) begin
         m_scbd = riv_rdy_vld_source_scoreboard::type_id::create("m_scbd", this);
      end

   endfunction : build_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: connect_phase
   //---------------------------------------------------------------------------------------------------------------------------------------
   function void connect_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".connect_phase"};

      // If the agent is active, connect the driver's seq_item_port to the sequencer's exported implementation.
      if (m_config.m_is_active == UVM_ACTIVE) begin
         m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
      end

      // If this agent has its own monitor, connect up the analysis port through the agent's port.
      if (m_config.m_enable_monitor) begin
         m_monitor.collected_item_ap.connect(this.collected_item_ap);
      end

      // If this agent has a local coverage collector and its own monitor, connect the monitor to the coverage collector.
      if (m_config.m_enable_coverage && m_config.m_enable_monitor) begin
         m_monitor.collected_item_ap.connect(m_cov.mon_ap_imp);
      end

      // If this agent has a local scoreboard/checker and its own monitor, connect the monitor to the scoreboard/checker.
      if (m_config.m_enable_scoreboard && m_config.m_enable_monitor) begin
         m_monitor.collected_item_ap.connect(m_scbd.mon_ap_imp);
      end

   endfunction : connect_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_source_agent
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SOURCE_AGENT_SVH_
