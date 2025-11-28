
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_ENV_SVH_
`define QECIPHY_ENV_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_env
//
// Abstract:
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_env extends uvm_component;

   `uvm_component_utils_begin(qeciphy_env)
   `uvm_component_utils_end

   qeciphy_env_config    m_config;
   qeciphy_env_sequencer m_sequencer;

   // Agents, scoreboards/checkers, coverage collectors etc., along with their config objects.
   riv_pbus_controller_config m_dut_pbus_cfg;
   riv_pbus_controller_agent  m_dut_pbus_agt;
   riv_rdy_vld_sink_config    m_dut_axis_rx_cfg;
   riv_rdy_vld_sink_agent     m_dut_axis_rx_agt;
   riv_rdy_vld_source_config  m_dut_axis_tx_cfg;
   riv_rdy_vld_source_agent   m_dut_axis_tx_agt;

   riv_pbus_controller_config m_tbphy_pbus_cfg;
   riv_pbus_controller_agent  m_tbphy_pbus_agt;
   riv_rdy_vld_sink_config    m_tbphy_axis_rx_cfg;
   riv_rdy_vld_sink_agent     m_tbphy_axis_rx_agt;
   riv_rdy_vld_source_config  m_tbphy_axis_tx_cfg;
   riv_rdy_vld_source_agent   m_tbphy_axis_tx_agt;

   qeciphy_env_data_xfer_scoreboard  m_dut2tbphy_data_scbd;
   qeciphy_env_data_xfer_scoreboard  m_tbphy2dut_data_scbd;
   qeciphy_env_state_scoreboard      m_state_scbd;


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction : new
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_phase
   //
   // Get the config object from ConfigDB and create any other objects needed by this environment.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void build_phase(uvm_phase phase);
      const string msg_id = { get_type_name(), ".build_phase" };

      if (! uvm_config_db#(qeciphy_env_config)::get(this, "", "config", m_config) ) begin
         `uvm_fatal(msg_id, "Can't find field 'config' in ConfigDB")
      end

      m_sequencer = qeciphy_env_sequencer::type_id::create("m_sequencer", this);    // Environment's virtual sequencer.

      configure_agents();   // Create and define configurations for all agents (forcing passive configuration if required).
      build_agents();       // Build all agents, according to configurations defined above.

      if (m_config.m_enable_ral)         build_ral_components();        // Build all RAL components if enabled.
      if (m_config.m_enable_scoreboards) build_scoreboards();           // Build all scoreboards if enabled.
      if (m_config.m_enable_coverage)    build_coverage_collectors();   // Build all coverage collectors if enabled.

   endfunction : build_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: connect_phase
   //
   // Connect up all analysis ports, sub-sequencers etc. (all sub-components are built by now).
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void connect_phase(uvm_phase phase);
      const string msg_id = { get_type_name(), ".connect_phase" };

      if (m_config.m_is_active == UVM_ACTIVE) connect_sub_sequencers();
      if (m_config.m_enable_scoreboards) connect_scoreboards();
      if (m_config.m_enable_coverage) connect_coverage_collectors();

   endfunction : connect_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: configure_agents
   //
   // Create and initialize configuration objects for each agent in the environment.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void configure_agents();
      const string  msg_id = { get_type_name(), ".configure_agents" };

      m_dut_pbus_cfg = riv_pbus_controller_config::type_id::create("m_dut_pbus_cfg", .contxt(get_full_name()));
      m_dut_pbus_cfg.m_vif = m_config.m_vifs.dut_pbus_vif;
      if (m_config.m_is_active == UVM_PASSIVE) m_dut_pbus_cfg.set_passive();
      uvm_config_db#(riv_pbus_controller_config)::set(this, "m_dut_pbus_agt*", "config", m_dut_pbus_cfg);

      m_dut_axis_rx_cfg = riv_rdy_vld_sink_config::type_id::create("m_dut_axis_rx_cfg", .contxt(get_full_name()));
      m_dut_axis_rx_cfg.m_vif = m_config.m_vifs.dut_axis_rx_vif;
      m_dut_axis_rx_cfg.m_always_ready = 1'b1;
      if (m_config.m_is_active == UVM_PASSIVE) m_dut_axis_rx_cfg.set_passive();
      uvm_config_db#(riv_rdy_vld_sink_config)::set(this, "m_dut_axis_rx_agt*", "config", m_dut_axis_rx_cfg);

      m_dut_axis_tx_cfg = riv_rdy_vld_source_config::type_id::create("m_dut_axis_tx_cfg", .contxt(get_full_name()));
      m_dut_axis_tx_cfg.m_vif = m_config.m_vifs.dut_axis_tx_vif;
      if (m_config.m_is_active == UVM_PASSIVE) m_dut_axis_tx_cfg.set_passive();
      uvm_config_db#(riv_rdy_vld_source_config)::set(this, "m_dut_axis_tx_agt*", "config", m_dut_axis_tx_cfg);

      m_tbphy_pbus_cfg = riv_pbus_controller_config::type_id::create("m_tbphy_pbus_cfg", .contxt(get_full_name()));
      m_tbphy_pbus_cfg.m_vif = m_config.m_vifs.tbphy_pbus_vif;
      if (m_config.m_is_active == UVM_PASSIVE) m_tbphy_pbus_cfg.set_passive();
      uvm_config_db#(riv_pbus_controller_config)::set(this, "m_tbphy_pbus_agt*", "config", m_tbphy_pbus_cfg);

      m_tbphy_axis_rx_cfg = riv_rdy_vld_sink_config::type_id::create("m_tbphy_axis_rx_cfg", .contxt(get_full_name()));
      m_tbphy_axis_rx_cfg.m_vif = m_config.m_vifs.tbphy_axis_rx_vif;
      m_tbphy_axis_rx_cfg.m_always_ready = 1'b1;
      if (m_config.m_is_active == UVM_PASSIVE) m_tbphy_axis_rx_cfg.set_passive();
      uvm_config_db#(riv_rdy_vld_sink_config)::set(this, "m_tbphy_axis_rx_agt*", "config", m_tbphy_axis_rx_cfg);

      m_tbphy_axis_tx_cfg = riv_rdy_vld_source_config::type_id::create("m_tbphy_axis_tx_cfg", .contxt(get_full_name()));
      m_tbphy_axis_tx_cfg.m_vif = m_config.m_vifs.tbphy_axis_tx_vif;
      if (m_config.m_is_active == UVM_PASSIVE) m_tbphy_axis_tx_cfg.set_passive();
      uvm_config_db#(riv_rdy_vld_source_config)::set(this, "m_tbphy_axis_tx_agt*", "config", m_tbphy_axis_tx_cfg);

   endfunction : configure_agents
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_agents
   //
   // Create each agent in the environment (environment and agent configs are valid).
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void build_agents();
      const string  msg_id = { get_type_name(), ".build_agents" };

      m_dut_pbus_agt    = riv_pbus_controller_agent::type_id::create("m_dut_pbus_agt", .parent(this));
      m_dut_axis_rx_agt = riv_rdy_vld_sink_agent::type_id::create("m_dut_axis_rx_agt", .parent(this));
      m_dut_axis_tx_agt = riv_rdy_vld_source_agent::type_id::create("m_dut_axis_tx_agt", .parent(this));

      m_tbphy_pbus_agt    = riv_pbus_controller_agent::type_id::create("m_tbphy_pbus_agt", .parent(this));
      m_tbphy_axis_rx_agt = riv_rdy_vld_sink_agent::type_id::create("m_tbphy_axis_rx_agt", .parent(this));
      m_tbphy_axis_tx_agt = riv_rdy_vld_source_agent::type_id::create("m_tbphy_axis_tx_agt", .parent(this));

   endfunction : build_agents
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_scoreboards
   //
   // Create each scoreboard in the environment (environment and scoreboard configs are valid).
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void build_scoreboards();
      const string  msg_id = { get_type_name(), ".build_scoreboards" };

      m_dut2tbphy_data_scbd = qeciphy_env_data_xfer_scoreboard::type_id::create("m_dut2tbphy_data_scbd", .parent(this));
      m_tbphy2dut_data_scbd = qeciphy_env_data_xfer_scoreboard::type_id::create("m_tbphy2dut_data_scbd", .parent(this));
      m_state_scbd          = qeciphy_env_state_scoreboard::type_id::create("m_state_scbd", .parent(this));

   endfunction : build_scoreboards
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_coverage_collectors
   //
   // Create each coverage collector in the environment (environment and coverage collector configs are valid).
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void build_coverage_collectors();
      const string  msg_id = { get_type_name(), ".build_coverage_collectors" };

      // HINT: m_covcol1_cov = qeciphy_env_my_coverage::type_id::create("m_covcol1_cov", .parent(this));

   endfunction : build_coverage_collectors
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_ral_components
   //
   // Create all components needed for RAL access (adapters, predictors).
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void build_ral_components();
      const string  msg_id = { get_type_name(), ".build_ral_components" };

      // HINT: m_agent1_reg_adapter   = my_agent_reg_adapter::type_id::create("m_agent1_reg_adapter", .contxt(get_full_name()));
      // HINT: m_agent1_reg_predictor = my_agent_reg_predictor::type_id::create("m_agent1_reg_predictor", .parent(this));

   endfunction : build_ral_components
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: connect_sub_sequencers
   //
   // Connect all agent sequencers to the sub-sequencer fields in the environment's sequencer.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void connect_sub_sequencers();
      const string  msg_id = { get_type_name(), ".connect_sub_sequencers" };

      m_sequencer.m_dut_pbus_seqr      = m_dut_pbus_agt.m_sequencer;
      m_sequencer.m_dut_axis_rx_seqr   = m_dut_axis_rx_agt.m_sequencer;
      m_sequencer.m_dut_axis_tx_seqr   = m_dut_axis_tx_agt.m_sequencer;
      m_sequencer.m_tbphy_pbus_seqr    = m_tbphy_pbus_agt.m_sequencer;
      m_sequencer.m_tbphy_axis_rx_seqr = m_tbphy_axis_rx_agt.m_sequencer;
      m_sequencer.m_tbphy_axis_tx_seqr = m_tbphy_axis_tx_agt.m_sequencer;

   endfunction : connect_sub_sequencers
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: connect_scoreboards
   //
   // Connect all scoreboard analysis imports to appropriate sources.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void connect_scoreboards();
      const string  msg_id = { get_type_name(), ".connect_scoreboards" };

      m_tbphy_axis_tx_agt.collected_item_ap.connect(m_tbphy2dut_data_scbd.axis_source_ap_imp);
      m_dut_axis_rx_agt.collected_item_ap.connect(m_tbphy2dut_data_scbd.axis_sink_ap_imp);

      m_dut_axis_tx_agt.collected_item_ap.connect(m_dut2tbphy_data_scbd.axis_source_ap_imp);
      m_tbphy_axis_rx_agt.collected_item_ap.connect(m_dut2tbphy_data_scbd.axis_sink_ap_imp);

      m_dut_pbus_agt.change_request_ap.connect(m_state_scbd.dut_pbus_start_ap_imp);
      m_tbphy_pbus_agt.change_request_ap.connect(m_state_scbd.tbphy_pbus_start_ap_imp);
      m_dut_pbus_agt.collected_item_ap.connect(m_state_scbd.dut_pbus_ap_imp);
      m_tbphy_pbus_agt.collected_item_ap.connect(m_state_scbd.tbphy_pbus_ap_imp);

   endfunction : connect_scoreboards
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: connect_coverage_collectors
   //
   // Connect all coverage-collector analysis imports to appropriate sources.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void connect_coverage_collectors();
      const string  msg_id = { get_type_name(), ".connect_coverage_collectors" };

      // HINT: m_agent1_agt.collected_item_ap.connect(m_covcol1_cov.agent1_ap_imp);

   endfunction : connect_coverage_collectors
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: connect_ral_components
   //
   // Connect up all components needed for RAL access (adapters, predictors).
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void connect_ral_components();
      const string  msg_id = { get_type_name(), ".connect_ral_components" };

      if (m_config.m_regs == null) `uvm_fatal(msg_id, "m_config.m_regs is NULL")
      // HINT: m_agent1_reg_predictor.map     = m_config.m_regs.m_agent1_reg_map;
      // HINT: m_agent1_reg_predictor.adapter = m_agent1_reg_adapter;
      // HINT: m_agent1_agt.collected_item_ap.connect(m_agent1_reg_predictor.bus_in);
      // HINT: m_config.m_regs.m_agent1_reg_map.set_sequencer(m_agent1_agt.m_sequencer, m_agent1_reg_predictor);
      // HINT: m_config.m_regs.m_agent1_reg_map.set_auto_predict(0);

   endfunction : connect_ral_components
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_env
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_ENV_SVH_
