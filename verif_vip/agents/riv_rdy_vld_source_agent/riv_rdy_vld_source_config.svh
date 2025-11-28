
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA


`ifndef RIV_RDY_VLD_SOURCE_CONFIG_SVH_
`define RIV_RDY_VLD_SOURCE_CONFIG_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: riv_rdy_vld_source_config
//
//------------------------------------------------------------------------------------------------------------------------------------------
class riv_rdy_vld_source_config extends uvm_object;

   // Control/status variables - not randomized.
   uvm_active_passive_enum  m_is_active          = UVM_ACTIVE;  // Enable/disable the creation of the driver and sequencer.
   bit                      m_enable_monitor     = 1;           // Enable/disable building of monitor (e.g. >1 agent on same interface).
   bit                      m_enable_coverage    = 1;           // Enable/disable building of agent-local coverage collector.
   bit                      m_enable_scoreboard  = 1;           // Enable/disable building of agent-local scoreboard/checker.
   real                     m_xfer_timeout_us    = 1000;        // Max. time (in us) from vld high to xfer timeout (0 = no timeout).

   // Randomized variables.
   // HINT: Declare randomizable variables here (use m_ prefix) and also add them to the field macros if desired.

   // Handle to the agent's interface. Does not specify any modport so it can be used by driver and monitor.
   virtual riv_rdy_vld_source_agent_if  m_vif;

   `uvm_object_utils_begin(riv_rdy_vld_source_config)
      `uvm_field_enum (uvm_active_passive_enum, m_is_active, UVM_DEFAULT          )
      `uvm_field_int  (m_enable_monitor,                     UVM_DEFAULT | UVM_BIN)
      `uvm_field_int  (m_enable_coverage,                    UVM_DEFAULT | UVM_BIN)
      `uvm_field_int  (m_enable_scoreboard,                  UVM_DEFAULT | UVM_BIN)
      `uvm_field_real (m_xfer_timeout_us,                    UVM_DEFAULT)
   `uvm_object_utils_end

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //---------------------------------------------------------------------------------------------------------------------------------------
   // HINT: Add constraints here.
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
   // Function: set_default_config
   //
   // Set some default values that can be used when creating default configurations.
   // Overriding this in extended classes can allow factory overrides to use different defaults.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void set_default_config();

      m_is_active          = UVM_ACTIVE;
      m_enable_monitor     = 1;
      m_enable_coverage    = 1;
      m_enable_scoreboard  = 1;

   endfunction: set_default_config
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: set_passive
   //
   // Set fields such that agent will operate as a passive agent (not driving interface signals).
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void set_passive();

      m_is_active = UVM_PASSIVE;

   endfunction: set_passive
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : riv_rdy_vld_source_config
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // RIV_RDY_VLD_SOURCE_CONFIG_SVH_
