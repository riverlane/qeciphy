//------------------------------------------------------------------------------------------------------------------------------------------
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_ENV_STATE_SCOREBOARD_SVH_
`define QECIPHY_ENV_STATE_SCOREBOARD_SVH_

// Class: qeciphy_env_state_scoreboard
//
// Abstract:
// Predict and check the value of the QECi-Phy STATUS outputs based on DUT activity.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_env_state_scoreboard extends uvm_scoreboard;

   int  m_num_errors;               // Number of scoreboard errors detected.
   bit  m_dut_state;                // Current state of DUT as reported by completed P-Channel transaction (1 = up, 0 = down).
   bit  m_tbphy_state;              // Current state of TB-Phy as reported by completed P-Channel transaction (1 = up, 0 = down).
   bit  m_requested_dut_state;      // Current requested-state of DUT as reported by start of P-Channel transaction (1 = up, 0 = down).
   bit  m_requested_tbphy_state;    // Current requested-state of TB-Phy as reported by start of P-Channel transaction (1 = up, 0 = down).
   bit  m_dut_power_up_pending;
   bit  m_dut_power_down_pending;
   bit  m_dut_cycle_pending;        // '1' during a DUT-initiated power-cycle (power-down then power-up).
   bit  m_tbphy_cycle_pending;      // '1' during a TB-Phy-initiated power-cycle (power-down then power-up).

   `uvm_component_utils_begin(qeciphy_env_state_scoreboard)
      `uvm_field_int(m_num_errors,            UVM_DEFAULT | UVM_UNSIGNED)
      `uvm_field_int(m_dut_state,             UVM_DEFAULT | UVM_BIN)
      `uvm_field_int(m_tbphy_state,           UVM_DEFAULT | UVM_BIN)
      `uvm_field_int(m_requested_dut_state,   UVM_DEFAULT | UVM_BIN)
      `uvm_field_int(m_requested_tbphy_state, UVM_DEFAULT | UVM_BIN)
      `uvm_field_int(m_dut_cycle_pending,     UVM_DEFAULT | UVM_BIN)
      `uvm_field_int(m_tbphy_cycle_pending,   UVM_DEFAULT | UVM_BIN)
   `uvm_component_utils_end

   // Analysis ports to receive transaction items (uvm_analysis_imp_* classes declared in qeciphy_env_common).
   uvm_analysis_imp_dut_pbus_ap#(         riv_pbus_controller_txn, qeciphy_env_state_scoreboard) dut_pbus_ap_imp;
   uvm_analysis_imp_tbphy_pbus_ap#(       riv_pbus_controller_txn, qeciphy_env_state_scoreboard) tbphy_pbus_ap_imp;
   uvm_analysis_imp_dut_pbus_start_ap#(   riv_pbus_controller_txn, qeciphy_env_state_scoreboard) dut_pbus_start_ap_imp;
   uvm_analysis_imp_tbphy_pbus_start_ap#( riv_pbus_controller_txn, qeciphy_env_state_scoreboard) tbphy_pbus_start_ap_imp;

   virtual qeciphy_env_miscio_if   m_miscio_vif;   // Virtual interface containing the STATUS and ECODE pins.

   event m_dut_power_up_evt;        // Triggered when DUT P-Channel requests a power-up.
   event m_dut_power_down_evt;      // Triggered when DUT P-Channel requests a power-down.
   event m_tbphy_power_up_evt;      // Triggered when TB-Phy P-Channel requests a power-up.
   event m_tbphy_power_down_evt;    // Triggered when TB-Phy P-Channel requests a power-down.

   qeciphy_env_config  m_config;    // Config object for the agent (fetched from ConfigDB).

   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //---------------------------------------------------------------------------------------------------------------------------------------
   function new(string name, uvm_component parent);

      super.new(name, parent);

      // Create analysis port implementations.
      dut_pbus_ap_imp         = new("dut_pbus_ap_imp",         this);
      tbphy_pbus_ap_imp       = new("tbphy_pbus_ap_imp",       this);
      dut_pbus_start_ap_imp   = new("dut_pbus_start_ap_imp",   this);
      tbphy_pbus_start_ap_imp = new("tbphy_pbus_start_ap_imp", this);

   endfunction : new
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_phase
   //
   // Get the config object from ConfigDB and create any other objects needed by this scoreboard.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".build_phase"};

      if (! uvm_config_db#(qeciphy_env_config)::get(this, "", "config", m_config) ) begin
         `uvm_fatal(msg_id, "Can't find field 'config' in ConfigDB")
      end

   endfunction : build_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: run_phase
   //
   // Wait for new transactions (or any other events, such as signal changes on the interface) and act upon them.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".run_phase"};

      m_miscio_vif = m_config.m_vifs.miscio_vif;      // Initialise local VIF pointer from the config object.

      forever begin

         // Wait for reset to go away, checking that PHY remains reset until it does so.
         // If first state after reset is not PHY_WAIT_FOR_RESET, then whole FSM is bad so stop checking until next reset.
         wait (m_miscio_vif.dut_arst_n === 1'b0);
         m_dut_state             = 1'b1;
         m_tbphy_state           = 1'b1;
         m_requested_dut_state   = 1'b1;
         m_requested_tbphy_state = 1'b1;
         m_dut_cycle_pending     = 1'b0;
         m_tbphy_cycle_pending   = 1'b0;

         // Allow reset to take effect and then check that DUT is in reset until reset goes away (synchronously).
         #1.0ns
         while (m_miscio_vif.dut_arst_n === 1'b0) begin
            void'(check_status("DUT", PHY_RESET));
            @(posedge m_miscio_vif.dut_aclk);
         end

         // Once out of reset, check FSM operation until next reset happens.
         fork
            wait (m_miscio_vif.dut_arst_n === 1'b0);
            check_fsm_states();
         join_any
         disable fork;

      end

   endtask : run_phase
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_fsm_states
   //
   // On entry, FSM should be in PHY_WAIT_FOR_RESET state (global reset is asynchronous and handled by calling task).
   // Checks that FSM states occur in a valid sequence.
   // If FSM goes wrong, checking will be aborted and control returned to calling task to wait for next reset.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual task check_fsm_states();
      const string        msg_id = {get_type_name(), ".check_fsm_states"};
      qeciphy_state_enum  exp_dut_status;
      qeciphy_state_enum  prev_dut_status;
      bit                 fsm_error;

      exp_dut_status  = PHY_WAIT_FOR_RESET;
      prev_dut_status = PHY_WAIT_FOR_RESET;
      fsm_error       = 1'b0;
      forever begin

         @(posedge m_miscio_vif.dut_aclk);

         prev_dut_status = exp_dut_status;
         case (exp_dut_status)
            PHY_RESET              : exp_dut_status = check_reset_state(fsm_error);
            PHY_WAIT_FOR_RESET     : exp_dut_status = check_wait_for_reset_state(fsm_error);
            PHY_LINK_TRAINING      : exp_dut_status = check_link_training_state(fsm_error);
            PHY_RX_LOCKED          : exp_dut_status = check_rx_locked_state(fsm_error);
            PHY_LINK_READY         : exp_dut_status = check_link_ready_state(fsm_error);
            PHY_SLEEP              : exp_dut_status = check_sleep_state(fsm_error);
            PHY_WAIT_FOR_POWERDOWN : exp_dut_status = check_wait_for_powerdown_state(fsm_error);
            PHY_FAULT_FATAL        : exp_dut_status = check_fault_fatal_state(fsm_error);
         endcase
         if (exp_dut_status != prev_dut_status) begin
            `uvm_info(msg_id, $sformatf("Exp status changed from %0s to %0s", prev_dut_status, exp_dut_status), UVM_LOW)
         end

         // Report any error that occurs and stop checking - FSM has gone wrong so operation is now undefined.
         if (fsm_error) begin
            `uvm_error(msg_id, "FSM error detected");
            m_num_errors++;
            break;
         end

      end

   endtask : check_fsm_states
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_reset_state
   //
   // Stay in RESET for only one clock and then transition to WAIT_FOR_RESET.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function qeciphy_state_enum check_reset_state(output bit error = 1'b0);

      error = ~check_status("DUT", PHY_WAIT_FOR_RESET);
      return (PHY_WAIT_FOR_RESET);

   endfunction : check_reset_state
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_wait_for_reset_state
   //
   // Stay in WAIT_FOR_RESET for a while and only allowed transition is to LINK_TRAINING.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function qeciphy_state_enum check_wait_for_reset_state(output bit error = 1'b0);

      if (get_status("DUT") != PHY_WAIT_FOR_RESET) begin
         error = ~check_status("DUT", PHY_LINK_TRAINING);
         return (PHY_LINK_TRAINING);
      end

      return (PHY_WAIT_FOR_RESET);

   endfunction : check_wait_for_reset_state
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_link_training_state
   //
   // Stay in LINK_TRAINING indefinitely and only allowed transition is to RX_LOCKED.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function qeciphy_state_enum check_link_training_state(output bit error = 1'b0);

      if (get_status("DUT") != PHY_LINK_TRAINING) begin
         error = ~check_status("DUT", PHY_RX_LOCKED);
         return (PHY_RX_LOCKED);
      end

      return (PHY_LINK_TRAINING);

   endfunction : check_link_training_state
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_rx_locked_state
   //
   // Stay in RX_LOCKED state for a while and only allowed transition is to LINK_READY.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function qeciphy_state_enum check_rx_locked_state(output bit error = 1'b0);

      if (get_status("DUT") != PHY_RX_LOCKED) begin
         error = ~check_status("DUT", PHY_LINK_READY);
         return (PHY_LINK_READY);
      end

      return (PHY_RX_LOCKED);

   endfunction : check_rx_locked_state
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_link_ready_state
   //
   // When in LINK_READY, any change is an error unless:
   //    Error code is non-0. Next state must be FAULT_FATAL.
   //    Local power-down request received. Next state must be PHY_SLEEP.
   //    Remote power-down request received. Next state must be PHY_WAIT_FOR_POWERDOWN.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function qeciphy_state_enum check_link_ready_state(output bit error = 1'b0);
      const string        msg_id = {get_type_name(), ".check_link_ready_state"};
      qeciphy_state_enum  status;

      status = get_status("DUT");
      if (status != PHY_LINK_READY) begin

         if (m_miscio_vif.dut_ecode !== 4'b0000) begin
            error = ~check_status("DUT", PHY_FAULT_FATAL);
            return (PHY_FAULT_FATAL);
         end

         if (m_requested_dut_state == 1'b0) begin
            error = ~check_status("DUT", PHY_SLEEP);
            return (PHY_SLEEP);
         end

         if (m_requested_tbphy_state == 1'b0) begin
            error = ~check_status("DUT", PHY_WAIT_FOR_POWERDOWN);
            return (PHY_WAIT_FOR_POWERDOWN);
         end

         `uvm_error(msg_id, $sformatf("DUT status not PHY_LINK_READY (%0s)", status.name()))
         error = 1'b1;
         m_num_errors++;

      end

      return (PHY_LINK_READY);

   endfunction : check_link_ready_state
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_fault_fatal_state
   //
   // Stay in FAULT_FATAL forever.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function qeciphy_state_enum check_fault_fatal_state(output bit error = 1'b0);

      error = ~check_status("DUT", PHY_FAULT_FATAL);
      return (PHY_FAULT_FATAL);

   endfunction : check_fault_fatal_state
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_sleep_state
   //
   // Stay in SLEEP until some time after DUT power-up request. Even then, the only allowed transition is to WAIT_FOR_RESET.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function qeciphy_state_enum check_sleep_state(output bit error = 1'b0);
      const string        msg_id = {get_type_name(), ".check_sleep_state"};
      qeciphy_state_enum  status;

      status = get_status("DUT");
      if (status != PHY_SLEEP) begin

         if (m_requested_dut_state == 1'b1) begin
            error =~check_status("DUT", PHY_WAIT_FOR_RESET);
            return (PHY_WAIT_FOR_RESET);
         end

         // If state has changed for any other reason, then it's an error.
         `uvm_error(msg_id, $sformatf("DUT status not PHY_SLEEP (%0s)", status.name()))
         error = 1'b1;
         m_num_errors++;

      end

      return (PHY_SLEEP);

   endfunction : check_sleep_state
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Task: check_wait_for_powerdown_state
   //
   // Stay in WAIT_FOR_POWERDOWN until after remote power-down request completes. Even then, only allowed transition is to RESET.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function qeciphy_state_enum check_wait_for_powerdown_state(output bit error = 1'b0);
      const string        msg_id = {get_type_name(), ".check_wait_for_powerdown_state"};
      qeciphy_state_enum  status;

      status = get_status("DUT");
      if (status != PHY_WAIT_FOR_POWERDOWN) begin

         if (m_tbphy_state == 1'b0) begin
            error = ~check_status("DUT", PHY_RESET);
            return (PHY_RESET);
         end

         // If state has changed for any other reason, then it's an error (check_status will always fail).
         `uvm_error(msg_id, $sformatf("DUT status not PHY_WAIT_FOR_POWERDOWN (%0s)", status.name()))
         error = 1'b1;
         m_num_errors++;

      end

      return (PHY_WAIT_FOR_POWERDOWN);

   endfunction : check_wait_for_powerdown_state
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: get_status
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function qeciphy_state_enum get_status(string device);
      const string msg_id = {get_type_name(), ".get_status"};

      case (device)
         "DUT"    :  return (qeciphy_state_enum'(m_miscio_vif.dut_status));
         "TBPHY"  :  return (qeciphy_state_enum'(m_miscio_vif.tbphy_status));
         default  :  begin
                        `uvm_fatal(msg_id, $sformatf("Invalid device: %0s", device))
                        return (PHY_RESET);
                     end
      endcase

   endfunction : get_status
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: check_status
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function bit check_status(string device, qeciphy_state_enum exp_status);
      const string        msg_id = {get_type_name(), ".check_status"};
      qeciphy_state_enum  status;

      status = get_status(device);
      if (status !== exp_status) begin
         `uvm_error(msg_id, $sformatf("%0s status not %0s (%0s)", device, exp_status.name(), status.name()))
         m_num_errors++;
         return 0;
      end

      return 1;

   endfunction : check_status
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: write_dut_pbus_ap
   //
   // Gets called when receiving DUT P-Bus transactions once a power-change request has completed.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void write_dut_pbus_ap(riv_pbus_controller_txn t);
      const string msg_id = {get_type_name(), ".write_dut_pbus_ap"};

      if ((t.state !== 1'b1) && (t.state !== 1'b0)) begin
         `uvm_error(msg_id, $sformatf("Invalid transaction state : %0b", t.state))
         m_num_errors++;
         return;
      end

      // On completion of a power-up, any existing DUT-initiated power-cycle is complete.
      if (t.state == 1'b1) m_dut_cycle_pending = 1'b0;

      `uvm_info(msg_id, $sformatf("DUT P-Channel power-%0s request complete", (t.state == 1'b1) ? "up" : "down"), UVM_MEDIUM)
      m_dut_state = t.state;

   endfunction : write_dut_pbus_ap
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: write_tbphy_pbus_ap
   //
   // Gets called when receiving TB-Phy P-Bus transactions once a power-change request has completed.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void write_tbphy_pbus_ap(riv_pbus_controller_txn t);
      const string msg_id = {get_type_name(), ".write_tbphy_pbus_ap"};

      if ((t.state !== 1'b1) && (t.state !== 1'b0)) begin
         `uvm_error(msg_id, $sformatf("Invalid transaction state : %0b", t.state))
         m_num_errors++;
         return;
      end

      // On completion of a power-up, any existing TB-Phy-initiated power-cycle is complete.
      if (t.state == 1'b1) m_tbphy_cycle_pending = 1'b0;

      `uvm_info(msg_id, $sformatf("TB-Phy P-Channel power-%0s request complete", (t.state == 1'b1) ? "up" : "down"), UVM_MEDIUM)
      m_tbphy_state = t.state;

   endfunction : write_tbphy_pbus_ap
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: write_dut_pbus_start_ap
   //
   // Gets called when receiving DUT P-Bus transactions at the start of a power-change request.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void write_dut_pbus_start_ap(riv_pbus_controller_txn t);
      const string        msg_id = {get_type_name(), ".write_dut_pbus_start_ap"};
      qeciphy_state_enum  status;

      if ((t.state !== 1'b1) && (t.state !== 1'b0)) begin
         `uvm_error(msg_id, $sformatf("Invalid transaction state : %0b", t.state))
         m_num_errors++;
         return;
      end

      `uvm_info(msg_id, $sformatf("DUT P-Channel power-%0s request received", (t.state == 1'b1) ? "up" : "down"), UVM_MEDIUM)
      status = get_status("DUT");

      // Check that power-change is happening at a valid time (if not, then behaviour is undefined and scoreboard will be invalid).
      if (t.state == 1'b0) begin
         if (m_dut_cycle_pending || m_tbphy_cycle_pending || (status !== PHY_LINK_READY)) begin
            if (m_dut_cycle_pending)       `uvm_error(msg_id, "Requesting power-down when DUT cycle already running")
            if (m_tbphy_cycle_pending)     `uvm_error(msg_id, "Requesting power-down when TB-Phy cycle already running")
            if (status !== PHY_LINK_READY) `uvm_error(msg_id, $sformatf("Requesting power-down when in %0s state", status.name()))
            m_num_errors++;
            return;
         end
      end
      if (t.state == 1'b1) begin
         if (!m_dut_cycle_pending || m_tbphy_cycle_pending || (status !== PHY_SLEEP)) begin
            if (!m_dut_cycle_pending)  `uvm_error(msg_id, "Requesting power-up when DUT cycle not running")
            if (m_tbphy_cycle_pending) `uvm_error(msg_id, "Requesting power-up when TB-Phy cycle already running")
            if (status !== PHY_SLEEP)  `uvm_error(msg_id, $sformatf("Requesting power-up when in %0s state", status.name()))
            m_num_errors++;
            return;
         end
      end

      m_dut_cycle_pending   = 1'b1;
      m_requested_dut_state = t.state;
      case (t.state)
         1'b1 : -> m_dut_power_up_evt;
         1'b0 : -> m_dut_power_down_evt;
      endcase

   endfunction : write_dut_pbus_start_ap
   //---------------------------------------------------------------------------------------------------------------------------------------


   //---------------------------------------------------------------------------------------------------------------------------------------
   // Function: write_tbphy_pbus_start_ap
   //
   // Gets called when receiving TB-Phy P-Bus transactions at the start of a power-change request.
   //---------------------------------------------------------------------------------------------------------------------------------------
   virtual function void write_tbphy_pbus_start_ap(riv_pbus_controller_txn t);
      const string        msg_id = {get_type_name(), ".write_tbphy_pbus_start_ap"};
      qeciphy_state_enum  status;

      if ((t.state !== 1'b1) && (t.state !== 1'b0)) begin
         `uvm_error(msg_id, $sformatf("Invalid transaction state : %0b", t.state))
         m_num_errors++;
         return;
      end

      `uvm_info(msg_id, $sformatf("TB-Phy P-Channel power-%0s request received", (t.state == 1'b1) ? "up" : "down"), UVM_MEDIUM)
      status = get_status("TBPHY");

      // Check that power-change is happening at a valid time (if not, then behaviour is undefined and scoreboard will be invalid).
      if (t.state == 1'b0) begin
         if (m_dut_cycle_pending || m_tbphy_cycle_pending || (status !== PHY_LINK_READY)) begin
            if (m_dut_cycle_pending)       `uvm_error(msg_id, "Requesting power-down when DUT cycle already running")
            if (m_tbphy_cycle_pending)     `uvm_error(msg_id, "Requesting power-down when TB-Phy cycle already running")
            if (status !== PHY_LINK_READY) `uvm_error(msg_id, $sformatf("Requesting power-down when in %0s state", status.name()))
            m_num_errors++;
            return;
         end
      end
      if (t.state == 1'b1) begin
         if (m_dut_cycle_pending || !m_tbphy_cycle_pending || (status !== PHY_SLEEP)) begin
            if (m_dut_cycle_pending)    `uvm_error(msg_id, "Requesting power-up when DUT cycle already running")
            if (!m_tbphy_cycle_pending) `uvm_error(msg_id, "Requesting power-up when TB-Phy cycle not running")
            if (status !== PHY_SLEEP)   `uvm_error(msg_id, $sformatf("Requesting power-up when in %0s state", status.name()))
            m_num_errors++;
            return;
         end
      end

      m_tbphy_cycle_pending   = 1'b1;
      m_requested_tbphy_state = t.state;
      case (t.state)
         1'b1 : -> m_tbphy_power_up_evt;
         1'b0 : -> m_tbphy_power_down_evt;
      endcase

   endfunction : write_tbphy_pbus_start_ap
   //---------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_env_state_scoreboard
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_ENV_STATE_SCOREBOARD_SVH_
