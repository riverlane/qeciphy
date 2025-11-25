
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_WAIT_LINK_READY_SEQ_SVH_
`define QECIPHY_WAIT_LINK_READY_SEQ_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_wait_link_ready_seq
//
// Abstract:
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_wait_link_ready_seq extends qeciphy_base_seq;

   // Control/status variables - not randomized.
   // HINT: Declare control fields here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   // Randomized variables.
   rand real m_timeout_us;

   `uvm_object_utils_begin(qeciphy_wait_link_ready_seq)
      `uvm_field_real (m_timeout_us, UVM_DEFAULT)
   `uvm_object_utils_end

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //----------------------------------------------------------------------------------------------------------------------------------------
   constraint c_timeout          {      m_timeout_us >=       0.0; }
   constraint c_moderate_timeout { soft m_timeout_us == 100_000.0; }
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function new(string name = "");
      super.new(name);
   endfunction : new
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: body
   //
   // HINT: Add sequence actions to this task (this is the task that runs after a sequence is started on a sequencer).
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task body ();
      const string                   msg_id = { get_type_name(), ".body" };
      virtual qeciphy_env_miscio_if  miscio_vif;
      qeciphy_state_enum             dut_status;

      miscio_vif = p_sequencer.m_config.m_vifs.miscio_vif;
      `uvm_info(msg_id, $sformatf("Waiting up to %0.3fus for link to be ready...", m_timeout_us), UVM_LOW)
      fork
         #(m_timeout_us * 1.0us);
         do begin
            @(posedge miscio_vif.dut_aclk);
            dut_status = qeciphy_state_enum'(miscio_vif.dut_status);
         end while (dut_status != PHY_LINK_READY);
      join_any

      if (dut_status != PHY_LINK_READY) begin
         `uvm_error(msg_id, $sformatf("Link not ready (state = %0s) after %03.fus.", dut_status, m_timeout_us))
      end else begin
         `uvm_info(msg_id, $sformatf("Link is up"), UVM_LOW)
      end

   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_wait_link_ready_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_WAIT_LINK_READY_SEQ_SVH_
