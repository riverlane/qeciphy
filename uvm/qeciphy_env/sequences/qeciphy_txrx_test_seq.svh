
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_TXRX_TEST_SEQ_SVH_
`define QECIPHY_TXRX_TEST_SEQ_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_txrx_test_seq
//
// Abstract:
// Run a stream of data in both directions through the DUT (using a TB instance of the PHY to receive/generate DUT Tx/Rx data).
// The pacing and quantity of data is randomized (using m_num_*_xfers and m_in_/max_*_delay_clks fields),
// See the field descriptions below for details of how to constrain the sequence.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_txrx_test_seq extends qeciphy_base_seq;

   // Control/status variables - not randomized.
   // HINT: Declare control fields here (use m_ prefix) and also add them to the convert2string() and do_*() functions below.

   // Randomized variables.
   rand int  m_num_dut_xfers;                // Number of xfers to be sent into the DUT Tx AXI-S port.
   rand int  m_min_dut_delay_clks;           // Minimum number of clocks between each word sent into the DUT Tx AXI-S port (default 0).
   rand int  m_max_dut_delay_clks;           // Maximum number of clocks between each word sent into the DUT Tx AXI-S port (default 100).
   rand int  m_num_tbphy_xfers;              // Number of xfers to be sent into the TB-Phy Tx AXI-S port (to be received by DUT).
   rand int  m_min_tbphy_delay_clks;         // Minimum number of clocks between each word sent into the TB-Phy Tx AXI-S port (default 0).
   rand int  m_max_tbphy_delay_clks;         // Maximum number of clocks between each word sent into the TB-Phy Tx AXI-S port (default 100).

   `uvm_object_utils_begin(qeciphy_txrx_test_seq)
      `uvm_field_int  (m_num_dut_xfers,              UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_min_dut_delay_clks,         UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_max_dut_delay_clks,         UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_num_tbphy_xfers,            UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_min_tbphy_delay_clks,       UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_max_tbphy_delay_clks,       UVM_DEFAULT | UVM_DEC)
   `uvm_object_utils_end

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //----------------------------------------------------------------------------------------------------------------------------------------
   // These constraints have to be obeyed for correct operation.
   constraint c_vld_num_dut_xfers              { m_num_dut_xfers              >= 0; }
   constraint c_vld_num_tbphy_xfers            { m_num_tbphy_xfers            >= 0; }
   constraint c_vld_max_dut_delay_clks         { m_max_dut_delay_clks         >= m_min_dut_delay_clks; }
   constraint c_vld_max_tbphy_delay_clks       { m_max_tbphy_delay_clks       >= m_min_tbphy_delay_clks; }

   // These soft constraints result in default values (see post_randomize()) but can be overridden by in-line constraints.
   constraint c_dflt_min_dut_delay_clks         { soft m_min_dut_delay_clks         == -1; }
   constraint c_dflt_max_dut_delay_clks         { soft m_max_dut_delay_clks         == -1; }
   constraint c_dflt_min_tbphy_delay_clks       { soft m_min_tbphy_delay_clks       == -1; }
   constraint c_dflt_max_tbphy_delay_clks       { soft m_max_tbphy_delay_clks       == -1; }
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
   // Function: post_randomize
   //----------------------------------------------------------------------------------------------------------------------------------------
   function void post_randomize();

      // The following fields have defaults which are selected if the randomized field is invalid (e.g. -1)
      // This allows the use of soft constraints which can be overridden with in-line constraints which include the default value in their
      // range whilst still allowing full randomization within the range (otherwise the soft constraint would always be the result).
      if (m_min_dut_delay_clks == -1)    m_min_dut_delay_clks   =   0;
      if (m_max_dut_delay_clks == -1)    m_max_dut_delay_clks   = 100;
      if (m_min_tbphy_delay_clks == -1)  m_min_tbphy_delay_clks =   0;
      if (m_max_tbphy_delay_clks == -1)  m_max_tbphy_delay_clks = 100;

   endfunction : post_randomize
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: body
   //
   // HINT: Add sequence actions to this task (this is the task that runs after a sequence is started on a sequencer).
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task body ();
      const string                       msg_id = { get_type_name(), ".body" };
      qeciphy_wait_link_ready_seq        wait_link_ready_seq;

      `uvm_info (
         msg_id,
         $sformatf (
            "Running %0d DUT xfers (delays of %0d to %0d clocks) and %0d TB-Phy xfers (delays of %0d to %0d clocks)...",
            m_num_dut_xfers, m_min_dut_delay_clks, m_max_dut_delay_clks, m_num_tbphy_xfers, m_min_tbphy_delay_clks, m_max_tbphy_delay_clks
         ),
         UVM_LOW
      )

      // Wait until LINK is up.
      `uvm_do_with(wait_link_ready_seq, { m_timeout_us == 100_000.0; })

      // Send burst of data into the DUT's Tx AXI-S port and, via the TB Phy, out of the DUT's Rx AXI-S port.
      // NOTE: The bursts are broken into chunks of 1000 words to prevent VCS solver slow-down / breaking.
      fork

         // Send bursts of data into the DUT TX-AXI-S port, in bursts of 1000 words at a time.
         begin
            for (int i = 0; i <= m_num_dut_xfers - 1000; i += 1000) begin
               send_dut_burst(1000);
               `uvm_info(msg_id, $sformatf("Sent %0d out of %0d words into DUT Tx AXI-S port...", i + 1000, m_num_dut_xfers), UVM_LOW)
            end
            if ((m_num_dut_xfers % 1000) > 0) send_dut_burst(m_num_dut_xfers % 1000);
            `uvm_info(msg_id, $sformatf("Sent %0d words into DUT Tx AXI-S port...", m_num_dut_xfers), UVM_LOW)
         end

         // Send bursts of data into the TB-Phy TX-AXI-S port, in bursts of 1000 words at a time.
         begin
            for (int i = 0; i <= m_num_tbphy_xfers - 1000; i += 1000) begin
               send_tbphy_burst(1000);
               `uvm_info(msg_id, $sformatf("Sent %0d out of %0d words into TB Phy Tx AXI-S port...", i + 1000, m_num_tbphy_xfers), UVM_LOW)
            end
            if ((m_num_tbphy_xfers % 1000) > 0) send_tbphy_burst(m_num_tbphy_xfers % 1000);
            `uvm_info(msg_id, $sformatf("Sent %0d words into TB Phy Tx AXI-S port...", m_num_tbphy_xfers), UVM_LOW)
         end

      join

      // Wait at end of test to allow detection of unexpected side-effects and to allow final signal states to be viewable on waveforms.
      #1us;

   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: send_dut_burst
   //
   // Send a burst of words into the DUT TX AXI-S port.
   // NOTE: Bursts of over 10000 words can seriously slow / break the VCS solver due to large array size.
   // HINT: Override this task in extending sequences to change data and/or delay randomization.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task send_dut_burst (int num_xfers);
      const string            msg_id = { get_type_name(), ".send_dut_burst" };
      riv_rdy_vld_source_txn  txn;
      int                     rand_ok;

      if (num_xfers == 0) return;

      txn = riv_rdy_vld_source_txn::type_id::create("txn", .contxt(get_full_name()));
      start_item(txn, .sequencer(p_sequencer.m_dut_axis_tx_seqr));
      rand_ok = txn.randomize() with {
         m_data.size() == local::num_xfers;
         foreach (m_delays_clks[i]) { m_delays_clks[i] inside {[m_min_dut_delay_clks : m_max_dut_delay_clks]}; }
      };
      finish_item(txn);

   endtask: send_dut_burst
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: send_tbphy_burst
   //
   // Send a burst of words into the TB Phy TX AXI-S port.
   // NOTE: Bursts of over 10000 words can seriously slow / break the VCS solver due to large array size.
   // HINT: Override this task in extending sequences to change data and/or delay randomization.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task send_tbphy_burst (int num_xfers);
      const string            msg_id = { get_type_name(), ".send_tbphy_burst" };
      riv_rdy_vld_source_txn  txn;
      int                     rand_ok;

      if (num_xfers == 0) return;

      txn = riv_rdy_vld_source_txn::type_id::create("txn", .contxt(get_full_name()));
      start_item(txn, .sequencer(p_sequencer.m_tbphy_axis_tx_seqr));
      rand_ok = txn.randomize() with {
         m_data.size() == local::num_xfers;
         foreach (m_delays_clks[i]) { m_delays_clks[i] inside {[m_min_tbphy_delay_clks : m_max_tbphy_delay_clks]}; }
      };
      finish_item(txn);

   endtask: send_tbphy_burst
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_txrx_test_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_TXRX_TEST_SEQ_SVH_
