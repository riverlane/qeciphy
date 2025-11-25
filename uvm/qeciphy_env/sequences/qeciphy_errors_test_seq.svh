
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_ERRORS_TEST_SEQ_SVH_
`define QECIPHY_ERRORS_TEST_SEQ_SVH_

//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_errors_test_seq
//
// Abstract:
// Whilst sending bursts (max-speed or stuttery) of data, momentarily introduce a bit error to the DUT serial receive-stream.
// Sequence can be constrained by constraining the m_num_errors, m_min_delay_ps, m_max_delay_ps and m_error_width_ps fields (see below).
// If no constraints are given during randomization, default values are used.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_errors_test_seq extends qeciphy_base_seq;

   // Randomized variables.
   rand int m_num_errors;        // Number of iterations to run with one error per iteration (DUT resets after an error).
   rand int m_min_delay_ps;      // Minimum time (in ps) into the data stream at which to generate an error.
   rand int m_max_delay_ps;      // Maximum time (in ps) into the data stream at which to generate an error.
   rand int m_error_width_ps;    // Duration (in ps) of the error condition.
   rand int m_min_stutter_clks;  // Minimum time (number of clks) between "stuttery" AXI-S data transfers.
   rand int m_max_stutter_clks;  // Maximum time (number of clks) between "stuttery" AXI-S data transfers.

   `uvm_object_utils_begin(qeciphy_errors_test_seq)
      `uvm_field_int  (m_num_errors,       UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_min_delay_ps,     UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_max_delay_ps,     UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_error_width_ps,   UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_min_stutter_clks, UVM_DEFAULT | UVM_DEC)
      `uvm_field_int  (m_max_stutter_clks, UVM_DEFAULT | UVM_DEC)
   `uvm_object_utils_end

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //----------------------------------------------------------------------------------------------------------------------------------------
   constraint c_vld_num_errors       { m_num_errors       >  0;                  }
   constraint c_vld_error_width      { m_error_width_ps   >  0;                  }
   constraint c_vld_min_delay        { m_min_delay_ps     >  0;                  }
   constraint c_vld_max_delay        { m_max_delay_ps     >  m_min_delay_ps;     }
   constraint c_vld_min_stutter_clks { m_min_stutter_clks >  0;                  }
   constraint c_vld_max_stutter_clks { m_max_stutter_clks >= m_min_stutter_clks; }

   // These set some "sensible" upper limits - disable or override if greater limits are needed.
   constraint c_dflt_max_num_errors   { soft m_num_errors       <        100; }
   constraint c_dflt_max_error_width  { soft m_min_delay_ps     < 10_000_000; }
   constraint c_dflt_max_delay        { soft m_error_width_ps   <  1_000_000; }
   constraint c_dflt_max_stutter_clks { soft m_max_stutter_clks <        500; }
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
   // Reset DUT and TB-Phy then send streams of data in both directions until an error is inserted into the DUT Rx stream.
   // Repeat this for the required number of times.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task body ();
      const string                 msg_id = { get_type_name(), ".body" };
      qeciphy_wait_link_ready_seq  wait_link_ready_seq;
      qeciphy_reset_seq            reset_seq;
      qeciphy_error_enum           ecode;
      int                          rand_ok;

      for (int i = 1; i <= m_num_errors; i++) begin : test_loop

         // Reset the DUT and TBPHY to clear errors from any previous iteration.
         reset_seq = qeciphy_reset_seq::type_id::create("reset_seq", .contxt(get_full_name()));
         rand_ok = reset_seq.randomize();
         if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize reset_seq")
         reset_seq.start(p_sequencer);
         #100ns;

         `uvm_info(msg_id, $sformatf("Running test-loop %0d of %0d...", i, m_num_errors), UVM_LOW)

         // Wait until LINK is up.
         if($test$plusargs("ERROR_CHECK"))begin
            fork
              `uvm_do_with(wait_link_ready_seq, { m_timeout_us == 100_00.0; });
              generate_error(.min_delay_ps(m_min_delay_ps), .max_delay_ps(m_max_delay_ps), .error_width_ps(m_error_width_ps));
            join
         end else begin
            `uvm_do_with(wait_link_ready_seq, { m_timeout_us == 100_000.0; });
         end

         // Start some random data streaming in both directions and cause an error at some random time.
         // NOTE: stream_data() never returns but generate_error() returns once error has happened.
         fork
            stream_data("DUT");
            stream_data("TBPHY");
            generate_error(.min_delay_ps(m_min_delay_ps), .max_delay_ps(m_max_delay_ps), .error_width_ps(m_error_width_ps));
         join_any
         disable fork;

         // After allowing some time for error to be seen, check that one actually happened.
         #200ns;
         ecode = qeciphy_error_enum'(p_sequencer.m_config.m_vifs.miscio_vif.dut_ecode);
         if (! (ecode inside {PHY_FAP_MISSING, PHY_CRC_ERROR})) begin
            `uvm_error(msg_id, $sformatf("Expected error but got %04b", ecode))
            break;
         end

      end : test_loop


   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: stream_data
   //
   // Send a continuous stream of words from the indicated device (DUT or TBPHY).
   // Note that the stream is designed to be "bursty" - sometimes at max data rate, sometimes with random gaps between words.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task stream_data (string device);
      const string                  msg_id = { get_type_name(), ".stream_data" };
      riv_rdy_vld_source_txn        txn;
      riv_rdy_vld_source_sequencer  seqr;
      bit                           max_speed;
      int                           rand_ok;

      case (device)
         "DUT"   : seqr = p_sequencer.m_dut_axis_tx_seqr;
         "TBPHY" : seqr = p_sequencer.m_tbphy_axis_tx_seqr;
         default : `uvm_fatal(msg_id, $sformatf("Bad device: %0s", device))
      endcase

      forever begin

         // Randomly select max-speed or stuttery stream
         if (! std::randomize(max_speed)) `uvm_fatal(msg_id, "Failed to randomize max_speed")

         txn = riv_rdy_vld_source_txn::type_id::create("txn", .contxt(get_full_name()));
         start_item(txn, .sequencer(seqr));
         rand_ok = txn.randomize() with {
            m_data.size() dist {[10 : 20] :/ 1, [21 : 100] :/ 1};
            foreach (m_delays_clks[i]) {
               max_speed  -> m_delays_clks[i] == 0;
               !max_speed -> m_delays_clks[i] inside {[m_min_stutter_clks : m_max_stutter_clks]};
            }
         };
         if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize txn")
         finish_item(txn);

      end

   endtask: stream_data
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: generate_error
   //
   // Wait for a period of time and then generate a bit-error on the DUT's receive serial link.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task generate_error (int min_delay_ps, int max_delay_ps, int error_width_ps);
      const string  msg_id = { get_type_name(), ".generate_error" };
      int           delay_ps;
      int           rand_ok;

      virtual riv_diff_pair_connector_vip_if  connector_vif;

      connector_vif = p_sequencer.m_config.m_vifs.tbphy2dut_conn_vif;

      rand_ok = std::randomize(delay_ps) with { delay_ps inside {[min_delay_ps : max_delay_ps]}; };
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize delay_ps")

      #(delay_ps * 1.0ps);
      `uvm_info(msg_id, $sformatf("Applying error condition for %0dps...", error_width_ps), UVM_LOW)
      connector_vif.set_swap_status(1);
      #(error_width_ps * 1.0ps);
      connector_vif.set_swap_status(0);
      `uvm_info(msg_id, $sformatf("Error condition released."), UVM_LOW)

   endtask: generate_error
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_errors_test_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_ERRORS_TEST_SEQ_SVH_
