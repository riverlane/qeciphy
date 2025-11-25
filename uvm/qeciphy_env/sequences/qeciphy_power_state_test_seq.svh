
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_POWER_STATE_TEST_SEQ_SVH_
`define QECIPHY_POWER_STATE_TEST_SEQ_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_power_state_test_seq
//
// Abstract:
// Randomly cycles the DUT between low- and active-power states.
// Cycles can be initiated by the DUT or the TB-Phy, but only one can initiate them at a time.
// See the field descriptions below for details of how to constrain the sequence.
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_power_state_test_seq extends qeciphy_base_seq;

   // Randomized variables.
   rand int m_num_dut_cycles;                // Number of DUT-iniitated cycles to do (default 1-5).
   rand int m_num_tbphy_cycles;              // Number of TB-Phy-iniitated cycles to do (default 1-5).
   rand int m_min_cycle_gap_ns;              // Minimum time (in ns) from link up before each power cycle (default 0us).
   rand int m_max_cycle_gap_ns;              // Maximum time (in ns) from link up before each power cycle (default 200us).
   rand int m_min_cycle_duration_ns;         // Minimum time (in ns) before powered-down device powers back up (default 30us).
   rand int m_max_cycle_duration_ns;         // Maximum time (in ns) before powered-down device powers back up (default 60us).

   // Randomized but intended to be locally-constrainted only (although in-line with {} constraints can be used if needed).
   rand int m_dut_cycle_gaps_ns[];           // Time (in ns) between link being up and the next DUT-initiated power-cycle.
   rand int m_dut_cycle_durations_ns[];      // Duration (in ns) of each DUT-initiated power-cycle.
   rand int m_tbphy_cycle_gaps_ns[];         // Time (in ns) between link being up and the next TB-Phy-initiated power-cycle.
   rand int m_tbphy_cycle_durations_ns[];    // Duration (in ns) of each TB-Phy-initiated power-cycle.

   `uvm_object_utils_begin(qeciphy_power_state_test_seq)
      `uvm_field_int (m_num_dut_cycles,        UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (m_num_tbphy_cycles,      UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (m_min_cycle_gap_ns,      UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (m_max_cycle_gap_ns,      UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (m_min_cycle_duration_ns, UVM_DEFAULT | UVM_DEC)
      `uvm_field_int (m_max_cycle_duration_ns, UVM_DEFAULT | UVM_DEC)
   `uvm_object_utils_end

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Constraints
   //----------------------------------------------------------------------------------------------------------------------------------------
   // These constraints have to be obeyed for correct operation.
   constraint c_vld_cycle_gap {
      m_min_cycle_gap_ns >= 0;
      m_max_cycle_gap_ns >= m_min_cycle_gap_ns;
   }
   constraint c_vld_cycle_duration {
      m_min_cycle_duration_ns >= 0;
      m_max_cycle_duration_ns >= m_min_cycle_duration_ns;
   }
   constraint c_vld_num_dut_cycles {
      solve m_num_dut_cycles before m_dut_cycle_gaps_ns, m_dut_cycle_durations_ns;
      m_num_dut_cycles                >= 0;
      m_dut_cycle_gaps_ns.size()      == m_num_dut_cycles;
      m_dut_cycle_durations_ns.size() == m_dut_cycle_gaps_ns.size();
   }
   constraint c_vld_num_tbphy_cycles {
      solve m_num_tbphy_cycles before m_tbphy_cycle_gaps_ns, m_tbphy_cycle_durations_ns;
      m_num_tbphy_cycles                >= 0;
      m_tbphy_cycle_gaps_ns.size()      == m_num_tbphy_cycles;
      m_tbphy_cycle_durations_ns.size() == m_tbphy_cycle_gaps_ns.size();
   }

   // These soft constraints are default values but can be overridden by in-line constraints.
   constraint c_dflt_num_dut_cycles       { soft m_num_dut_cycles          inside {[1 : 5]}; }
   constraint c_dflt_num_tbphy_cycles     { soft m_num_tbphy_cycles        inside {[1 : 5]}; }
   constraint c_dflt_min_cycle_gap        { soft m_min_cycle_gap_ns            ==       0;   }
   constraint c_dflt_max_cycle_gap        { soft m_max_cycle_gap_ns            == 200_000;   }
   constraint c_dflt_min_cycle_duration   { soft m_min_cycle_duration_ns       ==  30_000;   }
   constraint c_dflt_max_cycle_duration   { soft m_max_cycle_duration_ns       ==  60_000;   }

   // For both DUT- and TB-Phy-initiated cycles:
   //    All gaps between link-up and next cycle must be between permitted min/max values (but may be overridden).
   constraint c_dut_cycle_gaps {
      solve m_min_cycle_gap_ns, m_max_cycle_gap_ns before m_dut_cycle_gaps_ns;
      foreach (m_dut_cycle_gaps_ns[i]) {
         soft m_dut_cycle_gaps_ns[i] inside {[m_min_cycle_gap_ns : m_max_cycle_gap_ns]};
      }
   }
   constraint c_tbphy_cycle_gaps {
      solve m_min_cycle_gap_ns, m_max_cycle_gap_ns before m_tbphy_cycle_gaps_ns;
      foreach (m_tbphy_cycle_gaps_ns[i]) {
         soft m_tbphy_cycle_gaps_ns[i] inside {[m_min_cycle_gap_ns : m_max_cycle_gap_ns]};
      }
   }

   // For both DUT- and TB-Phy-initiated cycles:
   //    All cycle durations must be between permitted min/max values (but may be overridden).
   constraint c_dut_cycle_durations {
      solve m_min_cycle_duration_ns, m_max_cycle_duration_ns before m_dut_cycle_durations_ns;
      foreach (m_dut_cycle_durations_ns[i]) {
         soft m_dut_cycle_durations_ns[i] inside {[m_min_cycle_duration_ns : m_max_cycle_duration_ns]};
      }
   }
   constraint c_tbphy_cycle_durations {
      solve m_min_cycle_duration_ns, m_max_cycle_duration_ns before m_tbphy_cycle_durations_ns;
      foreach (m_tbphy_cycle_durations_ns[i]) {
         soft m_tbphy_cycle_durations_ns[i] inside {[m_min_cycle_duration_ns : m_max_cycle_duration_ns]};
      }
   }
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
   // Wait for link to come up and then, concurrently:
   //    Randomly cycle DUT through power-down/-up states (exclusive with TB-Phy).
   //    Randomly cycle TB-Phy through power-down/-up states (exclusive with DUT).
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task body ();
      const string                 msg_id = { get_type_name(), ".body" };
      qeciphy_wait_link_ready_seq  wait_link_ready_seq;
      bit                          dut_cycle_next;
      int                          dut_cycle_idx;
      int                          tbphy_cycle_idx;

      `uvm_info (
         msg_id,
         $sformatf (
            "Running %0d DUT and %0d TB-Phy power-state-cycles spaced by %0dns to %0dns and lasting %0dns to %0dns...",
            m_num_dut_cycles, m_num_tbphy_cycles, m_min_cycle_gap_ns, m_max_cycle_gap_ns, m_min_cycle_duration_ns, m_max_cycle_duration_ns
         ),
         UVM_LOW
      )

      // Wait until LINK is up.
      `uvm_do_with(wait_link_ready_seq, { m_timeout_us == 100_000.0; })

      // Iterate over all cycles on both devices, randomly selecting which device will initiate a power-state-cycle next.
      dut_cycle_idx   = 0;
      tbphy_cycle_idx = 0;
      while ((dut_cycle_idx < m_num_dut_cycles) || (tbphy_cycle_idx < m_num_tbphy_cycles)) begin
         std::randomize(dut_cycle_next) with {
            (dut_cycle_idx   >= m_num_dut_cycles)   -> dut_cycle_next == 1'b0;
            (tbphy_cycle_idx >= m_num_tbphy_cycles) -> dut_cycle_next == 1'b1;
         };
         if (dut_cycle_next) begin
            #(m_dut_cycle_gaps_ns[dut_cycle_idx] * 1.0ns);
            power_state_cycle("DUT", m_dut_cycle_durations_ns[dut_cycle_idx]);
            dut_cycle_idx++;
         end else begin
            #(m_tbphy_cycle_gaps_ns[tbphy_cycle_idx] * 1.0ns);
            power_state_cycle("TB-Phy", m_tbphy_cycle_durations_ns[tbphy_cycle_idx]);
            tbphy_cycle_idx++;
         end
      end

      // Wait at end of test to allow detection of unexpected side-effects and to allow final signal states to be viewable on waveforms.
      #1us;

   endtask: body
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: power_state_cycle
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task power_state_cycle (string target, int duration_ns);
      const string                       msg_id = { get_type_name(), ".power_state_cycle" };
      qeciphy_wait_link_ready_seq        wait_link_ready_seq;
      int                                rand_ok;

      // Initiate a power-down, wait for required duration then power up.
      set_power_state(target, 0);
      #(duration_ns * 1.0ns);
      set_power_state(target, 1);

      // Wait until LINK is up
      `uvm_do_with(wait_link_ready_seq, { m_timeout_us == 100_000.0; })

   endtask: power_state_cycle
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: set_power_state
   //
   // Set the state of the required device to either low-power (state = 0) or active (state = 1).
   // NOTE: QECi-Phy uses synchronous P-Channel, so align with clocks.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task set_power_state (string target, bit state);
      const string                       msg_id = { get_type_name(), ".power_state_cycle" };
      riv_pbus_controller_sequencer      seqr;
      riv_pbus_controller_set_state_seq  set_state_seq;
      int                                rand_ok;
      real                               aclk_prd_ns;

      // Select required sequencer and ACLK period then wait for next appropriate rising clock edge.
      case (target)
         "DUT"    :  begin
                        seqr        = p_sequencer.m_dut_pbus_seqr;
                        aclk_prd_ns = p_sequencer.m_config.m_dut_aclk_period_ns;
                        @(posedge p_sequencer.m_config.m_vifs.miscio_vif.dut_aclk);
                     end
         "TB-Phy" :  begin
                        seqr        = p_sequencer.m_tbphy_pbus_seqr;
                        aclk_prd_ns = p_sequencer.m_config.m_tbphy_aclk_period_ns;
                        @(posedge p_sequencer.m_config.m_vifs.miscio_vif.tbphy_aclk);
                     end
         default  : `uvm_fatal(msg_id, $sformatf("Bad target: %0s", target))
      endcase

      // Initiate a power-change with timings randomly distributed to cover < 1 ACLK, 1-2 ACLKs and > 2 ACLKs to test synchronizing).
      `uvm_info(msg_id, $sformatf("%0s requesting %0s state...", target, (state == 1'b0) ? "low-power" : "active"), UVM_LOW)
      set_state_seq = riv_pbus_controller_set_state_seq::type_id::create("set_state_seq", .contxt(get_full_name()));
      rand_ok = set_state_seq.randomize() with {
         new_state == state;
         tsu_state2req_ns  dist  {
                                    [0.1 : (aclk_prd_ns - 0.1)]                                 :/ 1,
                                    [((aclk_prd_ns * 1.0) + 0.1) : ((aclk_prd_ns * 2.0) - 0.1)] :/ 1,
                                    [((aclk_prd_ns * 2.0) + 0.1) : ((aclk_prd_ns * 9.0) - 0.1)] :/ 1
                                 };
         th_req2state_ns   dist  {
                                    [0.1 : (aclk_prd_ns - 0.1)]                                 :/ 1,
                                    [((aclk_prd_ns * 1.0) + 0.1) : ((aclk_prd_ns * 2.0) - 0.1)] :/ 1,
                                    [((aclk_prd_ns * 2.0) + 0.1) : ((aclk_prd_ns * 9.0) - 0.1)] :/ 1
                                 };
         tpd_accept2req_ns dist  {
                                    [0.1 : (aclk_prd_ns - 0.1)]                                 :/ 1,
                                    [((aclk_prd_ns * 1.0) + 0.1) : ((aclk_prd_ns * 2.0) - 0.1)] :/ 1,
                                    [((aclk_prd_ns * 2.0) + 0.1) : ((aclk_prd_ns * 9.0) - 0.1)] :/ 1
                                 };
      };
      set_state_seq.start(seqr, this);

   endtask: set_power_state
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_power_state_test_seq
//------------------------------------------------------------------------------------------------------------------------------------------

`endif  // QECIPHY_POWER_STATE_TEST_SEQ_SVH_
