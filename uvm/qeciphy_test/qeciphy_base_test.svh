
// SPDX-License-Identifier: None
// Copyright (c) 2024-2025 Riverlane Ltd.
// Original authors: jamesf-rlane, ONDWARAKA

`ifndef QECIPHY_BASE_TEST_SVH_
`define QECIPHY_BASE_TEST_SVH_



//------------------------------------------------------------------------------------------------------------------------------------------
// Class: qeciphy_base_test
//
// Abstract:
//------------------------------------------------------------------------------------------------------------------------------------------
class qeciphy_base_test extends uvm_test;

   bit  m_disable_scoreboards = 0;    // 1 = Disable all scoreboards/checkers.
   bit  m_disable_coverage    = 0;    // 1 = Disable all coverage collectors.

   `uvm_component_utils_begin(qeciphy_base_test)
      `uvm_field_int(m_disable_scoreboards, UVM_DEFAULT | UVM_BIN)
      `uvm_field_int(m_disable_coverage,    UVM_DEFAULT | UVM_BIN)
   `uvm_component_utils_end

   qeciphy_env_config m_env_config;     // Config object to be used by the environment.
   qeciphy_env        m_env;            // The environment.
   uvm_reg_block      m_regs;           // UVM RAL register block used by the test

   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: new
   //
   // Class constructor.
   //----------------------------------------------------------------------------------------------------------------------------------------
   function new (string name = "", uvm_component parent);
      super.new(name, parent);
   endfunction
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_phase
   //
   // HINT: Unless specific functionality is required, tests extending this base class only need to override the methods called here.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".build_phase"};

      `uvm_info(msg_id, "Starting build_phase....", UVM_LOW)

      apply_factory_overrides();    // Apply any factory overrides.

      // Create the environment's configuration object.
      m_env_config = qeciphy_env_config::type_id::create("m_env_config", .contxt(get_full_name()));

      build_ral();                    // Build RAL model.
      m_env_config.m_regs = m_regs;   // Make RAL model available to environment.
      configure_environment();        // Define environment's configuration.
      process_command_line();         // Process any command line options.
      build_config_db();              // Build the configuration database.
      build_environment();            // Build the environment.

      `uvm_info(msg_id, "Finished build_phase.", UVM_LOW)

   endfunction : build_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: end_of_elaboration_phase
   //
   // Tidy up and print some config information (if verbosity level is high enough).
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void end_of_elaboration_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".end_of_elaboration_phase"};

      super.end_of_elaboration_phase(phase);

      if (get_report_verbosity_level() >= UVM_FULL) begin
         uvm_factory factory = uvm_factory::get();

         `uvm_info(msg_id, "Final TB Configuration: \n", UVM_FULL)
         uvm_top.print_topology();
         factory.print();
         `uvm_info(msg_id, $sformatf("Environment config set to:\n%0s", m_env_config.sprint()), UVM_FULL)

      end

   endfunction : end_of_elaboration_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: start_of_simulation_phase
   //
   // TB is loaded, built and connected and the test is about to start so print a unique message ("Okey Dokey") for log-file analysis.
   // If overriding this class, call super.start_of_simulation_phase() first.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void start_of_simulation_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".start_of_simulation_phase"};

      super.start_of_simulation_phase(phase);

      `uvm_info(msg_id, $sformatf("Okey Dokey - Test %0s has built and is about to run....", get_name()), UVM_NONE)

   endfunction : start_of_simulation_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: reset_phase
   //
   // Run a reset sequence to initialize the TB, reset the DUT and get it clocking.
   // To preserve standard messaging etc. tests are recommended to override the run_reset_sequence() method instead of this one.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task reset_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".reset_phase"};

      `uvm_info(msg_id, "Running reset sequence....", UVM_LOW)
      phase.raise_objection(this, "Reset sequence");
      run_reset_sequence();
      phase.drop_objection(this, "Reset sequence");
      `uvm_info(msg_id, "Finished reset sequence.", UVM_LOW)

   endtask : reset_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: main_phase
   //
   // Run the main test sequence to reset configure the DUT.
   // To preserve standard messaging etc. tests are recommended to override the run_main_test_sequence() method instead of this one.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task main_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".main_phase"};

      `uvm_info(msg_id, "Running main test sequence....", UVM_LOW)
      phase.raise_objection(this, "Main test sequence");
      run_main_test_sequence();
      phase.drop_objection(this, "Main test sequence");
      `uvm_info(msg_id, "Finished main test sequence.", UVM_LOW)

   endtask : main_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: report_phase
   //
   // Report PASS/FAIL message as needed for CI auto-checking.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void report_phase(uvm_phase phase);
      const string       msg_id = {get_type_name(), ".report_phase"};
      bit                stat;
      uvm_report_server  reportServer;

      super.report_phase(phase);

      `uvm_info(msg_id, "Reporting PASS/FAIL for auto-checker detection...\n", UVM_LOW)

      reportServer = uvm_report_server::get_server();

      `uvm_info(get_name(),"",UVM_NONE);
      `uvm_info(get_name(),"---Test Summary---",UVM_NONE);
      `uvm_info(get_name(),"",UVM_NONE);

      `uvm_info(get_name(),"",UVM_NONE);
      //report_header();
      //report_summarize();
      `uvm_info(get_name(),"",UVM_NONE);

      `uvm_info(get_name(),"---Final Test Status---",UVM_NONE);
      assert (reportServer.get_severity_count(UVM_FATAL) == 0 && reportServer.get_severity_count(UVM_ERROR) == 0) begin
         `uvm_info(get_name(),"",UVM_NONE);
         `uvm_info(get_name(),"***PASSED***",UVM_NONE);
         `uvm_info(get_name(),"",UVM_NONE);
      end else begin
         `uvm_info(get_name(),"",UVM_NONE);
         `uvm_error(get_name(),"***FAILED***");
         `uvm_info(get_name(),"",UVM_NONE);
      end

   endfunction : report_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: final_phase
   //
   // Do any tidying up and print a standard, unique message ("Top Banana") for log-file analysis.
   // To preserve standard messaging etc. tests are recommended to override the finalize_test() method instead of this one.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void final_phase(uvm_phase phase);
      const string msg_id = {get_type_name(), ".final_phase"};

      super.final_phase(phase);

      finalize_test();

      `uvm_info(msg_id, $sformatf("Top Banana - Test %0s has completed properly.", get_name()), UVM_NONE)

   endfunction : final_phase
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: apply_factory_overrides
   //
   // Apply any required overrides.
   // HINT: Tests may override this function for specific requirements but should call super.apply_factory_overrides().
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void apply_factory_overrides();
      const string  msg_id = { get_type_name(), ".apply_factory_overrides" };

   endfunction : apply_factory_overrides
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_ral
   //
   // Build the RAL model before creating the environment.
   // HINT: Tests may override this function for specific settings.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_ral();
      const string  msg_id = { get_type_name(), ".build_ral" };

      // HINT: If using RAL, uncomment and edit the following two lines:
      // HINT: m_regs = qeciphy_ral_pkg::qeciphy_reg_block::type_id::create("m_regs");
      // HINT: m_regs.build();

   endfunction : build_ral
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: configure_environment
   //
   // Initialize configuration object for the environment (object has already been created).
   // HINT: Tests may override this function for specific configurations.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void configure_environment();
      const string  msg_id = { get_type_name(), ".configure_environment" };
      int           rand_ok;

      rand_ok = m_env_config.randomize() with {
         m_dut_aclk_period_ns   == T_DFLT_DUT_ACLK_PERIOD_NS;
         m_dut_rclk_period_ns   == T_DFLT_DUT_RCLK_PERIOD_NS;
         m_dut_fclk_period_ns   == T_DFLT_DUT_FCLK_PERIOD_NS;
         m_tbphy_aclk_period_ns == T_DFLT_TBPHY_ACLK_PERIOD_NS;
         m_tbphy_rclk_period_ns == T_DFLT_TBPHY_RCLK_PERIOD_NS;
         m_tbphy_fclk_period_ns == T_DFLT_TBPHY_FCLK_PERIOD_NS;
      };
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize m_env_config")

      // Assign all VIFs by fetching them from the ConfigDB, effectively connecting to the top-level interfaces.
      if (! uvm_config_db#(virtual qeciphy_env_miscio_if)::get(uvm_root::get(), "", "miscio_vif", m_env_config.m_vifs.miscio_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'miscio_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::get(uvm_root::get(), "", "dut_aclk_vif", m_env_config.m_vifs.dut_aclk_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'dut_aclk_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::get(uvm_root::get(), "", "dut_rclk_vif", m_env_config.m_vifs.dut_rclk_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'dut_rclk_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::get(uvm_root::get(), "", "dut_fclk_vif", m_env_config.m_vifs.dut_fclk_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'dut_fclk_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_pbus_controller_agent_if)::get(uvm_root::get(), "", "dut_pbus_vif", m_env_config.m_vifs.dut_pbus_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'dut_pbus_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_rdy_vld_sink_agent_if)::get(uvm_root::get(), "", "dut_axis_rx_vif", m_env_config.m_vifs.dut_axis_rx_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'dut_axis_rx_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_rdy_vld_source_agent_if)::get(uvm_root::get(), "", "dut_axis_tx_vif", m_env_config.m_vifs.dut_axis_tx_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'dut_axis_tx_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::get(uvm_root::get(), "", "tbphy_aclk_vif", m_env_config.m_vifs.tbphy_aclk_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'tbphy_aclk_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::get(uvm_root::get(), "", "tbphy_rclk_vif", m_env_config.m_vifs.tbphy_rclk_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'tbphy_rclk_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_clk_rst_gen_vip_if)::get(uvm_root::get(), "", "tbphy_fclk_vif", m_env_config.m_vifs.tbphy_fclk_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'tbphy_fclk_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_pbus_controller_agent_if)::get(uvm_root::get(), "", "tbphy_pbus_vif", m_env_config.m_vifs.tbphy_pbus_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'tbphy_pbus_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_rdy_vld_sink_agent_if)::get(uvm_root::get(), "", "tbphy_axis_rx_vif", m_env_config.m_vifs.tbphy_axis_rx_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'tbphy_axis_rx_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_rdy_vld_source_agent_if)::get(uvm_root::get(), "", "tbphy_axis_tx_vif", m_env_config.m_vifs.tbphy_axis_tx_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'tbphy_axis_tx_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_diff_pair_connector_vip_if)::get(uvm_root::get(), "", "dut2tbphy_conn_vif", m_env_config.m_vifs.dut2tbphy_conn_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'dut2phy_conn_vif' in ConfigDB")
      end

      if (! uvm_config_db#(virtual riv_diff_pair_connector_vip_if)::get(uvm_root::get(), "", "tbphy2dut_conn_vif", m_env_config.m_vifs.tbphy2dut_conn_vif)) begin
         `uvm_fatal(msg_id, "Can't find 'tbphy2dut_conn_vif' in ConfigDB")
      end

   endfunction : configure_environment
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: process_command_line
   //
   // Process any command lines options that affect the environment.
   // Note that this is called after configure_environment() so will override any settings it created.
   // HINT: Tests may override this function for specific options but should call super.process_command_line().
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void process_command_line();
      const string  msg_id = { get_type_name(), ".process_command_line" };

   endfunction : process_command_line
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_config_db
   //
   // Build the ConfigDB before creating the environment.
   // HINT: Tests may override this function for specific settings but should call super.build_config_db().
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_config_db();
      const string  msg_id = { get_type_name(), ".build_config_db" };

      // Put environment's config object into the ConfigDB.
      uvm_config_db#(qeciphy_env_config)::set(this, "m_env*", "config", m_env_config);

      // Enable transaction recording for everything unless verbosity is NONE (allows for faster regressions).
      if (get_report_verbosity_level() > UVM_NONE) begin
         uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_FULL);
      end else begin
         uvm_config_db#(int)::set(this, "*", "recording_detail", UVM_NONE);
      end

   endfunction : build_config_db
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: build_environment
   //
   // Create the environment (environment config is valid at this point).
   // HINT: Tests may override this function for specific environments.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void build_environment();
      const string  msg_id = { get_type_name(), ".build_environment" };

      m_env = qeciphy_env::type_id::create("m_env", .parent(this));

   endfunction : build_environment
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: run_reset_sequence
   //
   // Run sequence to initialize TB. apply reset, start clocks running etc.
   // Tests may override this task to run their own reset_phase sequence, but this should be OK by default.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_reset_sequence();
      const string               msg_id = { get_type_name(), ".run_reset_sequence" };
      qeciphy_initialize_tb_seq  init_seq;
      qeciphy_power_down_seq     pwr_dn_seq;
      qeciphy_power_up_seq       pwr_up_seq;
      qeciphy_reset_seq          reset_seq;
      int                        rand_ok;

      init_seq = qeciphy_initialize_tb_seq::type_id::create("init_seq", .contxt(get_full_name()));
      rand_ok = init_seq.randomize();
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize init_seq")
      init_seq.start(m_env.m_sequencer);
      #100ns;

      pwr_dn_seq = qeciphy_power_down_seq::type_id::create("pwr_dn_seq", .contxt(get_full_name()));
      rand_ok = pwr_dn_seq.randomize();
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize pwr_dn_seq")
      pwr_dn_seq.start(m_env.m_sequencer);
      #100ns;

      pwr_up_seq = qeciphy_power_up_seq::type_id::create("pwr_up_seq", .contxt(get_full_name()));
      rand_ok = pwr_up_seq.randomize();
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize pwr_up_seq")
      pwr_up_seq.start(m_env.m_sequencer);
      #100ns;

      reset_seq = qeciphy_reset_seq::type_id::create("reset_seq", .contxt(get_full_name()));
      rand_ok = reset_seq.randomize();
      if (! rand_ok) `uvm_fatal(msg_id, "Failed to randomize reset_seq")
      reset_seq.start(m_env.m_sequencer);
      #100ns;

   endtask : run_reset_sequence
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Task: run_main_test_sequence
   //
   // HINT: Tests MUST override this task to run the test - this base-level task will cause a FATAL error if not overridden.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual task run_main_test_sequence();
      const string  msg_id = { get_type_name(), ".run_main_test_sequence" };

      `uvm_fatal(msg_id, "Tried to run base-test - tests must override the run_main_test_sequence() method");

   endtask : run_main_test_sequence
   //----------------------------------------------------------------------------------------------------------------------------------------


   //----------------------------------------------------------------------------------------------------------------------------------------
   // Function: finalize_test
   //
   // Perform any actions to finalize the test (wait for sequences/scoreboards to finish etc.).
   // HINT: Tests may override this function for specific settings.
   //----------------------------------------------------------------------------------------------------------------------------------------
   virtual function void finalize_test();
      const string  msg_id = { get_type_name(), ".finalize_test" };

      // HINT: Add code here or leave blank (to allow overriding in extending classes).

   endfunction : finalize_test
   //----------------------------------------------------------------------------------------------------------------------------------------


endclass : qeciphy_base_test
//------------------------------------------------------------------------------------------------------------------------------------------

`endif // QECIPHY_BASE_TEST_SVH_

