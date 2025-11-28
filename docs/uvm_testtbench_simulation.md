# UVM Testbench simulation using Xilinx and Synopsys tools
To run the UVM testbench there are 2 steps to be followed:
1. Geenrate simulation files for the required transciever (GTY or GTX or GTX). This is done using the following commands 
    * `module load xilinx/vivado`(to be run just once on a new terminal)
    * `make generate-xci OPT_PROFILE=<opt_profile> OPT_SIM_FILES=true`
    * OPT_PROFILE can be chosen from the table below 

      | OPT_PROFILE | Purpose | GT Types |
      |---------|---------|----------|
      | `kasliSoC` | qeciphy_clk_mmcm + qeciphy_gtx_transceiver | GTX (7-series) |
      | `zcu106` | GTH transceiver wrapper | GTH (UltraScale) |
      | `zcu216` | GTY transceiver wrapper | GTY (UltraScale+) |
2. Run any test on the UVM testbench using synopsys-vcs and Verdi(gui) using the follwing commands 
    * `module load synopsys/vcs`(to be run just once on a new terminal)
    * `module load synopsys/verdi`(to be run just once on a new terminal)
    * `make uvm_sim OPT_TOP=qeciphy_uvmtb OPT_TEST=<test_name> OPT_PROFILE=<profile>` 
    * To run with GUI - `make uvm_sim OPT_TOP=qeciphy_uvmtb OPT_TEST=<test_name> OPT_PROFILE=<profile> OPT_MODE=gui OPT_ARGS=<args>(optional)`

All test names and run time arguments can be found in uvm/regression_testlist.txt

 # Example run command on a new terminal
   module laod xilixn/verdi  
   make generate-xci OPT_PROFILE=zcu216 OPT_SIM_FILES=true  
   Once this command is run,it can be observed that `generate_sim.f` and `generated_sim_verilog_only.f` files are generated 

   module laod synopsys/vcs  
   module load synopsys/verdi  
   make uvm_sim OPT_TOP=qeciphy_uvmtb OPT_TEST=qeciphy_txrx_test OPT_PROFILE=zcu216 OPT_MODE=gui OPT_ARGS=+DUT_XFERS=20000 +TBPHY_XFERS=100  
   Note* - Always use `make distclean` before generating files for a different transciever.  


