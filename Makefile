# SPDX-License-Identifier: LicenseRef-LICENSE
# Copyright (c) 2025 Riverlane Ltd.

# -------------------------------------------------------------
# Global variables (only OPT_ are modifiable)
# -------------------------------------------------------------
OPT_MODE?=batch
OPT_PROFILE?=
OPT_SIM_FILES  ?= false
OPT_TOOL?=
OPT_TEST?=
OPT_ARGS?=0
OPT_SEED?=0

# -------------------------------------------------------------
# Utils
# -------------------------------------------------------------
CURRENT_DIR = $(shell pwd)
export CURRENT_DIR

# Disable automatic expansions/replacements
.SUFFIXES:

# -------------------------------------------------------------
# Configuration variables
# -------------------------------------------------------------
PY        ?= python3
CFG       ?= config.json

# Collect fields from config (require OPT_PROFILE)
SYN_TOP   := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).synth.top)
SYN_FILELIST := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).synth.filelists)
XDC       := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).synth.constraints)
PART      := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).device.part)
VENDOR    := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).device.vendor)
BOARD     := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).board 2>/dev/null || true)
VARIANT   := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).variant)
HOOKS     := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).synth.pre_setup_hooks)

# Clock frequencies 
FCLK_FREQ        := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).fclk_freq 2>/dev/null || echo "")
RCLK_FREQ        := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).rclk_freq 2>/dev/null || echo "")

# Transceiver configuration variables
GT_LOC           := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).transceiver.gt_loc 2>/dev/null || echo "")
RX_RCLK_SRC      := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).transceiver.rx_rclk_src 2>/dev/null || echo "")
TX_RCLK_SRC      := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).transceiver.tx_rclk_src 2>/dev/null || echo "")
LINE_RATE_GBPS   := $(shell $(PY) scripts/read_cfg.py $(CFG) profiles.$(OPT_PROFILE).transceiver.line_rate_gbps 2>/dev/null || echo "")

# Static file lists
SIM_FILELIST := sim.f
LINT_FILELIST := lint.f
SRC_FILELIST := src.f
XCI_FILELIST := xci.f
UVM_FILELIST := uvm.f

# Extracted file lists
LINT_FILES := $(shell $(PY) scripts/extract_sources.py $(SRC_FILELIST) $(LINT_FILELIST))
SRC_FILES := $(shell $(PY) scripts/extract_sources.py $(SRC_FILELIST))
SIM_FILES := $(shell $(PY) scripts/extract_sources.py $(SIM_FILELIST))
SYN_FILES := $(shell $(PY) scripts/extract_sources.py $(SYN_FILELIST))
XCI_FILES := $(shell if [ -f $(XCI_FILELIST) ]; then $(PY) scripts/extract_sources.py $(XCI_FILELIST); fi)

# Tool paths and directories
XCI_DIR := xci
RUN_DIR := run
GEN_XCI_TCL_gth := vendors/xilinx/qeciphy_gth_transceiver.tcl
GEN_XCI_TCL_gtx := vendors/xilinx/qeciphy_gtx_transceiver.tcl
GEN_XCI_TCL_gtx_mmcm := vendors/xilinx/qeciphy_clk_mmcm.tcl
GEN_XCI_TCL_gty := vendors/xilinx/qeciphy_gty_transceiver.tcl
XSIM_TCL := scripts/vivado_sim.tcl
VIVADO_SYNTH_TCL := scripts/vivado_synth.tcl
VIVADO_SIM_EXPORT_TCL := scripts/vivado_sim_export.tcl

# -------------------------------------------------------------
# Targets
# -------------------------------------------------------------
.PHONY: help lint synth sim generate-xci format clean distclean uvm-sim

.DEFAULT_GOAL := help

help:
	@echo "Usage: make <target> [VARIABLES...]"
	@echo ""
	@echo "Available Targets:"
	@echo "----------------"
	@echo "  lint"
	@echo "    - Run lint checks on the design using Verilator"
	@echo ""
	@echo "  synth"
	@echo "    - Run design synthesis and implementation using Vivado"
	@echo "    - Required variables: OPT_PROFILE"
	@echo "    - Optional variables: OPT_MODE=(gui|batch) [default: batch]"
	@echo ""
	@echo "  sim"
	@echo "    - Run simulation using XSim (default) or VCS"
	@echo "    - Required variables: OPT_PROFILE"
	@echo "    - Optional variables: OPT_TOOL=(xsim|vcs)"
	@echo "    - Optional variables: OPT_MODE=(gui|batch) [default: batch]"
	@echo ""
	@echo "  uvm-sim"
	@echo "    - Run UVM-based simulation."
	@echo "    - Required variables: OPT_TEST"
	@echo "    - Required variables: OPT_PROFILE"
	@echo "    - Optional variables: OPT_MODE=(gui|batch|cov) [default: batch]"
	@echo "    - Optional variables: OPT_SEED=(integer) [for randomization]"
	@echo "    - Optional variables: OPT_ARGS=(string) [additional simulator arguments]"
	@echo ""
	@echo "  generate-xci"
	@echo "    - Generate Xilinx IP core files (.xci) for the target profile"
	@echo "    - Required variables: OPT_PROFILE"
	@echo "    - Optional variables: OPT_SIM_FILES=(true|false) [default: false]"
	@echo "      When OPT_SIM_FILES=true, also exports simulation files to tb/generated_sim_files/"
	@echo ""
	@echo "  format"
	@echo "    - Format SystemVerilog source code using Verible"
	@echo ""
	@echo "  clean"
	@echo "    - Clean up build artifacts and temporary files"
	@echo ""
	@echo "  distclean"
	@echo "    - Perform deep clean (includes clean + removes all generated files)"
	@echo ""
	@echo "Examples:"
	@echo "--------"
	@echo "  make clean"
	@echo "  make distclean"
	@echo "  make generate-xci OPT_PROFILE=zcu216"
	@echo "  make generate-xci OPT_PROFILE=zcu216 OPT_SIM_FILES=true"
	@echo "  make synth OPT_PROFILE=zcu216"
	@echo "  make sim OPT_PROFILE=zcu216 OPT_TOOL=vcs"
	@echo "  make sim OPT_PROFILE=zcu216 OPT_MODE=gui OPT_TOOL=vcs"
	@echo "  make lint"
	@echo "  make format"
	@echo "  make uvm-sim OPT_TEST=qeciphy_txrx_test OPT_PROFILE=zcu216" 
	@echo "  make uvm-sim OPT_TEST=qeciphy_txrx_test OPT_PROFILE=zcu216 OPT_MODE=gui" 
	@echo "  make uvm-sim OPT_TEST=qeciphy_txrx_test OPT_PROFILE=zcu216 OPT_MODE=cov" 
	@echo "  make uvm-sim OPT_TEST=qeciphy_txrx_test OPT_PROFILE=zcu216 OPT_MODE=gui OPT_ARGS=+DUT_XFERS=20000"
# -------------------------------------------------------------
# Profile validation
# -------------------------------------------------------------
AVAILABLE_PROFILES := $(shell $(PY) -c "import json; config=json.load(open('$(CFG)')); print(' '.join(config['profiles'].keys()))" 2>/dev/null || echo "")

check_profile:
ifeq ($(OPT_PROFILE),)
	@echo "ERROR: OPT_PROFILE is required but not specified."
	@echo "Available profiles: $(AVAILABLE_PROFILES)"
	@echo "Usage: make <target> OPT_PROFILE=<profile>"
	@exit 1
endif
	@echo "$(AVAILABLE_PROFILES)" | grep -q "$(OPT_PROFILE)" || { \
		echo "ERROR: Profile '$(OPT_PROFILE)' not found in $(CFG)"; \
		echo "Available profiles: $(AVAILABLE_PROFILES)"; \
		exit 1; \
	}

# -------------------------------------------------------------
# Simulator validation
# -------------------------------------------------------------
check_simulator:
	@if [ "$(OPT_TOOL)" != "xsim" ] && [ "$(OPT_TOOL)" != "vcs" ]; then \
		echo "ERROR: Unsupported simulator '$(OPT_TOOL)'. Supported: xsim, vcs"; \
		exit 1; \
	fi

# -------------------------------------------------------------
# GT type detection function
# -------------------------------------------------------------
get_gt_type = $(shell \
	if [ "$(OPT_PROFILE)" = "kasliSoC" ]; then echo "GTX"; \
	elif [ "$(OPT_PROFILE)" = "zcu106" ]; then echo "GTH"; \
	elif [ "$(OPT_PROFILE)" = "zcu216" ]; then echo "GTY"; \
	else echo "GTY"; fi)

# -------------------------------------------------------------
# Tool availability checks
# -------------------------------------------------------------
check_vivado:
	@if ! command -v vivado >/dev/null 2>&1; then \
		echo "ERROR: Vivado not found in PATH. Please ensure Vivado is installed and available."; \
		exit 1; \
	fi

check_vcs:
	@if ! command -v vcs >/dev/null 2>&1; then \
		echo "ERROR: VCS not found in PATH. Please ensure VCS is installed and available."; \
		exit 1; \
	fi

check_verilator:
	@if ! command -v verilator >/dev/null 2>&1; then \
		echo "ERROR: Verilator not found in PATH. Please install Verilator for linting."; \
		echo "       See: https://verilator.org/guide/latest/install.html"; \
		exit 1; \
	fi

check_verible:
	@if ! command -v verible-verilog-format >/dev/null 2>&1; then \
		echo "ERROR: Verible not found in PATH. Please install Verible for formatting."; \
		echo "       See: https://github.com/chipsalliance/verible"; \
		exit 1; \
	fi

# -------------------------------------------------------------
# Main targets
# -------------------------------------------------------------
format:
	@echo "INFO: Formatting with Verible"
	@$(MAKE) verible_format

lint:
	@echo "INFO: Linting with Verilator"
	@$(MAKE) verilator_lint

generate-xci:
	@$(MAKE) check_profile
	@echo "INFO: Generating XCI files for profile $(OPT_PROFILE)"
	@$(MAKE) vivado_generate_xci

sim:
	@$(MAKE) check_profile
	@$(MAKE) check_simulator
	@echo "INFO: Running simulation for profile $(OPT_PROFILE) using $(OPT_TOOL)"
	@if [ "$(OPT_TOOL)" = "vcs" ]; then \
		$(MAKE) vcs_sim; \
	else \
		$(MAKE) vivado_sim; \
	fi

synth: 
	@$(MAKE) check_profile
	@echo "INFO: Running synthesis for profile $(OPT_PROFILE)"
	@$(MAKE) vivado_synth

clean:
	@echo "INFO: Cleaning build artifacts"
	@rm -rf .Xil/ vivado* *.log run/ scripts/__pycache__/ simv synopsys_sim.setup simv.daidir/ csrc/ ucli.key verdi_config_file

distclean: clean
	@echo "INFO: Performing distclean"
	@rm -rf tb/compiled_simlib/ tb/generated_sim_files/ generated_sim.f xci/ xci.f 


# -------------------------------------------------------------
# Tool implementations
# -------------------------------------------------------------

verilator_lint:
	@$(MAKE) check_verilator
	@verilator --lint-only -sv -Isrc $(LINT_FILES) lint_waivers.vlt --top QECIPHY
	
verible_format:
	@$(MAKE) check_verible
	@files=$$(find . -type f \( -name "*.sv" -o -name "*.v" \) -not -path "./uvm/*" -not -path "./verif_vip/*" -not -path "./run/*"); \
	if [ -n "$$files" ]; then \
		verible-verilog-format --inplace --column_limit 200 --indentation_spaces 3 $$files; \
	else \
		echo "No .sv or .v files found."; \
	fi

vivado_generate_xci:
	@$(MAKE) check_vivado
	@mkdir -p $(XCI_DIR)
	@mkdir -p $(RUN_DIR)
	@if [ "$(VARIANT)" = "GTH" ]; then \
		vivado -mode batch -source $(GEN_XCI_TCL_gth) -tclargs $(PART) $(RUN_DIR) "$(GT_LOC)" "$(FCLK_FREQ)" "$(RCLK_FREQ)" "$(RX_RCLK_SRC)" "$(TX_RCLK_SRC)" "$(LINE_RATE_GBPS)"; \
		find $(RUN_DIR) -name "*.xci" -exec cp {} $(XCI_DIR)/ \; ; \
		echo "INFO: Copied .xci files from $(RUN_DIR) to $(XCI_DIR)"; \
	elif [ "$(VARIANT)" = "GTX" ]; then \
		vivado -mode batch -source $(GEN_XCI_TCL_gtx) -tclargs $(PART) $(RUN_DIR) "$(GT_LOC)" "$(FCLK_FREQ)" "$(RCLK_FREQ)" "$(RX_RCLK_SRC)" "$(TX_RCLK_SRC)" "$(LINE_RATE_GBPS)"; \
		find $(RUN_DIR) -name "*.xci" -exec cp {} $(XCI_DIR)/ \; ; \
		vivado -mode batch -source $(GEN_XCI_TCL_gtx_mmcm) -tclargs $(PART) $(RUN_DIR) "$(LINE_RATE_GBPS)"; \
		find $(RUN_DIR) -name "*.xci" -exec cp {} $(XCI_DIR)/ \; ; \
		echo "INFO: Copied .xci files from $(RUN_DIR) to $(XCI_DIR)"; \
	elif [ "$(VARIANT)" = "GTY" ]; then \
		vivado -mode batch -source $(GEN_XCI_TCL_gty) -tclargs $(PART) $(RUN_DIR) "$(GT_LOC)" "$(FCLK_FREQ)" "$(RCLK_FREQ)" "$(RX_RCLK_SRC)" "$(TX_RCLK_SRC)" "$(LINE_RATE_GBPS)"; \
		find $(RUN_DIR) -name "*.xci" -exec cp {} $(XCI_DIR)/ \; ; \
		echo "INFO: Copied .xci files from $(RUN_DIR) to $(XCI_DIR)"; \
	else \
		echo "ERROR: Unsupported variant $(VARIANT). Must be one of GTH, GTX, GTY."; \
		exit 1; \
	fi
	@echo "INFO: Generating XCI filelist"
	@find $(XCI_DIR) -name "*.xci" | sort > xci.f
	@echo "INFO: Created xci.f with $$(wc -l < xci.f) XCI files"
ifeq ($(OPT_SIM_FILES),true)
	@echo "INFO: Generating IP simulation files"
	@$(PY) scripts/generate_sim_files.py --part $(PART) --simulator vcs
endif
	@echo "INFO: Cleaning up temporary project files in $(RUN_DIR)"
	@rm -rf $(RUN_DIR)

vivado_sim:
	@$(MAKE) check_vivado
	@mkdir -p $(RUN_DIR)
	@vivado -mode $(OPT_MODE) -source $(XSIM_TCL) -tclargs qeciphy_tb $(PART) $(VARIANT) $(SRC_FILES) -- $(SIM_FILES) -- $(XCI_FILES)

vcs_sim:
	@$(MAKE) check_vcs
	@export XILINX_VIVADO=$$(dirname `dirname \`which vivado\``) && \
	echo "INFO: Using XILINX_VIVADO=$$XILINX_VIVADO" && \
	echo "INFO: Filtering out VHDL files from generated simulation files" && \
	grep -v "\.vhd$$" generated_sim.f > generated_sim_verilog_only.f && \
	GT_TYPE_DEF="$(get_gt_type)" && \
	echo "INFO: Using GT_TYPE=$$GT_TYPE_DEF for profile $(OPT_PROFILE)" && \
	echo "INFO: Compiling design + IP + Xilinx GT/clock primitives + SecureIP into VCS" && \
	vcs -full64 -sverilog -timescale=1ps/1ps +define+WAVES_FSDB +define+WAVES=\"fsdb\"  \
	+plusarg_save -debug_access+r -debug_region=cell+encrypt -kdb \
		+v2k +define+VCS +define+GT_TYPE=\"$$GT_TYPE_DEF\" +libext+.v+.sv+.vp \
		-work work \
		+incdir+src \
		-y $$XILINX_VIVADO/data/verilog/src/unisims \
		-y $$XILINX_VIVADO/data/verilog/src/retarget \
		-f $$XILINX_VIVADO/data/secureip/secureip_cell.list.f \
		$$XILINX_VIVADO/data/verilog/src/glbl.v \
		-file generated_sim_verilog_only.f \
		$(SRC_FILES) \
		$(SIM_FILES) \
		-top qeciphy_tb \
		+nospecify +notimingchecks \
		-o simv && \
		rm generated_sim_verilog_only.f && \
	echo "INFO: Running VCS simulation in $(OPT_MODE) mode" && \
	if [ "$(OPT_MODE)" = "gui" ]; then \
		./simv -gui; \
	else \
		./simv; \
	fi
uvm-vcs-compile-sim:
	@export XILINX_VIVADO=$$(dirname `dirname \`which vivado\``) && \
    echo "INFO: Running uvm simulation" \
    echo "INFO: Using XILINX_VIVADO=$$XILINX_VIVADO" && \
    echo "INFO: Filtering out VHDL files from generated simulation files" && \
    grep -v "\.vhd$$" generated_sim.f > generated_sim_verilog_only.f && \
    GT_TYPE_DEF="$(get_gt_type)" && \
    echo "INFO: Using GT_TYPE=$$GT_TYPE_DEF for profile $(OPT_PROFILE)" && \
    echo "INFO: Compiling design + IP + Xilinx GT/clock primitives + SecureIP into VCS" && \
   vcs -full64 -ntb_opts uvm -sverilog +systemverilogext+2017 -quiet -xlrm floating_pnt_constraint \
	+define+SYNOPSYS_SV +define+UVM_DISABLE_AUTO_ITEM_RECORDING +lint=TFIPC-L -sv_net_ports -sverilog \
	-timescale=1ps/1ps +define+WAVES_FSDB +define+WAVES=\"fsdb\" +plusarg_save -debug_access+r -debug_region=cell+encrypt \
	-cm_libs yv+celldefine -cm line+cond+tgl+fsm+branch+assert  \
	+define+GT_TYPE=\"$$GT_TYPE_DEF\" -kdb -top WORK.qeciphy_uvmtb -top glbl \
   	+v2k +define+VCS +libext+.v+.sv+.vp -ignore initializer_driver_checks \
	-work work \
   	+incdir+src \
	-F $(UVM_FILELIST) \
   	-y $$XILINX_VIVADO/data/verilog/src/unisims \
   	-y $$XILINX_VIVADO/data/verilog/src/retarget \
   	-f $$XILINX_VIVADO/data/secureip/secureip_cell.list.f \
   	$$XILINX_VIVADO/data/verilog/src/glbl.v \
   	-file generated_sim_verilog_only.f \
   	$(SRC_FILES) \
   	-top glbl

uvm-sim:
	@$(MAKE) check_vcs
   ifeq ($(OPT_MODE), gui)
	@$(MAKE) uvm-vcs-compile-sim
   ./simv $(OPT_ARGS) -gui=verdi  +UVM_VERBOSITY=UVM_LOW +UVM_TESTNAME=$(OPT_TEST) -l ${OPT_TEST}.log +ntb_random_seed=$(OPT_SEED)
   rm generated_sim_verilog_only.f
   else ifeq ($(OPT_MODE),cov)
	@$(MAKE) uvm-vcs-compile-sim
	./simv $(OPT_ARGS) +UVM_VERBOSITY=UVM_LOW +UVM_TESTNAME=$(OPT_TEST) -l uvm_regression_logs/${OPT_TEST}_${OPT_SEED}_${OPT_PROFILE}.log +ntb_random_seed=$(OPT_SEED) -cm line+cond+tgl+fsm+branch+assert +enable_coverage=1 -cm_dir coverage/$(OPT_TEST)_$(OPT_SEED)__${OPT_PROFILE}_cov.vdb
	rm generated_sim_verilog_only.f
   else
	@$(MAKE) uvm-vcs-compile-sim
	./simv $(OPT_ARGS) +UVM_VERBOSITY=UVM_LOW +UVM_TESTNAME=$(OPT_TEST) -l ${OPT_TEST}.log +ntb_random_seed=$(OPT_SEED) 
	rm generated_sim_verilog_only.f
   endif
 

vivado_synth:
	@$(MAKE) check_vivado
	@mkdir -p $(RUN_DIR)
	@vivado -mode $(OPT_MODE) -source $(VIVADO_SYNTH_TCL) -tclargs $(SYN_TOP) $(XDC) $(PART) "$(BOARD)" '$(HOOKS)' $(SYN_FILES) -- $(XCI_FILES)