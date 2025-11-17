# SPDX-License-Identifier: LicenseRef-LICENSE
# Copyright (c) 2025 Riverlane Ltd.

# -------------------------------------------------------------
# Global variables (only OPT_ are modifiable)
# -------------------------------------------------------------
OPT_MODE?=batch
OPT_PROFILE?=
OPT_SIM_FILES  ?= false
OPT_SIMULATOR  ?= xsim

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

# Static file lists
SIM_FILELIST := sim.f
LINT_FILELIST := lint.f
SRC_FILELIST := src.f
XCI_FILELIST := xci.f

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
.PHONY: help check_profile lint synth sim generate-xci vcs_sim format clean distclean

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
	@echo "    - Run simulation using Vivado XSim"
	@echo "    - Required variables: OPT_PROFILE"
	@echo "    - Optional variables: OPT_MODE=(gui|batch) [default: batch]"
	@echo ""
	@echo "  generate-xci"
	@echo "    - Generate Xilinx IP core files (.xci) for the target profile"
	@echo "    - Required variables: OPT_PROFILE"
	@echo "    - Optional variables: OPT_SIM_FILES=(true|false) [default: false]"
	@echo "      When OPT_SIM_FILES=true, also exports simulation files to tb/generated_sim_files/"
	@echo ""
	@echo "  compile-simlib"
	@echo "    - Compile Xilinx simulation libraries for the specified simulator"
	@echo "    - Optional variables: OPT_SIMULATOR=(xsim|vcs) [default: xsim]"
	@echo "    - Libraries are compiled to tb/compiled_simlib/"
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
	@echo "  make compile-simlib OPT_SIMULATOR=xsim"
	@echo "  make synth OPT_PROFILE=zcu216"
	@echo "  make sim OPT_PROFILE=zcu216"
	@echo "  make lint"
	@echo "  make format"

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
	@if [ "$(OPT_SIMULATOR)" != "xsim" ] && [ "$(OPT_SIMULATOR)" != "vcs" ]; then \
		echo "ERROR: Unsupported simulator '$(OPT_SIMULATOR)'. Supported: xsim, vcs"; \
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

compile-simlib:
	@$(MAKE) check_simulator
	@echo "INFO: Compiling simulation libraries for $(OPT_SIMULATOR)"
	@if [ "$(OPT_SIMULATOR)" = "xsim" ]; then \
		echo "INFO: XSim uses built-in simulation libraries - nothing to compile"; \
	else \
		$(MAKE) vivado_compile_simlib; \
	fi

sim:
	@$(MAKE) check_profile
	@$(MAKE) check_simulator
	@echo "INFO: Running simulation for profile $(OPT_PROFILE) using $(OPT_SIMULATOR)"
	@if [ "$(OPT_SIMULATOR)" = "vcs" ]; then \
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
	@rm -rf .Xil/ vivado* *.log run/ scripts/__pycache__/ simv synopsys_sim.setup simv.daidir/ csrc/ ucli.key

distclean: clean
	@echo "INFO: Performing distclean"
	@rm -rf tb/compiled_simlib/ tb/generated_sim_files/ generated_sim.f xci/ xci.f

# -------------------------------------------------------------
# Tool implementations
# -------------------------------------------------------------

verilator_lint:
	@verilator --lint-only -sv -Isrc $(LINT_FILES) lint_waivers.vlt --top QECIPHY
	
verible_format:
	@files=$$(find . -type f \( -name "*.sv" -o -name "*.v" \)); \
	if [ -n "$$files" ]; then \
		verible-verilog-format --inplace --column_limit 200 --indentation_spaces 3 $$files; \
	else \
		echo "No .sv or .v files found."; \
	fi

vivado_generate_xci:
	@mkdir -p $(XCI_DIR)
	@mkdir -p $(RUN_DIR)
	@if [ "$(VARIANT)" = "GTH" ]; then \
		vivado -mode batch -source $(GEN_XCI_TCL_gth) -tclargs $(PART) $(RUN_DIR) "$(GT_LOC)" "$(FCLK_FREQ)" "$(RCLK_FREQ)" "$(RX_RCLK_SRC)" "$(TX_RCLK_SRC)"; \
		find $(RUN_DIR) -name "*.xci" -exec cp {} $(XCI_DIR)/ \; ; \
		echo "INFO: Copied .xci files from $(RUN_DIR) to $(XCI_DIR)"; \
	elif [ "$(VARIANT)" = "GTX" ]; then \
		vivado -mode batch -source $(GEN_XCI_TCL_gtx) -tclargs $(PART) $(RUN_DIR) "$(GT_LOC)" "$(FCLK_FREQ)" "$(RCLK_FREQ)" "$(RX_RCLK_SRC)" "$(TX_RCLK_SRC)"; \
		find $(RUN_DIR) -name "*.xci" -exec cp {} $(XCI_DIR)/ \; ; \
		vivado -mode batch -source $(GEN_XCI_TCL_gtx_mmcm) -tclargs $(PART) $(RUN_DIR); \
		find $(RUN_DIR) -name "*.xci" -exec cp {} $(XCI_DIR)/ \; ; \
		echo "INFO: Copied .xci files from $(RUN_DIR) to $(XCI_DIR)"; \
	elif [ "$(VARIANT)" = "GTY" ]; then \
		vivado -mode batch -source $(GEN_XCI_TCL_gty) -tclargs $(PART) $(RUN_DIR) "$(GT_LOC)" "$(FCLK_FREQ)" "$(RCLK_FREQ)" "$(RX_RCLK_SRC)" "$(TX_RCLK_SRC)"; \
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
	@mkdir -p $(RUN_DIR)
	@vivado -mode $(OPT_MODE) -source $(XSIM_TCL) -tclargs qeciphy_tb $(PART) $(VARIANT) $(SRC_FILES) -- $(SIM_FILES) -- $(XCI_FILES)

vcs_sim:
	@export XILINX_VIVADO=$$(dirname `dirname \`which vivado\``) && \
	echo "INFO: Using XILINX_VIVADO=$$XILINX_VIVADO" && \
	echo "INFO: Compiling design + IP + Xilinx GT/clock primitives + SecureIP into VCS" && \
	vcs -full64 -sverilog -timescale=1ns/1ps \
		+v2k +define+VCS +libext+.v+.sv+.vp \
		-work work \
		+incdir+src \
		$$XILINX_VIVADO/data/verilog/src/unisims/GTYE4_CHANNEL.v \
		$$XILINX_VIVADO/data/verilog/src/unisims/GTYE4_COMMON.v \
		$$XILINX_VIVADO/data/verilog/src/unisims/IBUFDS_GTE4.v \
		$$XILINX_VIVADO/data/verilog/src/unisims/BUFG_GT.v \
		-f $$XILINX_VIVADO/data/secureip/secureip_cell.list.f \
		$$XILINX_VIVADO/data/verilog/src/glbl.v \
		-file generated_sim.f \
		$(SRC_FILES) \
		$(SIM_FILES) \
		-top qeciphy_tb \
		+nospecify +notimingchecks \
		-o simv && \
	echo "INFO: Running VCS simulation in $(OPT_MODE) mode" && \
	if [ "$(OPT_MODE)" = "gui" ]; then \
		./simv -gui; \
	else \
		./simv; \
	fi

vivado_synth:
	@mkdir -p $(RUN_DIR)
	@vivado -mode $(OPT_MODE) -source $(VIVADO_SYNTH_TCL) -tclargs $(SYN_TOP) $(XDC) $(PART) "$(BOARD)" '$(HOOKS)' $(SYN_FILES) -- $(XCI_FILES)