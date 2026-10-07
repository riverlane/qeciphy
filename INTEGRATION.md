# QECIPHY Integration Guide

This document provides detailed instructions for integrating QECIPHY into your FPGA design. If you haven't already, please read the [README.md](README.md) for an overview of QECIPHY's features and capabilities. If you are interested in the architecture of QECIPHY, please refer to the [architecture](docs/architecture.md) document.

## Table of Contents

1. [Integration Overview](#integration-overview)
2. [Prerequisites](#prerequisites)
3. [Step-by-Step Integration](#step-by-step-integration)
4. [Timing Constraints](#timing-constraints)
5. [Data Path Integration Examples](#data-path-integration-examples)
6. [Interface Details](#interface-details)
7. [Support](#support)

## Integration Overview

QECIPHY provides a simple AXI4-Stream interface that abstracts away all physical layer complexity. The integration process involves:

1. **Platform Configuration**: Set up your hardware profile and generate IP dependencies
2. **HDL Instantiation**: Instantiate the QECIPHY module (or QECIPHY_QUAD, for several lanes in one transceiver quad) directly in your SystemVerilog design
3. **Interface Connection**: Connect AXI4-Stream interfaces to your application logic
4. **Status Monitoring**: Implement link status monitoring and error handling
5. **Constraint Application**: Apply provided timing constraints

## Prerequisites

### Hardware Requirements

- Xilinx FPGA with GTX, GTH, or GTY transceivers, or Altera FPGA with E-Tile or F-Tile transceivers
- Appropriate reference clock source
- Differential signal routing between FPGAs

### Software Requirements

- Vivado 2024.1 or later (Xilinx profiles)
- Quartus Prime Pro 25.3.1 (Altera profiles)
- Python 3.8+ (for build scripts)
- Make (for build automation)

## Step-by-Step Integration

### Step 1: Clone and Setup Repository

```bash
# Clone the repository
git clone https://github.com/riverlane/qeciphy.git
cd qeciphy

# Create a branch for your integration
git checkout -b integration-<your-platform>
```

### Step 2: Configure Your Platform Profile

Check if your hardware platform matches one of the existing profiles in `config.json`:

- **zcu216**: Zynq UltraScale+ with GTY transceivers
- **zcu111_quad**: Zynq UltraScale+ RFSoC with 4 GTY lanes in one quad via `QECIPHY_QUAD`
- **zcu106**: Zynq UltraScale with GTH transceivers  
- **kasliSoC**: 7-series with GTX transceivers
- **de10**: Agilex 7 with E-Tile transceiver
- **agilex7**: Agilex 7 I-Series Development Kit with F-Tile transceiver

If your platform is not listed, create a new profile in `config.json`. Examples for both vendors:

**Xilinx (GTY example):**
```json
{
  "profiles": {
    "your-platform": {
      "device": {
        "part": "xczu49dr-ffvf1760-2-e",
        "vendor": "xilinx"
      },
      "board": "xilinx.com:zcu216:part0:2.0",
      "variant": "GTY",
      "fclk_freq": "156.25",
      "rclk_freq": "156.25",
      "transceiver": {
        "gt_loc": "X0Y8",
        "rx_rclk_src": "X0Y8 clk1+2",
        "tx_rclk_src": "X0Y8 clk1+2",
        "line_rate_gbps": "12.5"
      },
      "synth": {
        "top": "qeciphy_syn_wrapper",
        "filelists": [
          "example_designs/<your-platform>/src.f"
        ],
        "constraints": [
          "example_designs/<your-platform>/syn/constraints.xdc"
        ]
      }
    }
  }
}
```

**Altera (E-Tile example):**
```json
{
  "profiles": {
    "your-platform": {
      "device": {
        "part": "AGFB014R24B2E2V",
        "vendor": "altera",
        "family": "Agilex 7"
      },
      "variant": "ETILE",
      "rclk_freq": "156.25",
      "transceiver": {
        "line_rate_gbps": "10.3125"
      },
      "synth": {
        "top": "qeciphy_syn_wrapper",
        "filelists": [
          "example_designs/<your-platform>/src.f"
        ],
        "constraints": [
          "example_designs/<your-platform>/syn/project_settings.tcl",
          "example_designs/<your-platform>/syn/clock_constraints.sdc",
          "example_designs/<your-platform>/syn/pin_assignments.tcl"
        ]
      }
    }
  }
}
```

**Profile Parameters:**
- `device.part`: Your FPGA part number
- `device.family`: Device family (Altera only)
- `board`: Xilinx board file (optional)
- `variant`: Transceiver type (`GTX`/`GTH`/`GTY`/`ETILE`/`FTILE`)
- `fclk_freq`: Transceiver DRP clock frequency in MHz (Xilinx only)
- `rclk_freq`: Transceiver reference clock frequency in MHz
- `transceiver.gt_loc`: Transceiver location (e.g., "X0Y8") (Xilinx only)
- `transceiver.rx_rclk_src`: RX reference clock source (e.g., "X0Y8 clk1+2" means using refclock 1 from the GT quad located 2 quads above X0Y8) (Xilinx only)
- `transceiver.tx_rclk_src`: TX reference clock source (same format as RX) (Xilinx only)
- `transceiver.line_rate_gbps`: Transceiver line rate in Gbps (e.g., "10.3125")
- `transceiver.gt_common`: GT COMMON (QPLL0) placement, `GTY`/`GTH` only (default `"internal"` if omitted):
  - `"internal"`: GT COMMON is embedded in this lane's GTWizard core (`LOCATE_COMMON=CORE`), so each
    `QECIPHY` instance is fully self-contained. Two lanes built this way cannot share a physical GT quad
    (each core reserves the quad's single COMMON hard block for itself).
  - `"external"`: GT COMMON is excluded from this lane's GTWizard core (`LOCATE_COMMON=EXAMPLE_DESIGN`).
    `QECIPHY` gains four extra top-level ports - `GT_QPLL_CLK`/`GT_QPLL_REFCLK`/`GT_QPLL_LOCK` (inputs) and
    `GT_QPLL_RESET` (output) - guarded by the `` `QECIPHY_GT_COMMON_EXTERNAL `` macro (set automatically by
    `make render-design` via the generated `src/qeciphy_build_cfg_pkg.sv`). Use this when multiple lanes need
    to share one quad, via `QECIPHY_QUAD` (see [Multiple Lanes in One Quad](#multiple-lanes-in-one-quad-qeciphy_quad)),
    which instantiates one `qeciphy_gty_common`/`qeciphy_gth_common` and wires every lane to it. If you
    instantiate `QECIPHY` directly in an `"external"` build, you must drive its `GT_QPLL_*` ports yourself.
    All lanes sharing a COMMON must be built from the same generated GTWizard core config (same line
    rate/refclk source), since they share one physical QPLL0.
    - The COMMON's attributes (QPLL0 PLL settings, `QPLL0CLKOUT_RATE`, bias, PPF, SDM) are extracted by
      `make render-design` from the wizard's own generated COMMON wrapper for this profile into
      `src/qeciphy_gty_common_attrs.svh`/`src/qeciphy_gth_common_attrs.svh`. The primitive's defaults are
      not valid - e.g. its default `QPLL0CLKOUT_RATE` runs the lanes at twice their line rate - and the
      correct values vary by part/speed grade, so always re-run `render-design` after changing the profile.
    - The shared QPLL0 is reset at power-up and when every lane's `ARSTn` is asserted together, but never
      by one lane's reset alone. The wizard's reset helper doesn't recover if its PLL loses lock after its
      sequence finishes, so if you drive the COMMON yourself, don't simply OR the lanes' `GT_QPLL_RESET`
      requests - that lets resetting any one lane permanently break the rest.
    - Set `transceiver.shared_channel_core` to `"true"` when the same channel-only core is instantiated more
      than once and relocated per lane with `LOC` constraints in your XDC; `make synth` then disables the
      core's own scoped constraints, which would otherwise pin every instance to the customized `gt_loc`.
- `synth`: Synthesis configuration (optional, for standalone testing)
- `pre_setup_hooks` Lists IP (`.tcl`) scripts run at synthesis time to generate board-level IPs (VIO probes, ILAs, etc.). Leave empty if no such IPs are needed.

**Vendor-Specific Notes (Important):**
- Xilinx profiles (`GTX`/`GTH`/`GTY`) require `fclk_freq`, `transceiver.gt_loc`, and Xilinx-oriented `rx_rclk_src`/`tx_rclk_src` values.
- Altera `ETILE` and `FTILE` profiles may differ by design:
  - `device.family` is required (for example `"Agilex 7"`).
  - `fclk_freq` should be omitted
  - `transceiver.gt_loc` should be omitted

**Important:** Refer to your FPGA documentation for correct GT site assignments and available reference clock sources for your specific device and board.

### Step 3: Generate Platform-Specific IP

```bash
# Render design for your platform (generates vendor specific IP cores and configs)
make render-design OPT_PROFILE=<your-profile>
```

This generates transceiver IP cores and package files configured for your hardware platform.

### Step 4: (Optional) Create Standalone Test Design

For quick platform validation, create a standalone example design:

1. **Create Platform Example**:
   ```bash
   mkdir -p example_designs/<your-platform>
   cd example_designs/<your-platform>
   ```

2. **Create Top-Level and Constraints**:
   Learn from existing example designs (`zcu106/`, `zcu216/`) to create:
   - Top-level module that instantiates QECIPHY
   - XDC constraint file with pin assignments and timing

   **Example Designs Folder Structure (Xilinx):**
   ```
   example_designs/<your-platform>/
   ├── src/
   │   └── qeciphy_syn_wrapper.sv    # Top-level wrapper module
   ├── src.f                         # Source file list
   └── syn/
       └── constraints.xdc           # XDC timing and pin constraints
   ```

   **Example Designs Folder Structure (Altera):**
   ```
   example_designs/<your-platform>/
   ├── src/
   │   └── qeciphy_syn_wrapper.sv    # Top-level wrapper module
   ├── src.f                         # Source file list
   └── syn/
       ├── project_settings.tcl      # Quartus project/device settings
       ├── clock_constraints.sdc     # SDC timing constraints
       └── pin_assignments.tcl       # Quartus pin assignment script
       └── signal_tap.stp            # Quartus signal tap assignments
   ```

   **Required Files:**
   - **`src/qeciphy_syn_wrapper.sv`**: SystemVerilog top-level that instantiates QECIPHY with your platform's clock and pin connections
   - **`src.f`**: File list containing the path to your top-level module
   - **`syn/constraints.xdc`** (Xilinx): XDC file with pin assignments, clock definitions, and I/O standards for your platform
   - **`syn/project_settings.tcl`** (Altera): Tcl script sourced by Quartus with board-level project settings
   - **`syn/clock_constraints.sdc`** (Altera): SDC file with clock definitions, clock groups, multicycle paths, and false paths
   - **`syn/pin_assignments.tcl`** (Altera): Tcl script sourced by Quartus for pin and I/O standard assignments

3. **Update Config for Synthesis**:
   Add synthesis settings to your profile in `config.json`:
   ```json
   "synth": {
     "top": "qeciphy_syn_wrapper",
     "filelists": [
       "example_designs/<your-platform>/src.f"
     ],
     "constraints": [
       "example_designs/<your-platform>/syn/constraints.xdc"
     ]
   }
   ```

   For Altera, list `.sdc` and `.tcl` constraint files instead of `.xdc`:
   ```json
   "constraints": [
     "example_designs/<your-platform>/syn/project_settings.tcl",
     "example_designs/<your-platform>/syn/clock_constraints.sdc",
     "example_designs/<your-platform>/syn/pin_assignments.tcl"
   ]
   ```

4. **Run Synthesis**:
   ```bash
   make synth OPT_PROFILE=<your-platform>
   ```
   
   For Xilinx profiles, this creates a bitstream and debug file at:
   - `run/synth_qeciphy/synth_qeciphy.runs/impl_1/qeciphy_syn_wrapper.bit`
   - `run/synth_qeciphy/synth_qeciphy.runs/impl_1/qeciphy_syn_wrapper.ltx`

   For Altera profiles, the SOF programming file is at:
   - `run/<project_name>/output_files/<top>.sof`

   where `<project_name>` is controlled by `OPT_QUARTUS_PROJECT` (default: `qeciphy_integration`).

### Step 5: Integrate into Your Actual Design

#### Add QECIPHY Files to Your Project

For Xilinx, add all files listed in `src_xilinx.f` and `generated_ip.f` to your project. For Altera, add all files listed in `src_altera.f` and `generated_ip.f`.

#### Instantiate QECIPHY Module

```systemverilog
QECIPHY i_QECIPHY (
    // Clocks and Reset
    .RCLK       (gt_refclk),
    .FCLK       (freerun_clk), 
    .ACLK       (axi_clk),
    .ARSTn      (aresetn),
    
    // TX Interface (from your design)
    .TX_TDATA   (qeciphy_tx_tdata),
    .TX_TVALID  (qeciphy_tx_tvalid),
    .TX_TREADY  (qeciphy_tx_tready),
    
    // RX Interface (to your design)
    .RX_TDATA   (qeciphy_rx_tdata),
    .RX_TVALID  (qeciphy_rx_tvalid), 
    .RX_TREADY  (qeciphy_rx_tready),
    
    // Status and Control
    .STATUS     (qeciphy_status),
    .ECODE      (qeciphy_ecode),
    .LINK_READY (qeciphy_link_ready),
    .FAULT_FATAL(qeciphy_fault_fatal),
    
    // GT Interface (connect to transceivers)
    .GT_TXP     (gt_txp),
    .GT_TXN     (gt_txn),
    .GT_RXP     (gt_rxp),
    .GT_RXN     (gt_rxn)
);
```

#### Multiple Lanes in One Quad (`QECIPHY_QUAD`)

For a single lane, instantiate `QECIPHY` as above. To put 2-4 lanes in the same physical transceiver quad,
instantiate `QECIPHY_QUAD` (`src/QECIPHY_QUAD.sv`) instead. It contains `NUM_LANES` `QECIPHY` lanes plus
any per-quad clocking the vendor needs. Its ports are the same as `QECIPHY`'s, but per lane: single-bit
signals become `[NUM_LANES-1:0]` vectors, and `TX_TDATA`/`RX_TDATA`/`STATUS`/`ECODE` become unpacked arrays
indexed by lane. `RCLK` and `FCLK` are shared by all lanes.

```systemverilog
QECIPHY_QUAD #(
    .NUM_LANES(4)
) i_QECIPHY_QUAD (
    .RCLK       (gt_refclk),            // shared by all lanes
    .FCLK       (freerun_clk),          // shared by all lanes
    .ACLK       (axi_clk),              // [NUM_LANES-1:0]
    .ARSTn      (aresetn),              // [NUM_LANES-1:0]
    .TX_TDATA   (qeciphy_tx_tdata),     // logic [63:0] qeciphy_tx_tdata [NUM_LANES]
    .TX_TVALID  (qeciphy_tx_tvalid),
    .TX_TREADY  (qeciphy_tx_tready),
    .RX_TDATA   (qeciphy_rx_tdata),     // logic [63:0] qeciphy_rx_tdata [NUM_LANES]
    .RX_TVALID  (qeciphy_rx_tvalid),
    .RX_TREADY  (qeciphy_rx_tready),
    .STATUS     (qeciphy_status),       // logic [3:0] qeciphy_status [NUM_LANES]
    .ECODE      (qeciphy_ecode),        // logic [3:0] qeciphy_ecode [NUM_LANES]
    .LINK_READY (qeciphy_link_ready),
    .FAULT_FATAL(qeciphy_fault_fatal),
    .GT_TX_P    (gt_tx_p),
    .GT_TX_N    (gt_tx_n),
    .GT_RX_P    (gt_rx_p),
    .GT_RX_N    (gt_rx_n)
);
```

Per vendor:
- **Xilinx GTY**: all lanes share one GT COMMON (QPLL0) inside `QECIPHY_QUAD`. The profile must set
  `transceiver.gt_common` to `"external"` and `transceiver.shared_channel_core` to `"true"`. Every lane uses
  the same generated channel core, customized for `transceiver.gt_loc`. Place each lane on its own channel
  with a `LOC` on `*i_QECIPHY_QUAD/gen_lane[N].i_QECIPHY*...GTYE4_CHANNEL_PRIM_INST` in your
  XDC, and repeat the per-lane clock constraints for each `gen_lane[N]`. See
  `example_designs/*_quad/syn/constraints.xdc`. The shared QPLL0 is reset at power-up and when every lane's
  `ARSTn` is asserted together, never by a single lane's reset.
- **Xilinx GTH**: currently unsupported. The GTH path (`qeciphy_gth_common`) is implemented but has not been
  tested in simulation or on hardware.
- **Xilinx GTX**: not supported (each GTX lane embeds its own COMMON). Elaboration fails with an error.
- **Altera E-tile/F-tile**: there is no shared PLL block (each lane's PHY has its own TX PLL and RX CDR), so
  the lanes are instantiated side by side. Keep any per-tile reference clock IP (e.g. the F-tile `refclk`
  IP) in your top level as for a single `QECIPHY`, and assign each lane's serial pins in your pin
  assignments. There is no Altera multi-lane example design yet, and this path has not been compiled in
  Quartus. Expect each lane to need two fabric PLLs (`qeciphy_altera_clk_mmcm`), and per-lane copies of the
  SDC clock constraints.

Selecting a configuration `QECIPHY_QUAD` can't support (Xilinx with `transceiver.gt_common` not set to
`"external"`, GTX, or `NUM_LANES` outside 1-4) is an elaboration error that says what to change.

### Step 6: Apply Timing Constraints and Run Synthesis

1. **Add Timing Constraints**: Copy the appropriate timing constraints from the [Timing Constraints](#timing-constraints) section below and add them to your project's constraint file (`.xdc` for Xilinx, `.sdc` for Altera).

2. **Run Synthesis**: With QECIPHY integrated into your design and timing constraints applied, run synthesis with your complete design.

## Timing Constraints

You must add the following timing constraints to your project for proper operation. Xilinx profiles use XDC format (Vivado); Altera profiles use SDC format (Quartus).

We recommend instantiating the IP with the name `i_QECIPHY` or `u_QECIPHY`. The following constraints can then be applied based on the type of transceiver being used. These constraints handle the clock relationships within the QECIPHY.

**Note:** The E-Tile and F-Tile SDC constraints use `get_keepers` path expressions containing `i_QECIPHY` — the `i_QECIPHY` instantiation name is required for these expressions to resolve.

### GTY Transceiver Constraints

```tcl
# Reference clock
create_clock -period <refclk_period> -name RCLK [get_ports <refclk_port>]

# Free-running clock
create_clock -period <freerun_clk_period> -name FCLK [get_ports <freerun_clk_port>]

# AXI4 stream clock
create_clock -period <axi_clk_period> -name ACLK [get_ports <axi_clk_port>]

# Create generated clocks for GT wrapper clocks
create_generated_clock -name rx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name rx_clk_2x [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_gt_rx_clk/O}]
create_generated_clock -name tx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name tx_clk_2x [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_gt_tx_clk/O}]

# Set asynchronous clock groups
# Optionally include ACLK if needed
set_clock_groups -asynchronous -group [get_clocks RCLK] -group [get_clocks FCLK] -group [get_clocks {rx_clk rx_clk_2x}] -group [get_clocks {tx_clk tx_clk_2x}]

# Clock delay groups for timing closure
set_property CLOCK_DELAY_GROUP rx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/rx_clk_o || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/rx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/tx_clk_o || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/tx_clk_2x_o}]

# Multicycle paths for GT wrapper internal timing
set_multicycle_path 2 -setup -end -from [get_clocks rx_clk] -to [get_clocks rx_clk_2x]
set_multicycle_path 1 -hold  -end -from [get_clocks rx_clk] -to [get_clocks rx_clk_2x]
set_multicycle_path 2 -setup -start -from [get_clocks rx_clk_2x] -to [get_clocks rx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks rx_clk_2x] -to [get_clocks rx_clk]
set_multicycle_path 2 -setup -end -from [get_clocks tx_clk] -to [get_clocks tx_clk_2x]
set_multicycle_path 1 -hold  -end -from [get_clocks tx_clk] -to [get_clocks tx_clk_2x]
set_multicycle_path 2 -setup -start -from [get_clocks tx_clk_2x] -to [get_clocks tx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks tx_clk_2x] -to [get_clocks tx_clk]
```

### GTH Transceiver Constraints

```tcl
# Reference clock
create_clock -period <refclk_period> -name RCLK [get_ports <refclk_port>]

# Free-running clock
create_clock -period <freerun_clk_period> -name FCLK [get_ports <freerun_clk_port>]

# AXI4 stream clock
create_clock -period <axi_clk_period> -name ACLK [get_ports <axi_clk_port>]

# Create generated clocks for GT wrapper clocks
create_generated_clock -name rx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTH_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name rx_clk_2x [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTH_transceiver.i_BUFG_gt_rx_clk/O}]
create_generated_clock -name tx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTH_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name tx_clk_2x [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTH_transceiver.i_BUFG_gt_tx_clk/O}]

# Set asynchronous clock groups
# Optionally include ACLK if needed
set_clock_groups -asynchronous -group [get_clocks RCLK] -group [get_clocks FCLK] -group [get_clocks {rx_clk rx_clk_2x}] -group [get_clocks {tx_clk tx_clk_2x}]

# Clock delay groups for timing closure
set_property CLOCK_DELAY_GROUP rx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/rx_clk_o || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/rx_clk_2x_o}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/tx_clk_o || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/tx_clk_2x_o}]

# Multicycle paths for GT wrapper internal timing
set_multicycle_path 2 -setup -end -from [get_clocks rx_clk] -to [get_clocks rx_clk_2x]
set_multicycle_path 1 -hold  -end -from [get_clocks rx_clk] -to [get_clocks rx_clk_2x]
set_multicycle_path 2 -setup -start -from [get_clocks rx_clk_2x] -to [get_clocks rx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks rx_clk_2x] -to [get_clocks rx_clk]
set_multicycle_path 2 -setup -end -from [get_clocks tx_clk] -to [get_clocks tx_clk_2x]
set_multicycle_path 1 -hold  -end -from [get_clocks tx_clk] -to [get_clocks tx_clk_2x]
set_multicycle_path 2 -setup -start -from [get_clocks tx_clk_2x] -to [get_clocks tx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks tx_clk_2x] -to [get_clocks tx_clk]
```

### GTX Transceiver Constraints

```tcl
# Reference clock
create_clock -period <refclk_period> -name RCLK [get_ports <refclk_port>]

# Free-running clock
create_clock -period <freerun_clk_period> -name FCLK [get_ports <freerun_clk_port>]

# AXI4 stream clock
create_clock -period <axi_clk_period> -name ACLK [get_ports <axi_clk_port>]

# Create generated clocks from MMCM outputs
create_generated_clock -name rx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_rx_clks*inst/mmcm_adv_inst/CLKOUT0}]
create_generated_clock -name rx_clk_2x [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_rx_clks*inst/mmcm_adv_inst/CLKOUT1}]
create_generated_clock -name tx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_tx_clks*inst/mmcm_adv_inst/CLKOUT0}]
create_generated_clock -name tx_clk_2x [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_tx_clks*inst/mmcm_adv_inst/CLKOUT1}]

# Set asynchronous clock groups
# Optionally include ACLK if needed
set_clock_groups -asynchronous -group [get_clocks RCLK] -group [get_clocks FCLK] -group [get_clocks {rx_clk rx_clk_2x}] -group [get_clocks {tx_clk tx_clk_2x}]

# Clock delay groups for timing closure
set_property CLOCK_DELAY_GROUP rx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_rx_clks/inst/clk_out || NAME =~ *QECIPHY*i_rx_clks/inst/clk_out_2x}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_tx_clks/inst/clk_out || NAME =~ *QECIPHY*i_tx_clks/inst/clk_out_2x}]

# Multicycle paths for clock domain timing
set_multicycle_path 2 -setup -end -from [get_clocks rx_clk] -to [get_clocks rx_clk_2x]
set_multicycle_path 1 -hold  -end -from [get_clocks rx_clk] -to [get_clocks rx_clk_2x]
set_multicycle_path 2 -setup -start -from [get_clocks rx_clk_2x] -to [get_clocks rx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks rx_clk_2x] -to [get_clocks rx_clk]
set_multicycle_path 2 -setup -end -from [get_clocks tx_clk] -to [get_clocks tx_clk_2x]
set_multicycle_path 1 -hold  -end -from [get_clocks tx_clk] -to [get_clocks tx_clk_2x]
set_multicycle_path 2 -setup -start -from [get_clocks tx_clk_2x] -to [get_clocks tx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks tx_clk_2x] -to [get_clocks tx_clk]

# GT location constraint (replace 'location' with actual GT site)
set_property LOC {location} [get_cells -hierarchical -filter {lib_cell =~ GTXE2_CHANNEL && NAME =~ *QECIPHY*}]
```

### E-Tile Transceiver Constraints

These constraints are in SDC format for Quartus Prime. They assume the QECIPHY instance is named `i_QECIPHY` — this naming is required for the false path `get_keepers` expressions to resolve correctly.

```tcl
# Reference clock and free-running/AXI clock (replace period and port names for your board)
create_clock -name RCLK -period <refclk_period> [get_ports {<refclk_port>}]
create_clock -name ACLK -period <axi_clk_period> [get_ports {<axi_clk_port>}]

# QECIPHY internal clocks from Altera clock divider network
# Periods depend on the configured line rate:
#   2x clock period (ns) = 40 / line_rate_gbps    (e.g. 3.878 ns at 10.3125 Gbps)
#   1x clock period (ns) = 80 / line_rate_gbps    (e.g. 7.756 ns at 10.3125 Gbps)
create_clock -name tx_clk_2x_o -period <2x_period> \
    [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_tx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div1]
create_clock -name rx_clk_2x_o -period <2x_period> \
    [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_rx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div1]
create_clock -name tx_clk_o -period <1x_period> \
    [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_tx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div2]
create_clock -name rx_clk_o -period <1x_period> \
    [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_rx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div2]

# Collect clock groups
set rx_clk_2x [get_clocks -include_generated_clocks rx_clk_2x_o]
set rx_clk_1x [get_clocks -include_generated_clocks rx_clk_o]
set tx_clk_2x [get_clocks -include_generated_clocks tx_clk_2x_o]
set tx_clk_1x [get_clocks -include_generated_clocks tx_clk_o]

set rx_grp [add_to_collection $rx_clk_2x $rx_clk_1x]
set tx_grp [add_to_collection $tx_clk_2x $tx_clk_1x]

# Set asynchronous clock groups
# Optionally include additional board clocks
set_clock_groups -asynchronous \
    -group [get_clocks RCLK] \
    -group [get_clocks -include_generated_clocks ACLK] \
    -group $rx_grp \
    -group $tx_grp

# Multicycle paths for 1x/2x clock pair timing
set_multicycle_path -setup -end   -from $rx_clk_2x -to $rx_clk_1x 2
set_multicycle_path -hold  -end   -from $rx_clk_2x -to $rx_clk_1x 1
set_multicycle_path -setup -start -from $rx_clk_1x -to $rx_clk_2x 2
set_multicycle_path -hold  -start -from $rx_clk_1x -to $rx_clk_2x 1
set_multicycle_path -setup -end   -from $tx_clk_2x -to $tx_clk_1x 2
set_multicycle_path -hold  -end   -from $tx_clk_2x -to $tx_clk_1x 1
set_multicycle_path -setup -start -from $tx_clk_1x -to $tx_clk_2x 2
set_multicycle_path -hold  -start -from $tx_clk_1x -to $tx_clk_2x 1

# False paths for E-Tile reset/ready signals crossing clock domains
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|gen_etile.transceiver_inst|xcvrnphy_fme_0|g_pma_rsfec_reset.g_auto_reset.reset_ip_auto_etile_inst|reset_control_inst|g_rx.g_rx[0].g_rx.counter_rx_ready|r_reset}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|i_rx_ready_sync|sync_stage_sf[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|gen_etile.transceiver_inst|xcvrnphy_fme_0|g_pma_rsfec_reset.g_auto_reset.reset_ip_auto_etile_inst|reset_control_inst|g_tx.g_tx[0].g_tx.counter_tx_ready|r_reset}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|i_tx_ready_sync|sync_stage_sf[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|gen_etile.transceiver_inst|xcvrnphy_fme_0|g_pma_rsfec_reset.g_auto_reset.reset_ip_auto_etile_inst|reset_control_inst|g_rx.g_rx[0].g_rx.counter_rx_ready|r_reset}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|i_rx_ready_2x_sync|sync_stage_sf[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|gen_etile.transceiver_inst|xcvrnphy_fme_0|g_pma_rsfec_reset.g_auto_reset.reset_ip_auto_etile_inst|reset_control_inst|g_tx.g_tx[0].g_tx.counter_tx_ready|r_reset}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|i_tx_ready_2x_sync|sync_stage_sf[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_resetcontroller|i_cdc_gt_rst_n_o|sync_stage_sf[1]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tx_reset_sync_ff[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_resetcontroller|i_cdc_gt_rst_n_o|sync_stage_sf[1]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|rx_reset_sync_ff[0]}]
```

### F-Tile Transceiver Constraints

These constraints are in SDC format for Quartus Prime. They assume the QECIPHY instance is named `i_QECIPHY`. The clock creation paths are identical to E-Tile; only the false path `get_keepers` expressions differ due to the F-Tile's internal reset controller hierarchy.

```tcl
# Reference clock and AXI clock (replace period and port names for your board)
create_clock -name RCLK -period <refclk_period> [get_ports {<refclk_port>}]
create_clock -name ACLK -period <axi_clk_period> [get_ports {<axi_clk_port>}]

# QECIPHY internal clocks from Altera clock divider network
# Periods depend on the configured line rate:
#   2x clock period (ns) = 40 / line_rate_gbps    (e.g. 3.878 ns at 10.3125 Gbps)
#   1x clock period (ns) = 80 / line_rate_gbps    (e.g. 7.756 ns at 10.3125 Gbps)
create_clock -name tx_clk_2x_o -period <2x_period> \
    [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_tx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div1]
create_clock -name rx_clk_2x_o -period <2x_period> \
    [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_rx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div1]
create_clock -name tx_clk_o -period <1x_period> \
    [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_tx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div2]
create_clock -name rx_clk_o -period <1x_period> \
    [get_pins i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tile_rx_clk_network|intelclkctrl_0|clkdiv_inst|clock_div2]

# Collect clock groups
set rx_clk_2x [get_clocks -include_generated_clocks rx_clk_2x_o]
set rx_clk_1x [get_clocks -include_generated_clocks rx_clk_o]
set tx_clk_2x [get_clocks -include_generated_clocks tx_clk_2x_o]
set tx_clk_1x [get_clocks -include_generated_clocks tx_clk_o]

set rx_grp [add_to_collection $rx_clk_2x $rx_clk_1x]
set tx_grp [add_to_collection $tx_clk_2x $tx_clk_1x]

# Set asynchronous clock groups
# Optionally include additional board clocks
set_clock_groups -asynchronous \
    -group [get_clocks RCLK] \
    -group [get_clocks -include_generated_clocks ACLK] \
    -group $rx_grp \
    -group $tx_grp

# Multicycle paths for 1x/2x clock pair timing
set_multicycle_path -setup -end   -from $rx_clk_2x -to $rx_clk_1x 2
set_multicycle_path -hold  -end   -from $rx_clk_2x -to $rx_clk_1x 1
set_multicycle_path -setup -start -from $rx_clk_1x -to $rx_clk_2x 2
set_multicycle_path -hold  -start -from $rx_clk_1x -to $rx_clk_2x 1
set_multicycle_path -setup -end   -from $tx_clk_2x -to $tx_clk_1x 2
set_multicycle_path -hold  -end   -from $tx_clk_2x -to $tx_clk_1x 1
set_multicycle_path -setup -start -from $tx_clk_1x -to $tx_clk_2x 2
set_multicycle_path -hold  -start -from $tx_clk_1x -to $tx_clk_2x 1

# False paths for F-Tile reset/ready signals crossing clock domains
set_false_path -from [get_keepers -no_duplicates {synth_qeciphy_auto_tiles|*__reset_controller|x_f_tile_soft_reset_ctlr_sip_v1|x_ftile_reset|rst_ctrl|rx_lane_current_state_r[13]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|i_rx_ready_sync|sync_stage_sf[0]}]
set_false_path -from [get_keepers -no_duplicates {synth_qeciphy_auto_tiles|*__reset_controller|x_f_tile_soft_reset_ctlr_sip_v1|x_ftile_reset|rst_ctrl|tx_lane_current_state_r[13]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|i_tx_ready_sync|sync_stage_sf[0]}]
set_false_path -from [get_keepers -no_duplicates {synth_qeciphy_auto_tiles|*__reset_controller|x_f_tile_soft_reset_ctlr_sip_v1|x_ftile_reset|rst_ctrl|rx_lane_current_state_r[13]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|i_rx_ready_2x_sync|sync_stage_sf[0]}]
set_false_path -from [get_keepers -no_duplicates {synth_qeciphy_auto_tiles|*__reset_controller|x_f_tile_soft_reset_ctlr_sip_v1|x_ftile_reset|rst_ctrl|tx_lane_current_state_r[13]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|i_tx_ready_2x_sync|sync_stage_sf[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_resetcontroller|i_cdc_gt_rst_n_o|sync_stage_sf[1]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|tx_reset_sync_ff[0]}]
set_false_path -from [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_resetcontroller|i_cdc_gt_rst_n_o|sync_stage_sf[1]}] -to [get_keepers -no_duplicates {i_QECIPHY|i_qeciphy_serdes|i_qeciphy_gt_wrapper|gen_altera.i_qeciphy_gt_altera|rx_reset_sync_ff[0]}]
```

> **Note:** The exact keeper paths for F-Tile false paths depend on Quartus's auto-tile placement. Replace `*__reset_controller` with the specific tile instance name reported by the Quartus Timing Analyzer for your device. Refer to `example_designs/agilex7/syn/clock_constraints.sdc` for a board-specific example.

## Data Path Integration Examples

### Reset Synchronization

The `ARSTn` input requires a properly synchronized reset signal. The following example shows how to synchronize an external asynchronous reset (`async_rst_n`) to the AXI clock domain to create `aresetn` that can be asynchronously asserted but is synchronously de-asserted.

```systemverilog
logic [1:0] aresetn_sync;
logic aresetn;

assign aresetn = aresetn_sync[1];

always_ff @(posedge axi_clk or negedge async_rst_n) begin
    if (!async_rst_n) begin
        aresetn_sync <= 2'h0;
    end else begin
        aresetn_sync <= {aresetn_sync[0], 1'b1};
    end
end
```

### TX Data Path Example

```systemverilog
// From your application logic
logic [63:0] user_tdata;
logic        user_tvalid;
logic        user_tready;

// QECIPHY TX interface signals
logic [63:0] qeciphy_tx_tdata;
logic        qeciphy_tx_tvalid;
logic        qeciphy_tx_tready;

// Connect user logic to QECIPHY TX interface
assign qeciphy_tx_tdata  = user_tdata;
assign qeciphy_tx_tvalid = user_tvalid;
assign user_tready       = qeciphy_tx_tready;
```

### RX Data Path Example

```systemverilog
// QECIPHY RX interface signals
logic [63:0] qeciphy_rx_tdata;
logic        qeciphy_rx_tvalid;
logic        qeciphy_rx_tready;

// To your application logic
logic [63:0] user_rx_tdata;
logic        user_rx_tvalid;

// Connect QECIPHY RX interface to user logic
assign user_rx_tdata  = qeciphy_rx_tdata;
assign user_rx_tvalid = qeciphy_rx_tvalid;
assign qeciphy_rx_tready = 1'b1; // Always ready to accept data
```

### Status Monitoring Implementation

```systemverilog
`include "/path/to/qeciphy_pkg.sv"
...
import qeciphy_pkg::*;

// Status and Error signals from QECIPHY
logic [3:0] qeciphy_status;
logic [3:0] qeciphy_ecode;
logic       qeciphy_link_ready;
logic       qeciphy_fault_fatal;

// Status monitoring enums
qeciphy_status_t qeciphy_status_enum;
qeciphy_error_t  qeciphy_ecode_enum;

// Convert STATUS and ECODE to enums
qeciphy_status_enum = qeciphy_status_t'(qeciphy_status);

always_ff @(posedge axi_clk) begin
    if (!aresetn) begin
        qeciphy_ecode_enum <= NO_ERROR;
    end else if (qeciphy_fault_fatal) begin
        qeciphy_ecode_enum <= qeciphy_error_t'(qeciphy_ecode);
    end
end
```

Note: If the QECIPHY enters FAULT-FATAL state, please reset the IP to get out of the fault condition.

## Interface Details

### Clocking and Reset
- **RCLK**: Reference clock for transceivers
- **FCLK**: Free-running clock
- **ACLK**: AXI4-Stream clock for TX/RX interfaces
- **ARSTn**: Active LOW reset, asynchronously asserted, synchronously de-asserted to ACLK domain

**Note:** RCLK, FCLK and ACLK can all be asynchronous to each other. QECIPHY handles clock domain crossing internally.

### AXI4-Stream Protocol

QECIPHY uses standard AXI4-Stream protocol with 64-bit data width:

**Transmit Channel:**
- **TX_TDATA[63:0]**: Data payload from the user logic
- **TX_TVALID**: User indicates valid data
- **TX_TREADY**: QECIPHY can accept data

**Receive Channel:**
- **RX_TDATA[63:0]**: Data payload to the user logic
- **RX_TVALID**: QECIPHY indicates valid data
- **RX_TREADY**: User can accept data

**Important Note**: The backpressure support in QECIPHY is minimal. User logic should always be able to consume RX data. Design your receive path accordingly.

### Status and Error Codes

#### STATUS[3:0] Values
- `4'h0`: RESET - In reset
- `4'h1`: WAIT-FOR-RESET - Waiting for reset completion
- `4'h2`: LINK-TRAINING - Link training in progress  
- `4'h3`: RX-LOCKED - Receiver locked to data pattern
- `4'h4`: LINK-READY - Ready for data transfer
- `4'h5`: FAULT-FATAL - Fatal fault detected

#### ECODE[3:0] Values
- `4'h0`: NO-ERROR - No error
- `4'h1`: FAW-ERROR - Frame Alignment Word missing
- `4'h2`: CRC-ERROR - CRC error detected
- `4'h3`: TX-FIFO-OVERFLOW - Transmit FIFO overflow
- `4'h4`: RX-FIFO-OVERFLOW - Receive FIFO overflow

## Support

For additional support, please refer to:
- [README.md](README.md) - Project overview and quick start
- [docs/architecture.md](docs/architecture.md) - Detailed architecture description
- [GitHub Issues](https://github.com/riverlane/qeciphy/issues) - Report issues or ask questions
