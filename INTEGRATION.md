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
2. **HDL Instantiation**: Instantiate QECIPHY module directly in your SystemVerilog design
3. **Interface Connection**: Connect AXI4-Stream interfaces to your application logic
4. **Status Monitoring**: Implement link status monitoring and error handling
5. **Constraint Application**: Apply provided timing constraints

## Prerequisites

### Hardware Requirements

- Xilinx FPGA with GTX, GTH, or GTY transceivers
- Appropriate reference clock source
- Differential signal routing between FPGAs

### Software Requirements

- Vivado 2024.1 or later
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
- **zcu106**: Zynq UltraScale with GTH transceivers  
- **kasliSoC**: 7-series with GTX transceivers

If your platform is not listed, create a new profile in `config.json`:

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

**Profile Parameters:**
- `device.part`: Your FPGA part number
- `board`: Xilinx board file (optional)
- `variant`: Transceiver type (GTX/GTH/GTY)
- `fclk_freq`: Transceiver DRP clock frequency in MHz
- `rclk_freq`: Transceiver reference clock frequency in MHz
- `transceiver.gt_loc`: Transceiver location (e.g., "X0Y8") 
- `transceiver.rx_rclk_src`: RX reference clock source (e.g., "X0Y8 clk1+2" means using refclock 1 from the GT quad located 2 quads above X0Y8)
- `transceiver.tx_rclk_src`: TX reference clock source (same format as RX)
- `transceiver.line_rate_gbps`: Transceiver line rate in Gbps (e.g., "10.3125")
- `synth`: Synthesis configuration (optional, for standalone testing)

**Important:** Refer to your FPGA documentation for correct GT site assignments and available reference clock sources for your specific device and board.

### Step 3: Generate Platform-Specific IP

```bash
# Generate XCI cores for your profile
make generate-xci OPT_PROFILE=<your-profile>
```

This generates transceiver IP cores configured for your hardware platform.

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

   **Example Designs Folder Structure:**
   ```
   example_designs/<your-platform>/
   ├── src/
   │   └── qeciphy_syn_wrapper.sv    # Top-level wrapper module
   ├── src.f                         # Source file list
   └── syn/
       └── constraints.xdc           # Platform-specific constraints
   ```

   **Required Files:**
   - **`src/qeciphy_syn_wrapper.sv`**: SystemVerilog top-level that instantiates QECIPHY with your platform's clock and pin connections
   - **`src.f`**: File list containing the path to your top-level module
   - **`syn/constraints.xdc`**: XDC file with pin assignments, clock definitions, and I/O standards for your platform

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

4. **Run Synthesis**:
   ```bash
   make synth OPT_PROFILE=<your-platform>
   ```
   
   This creates a synthesis project with bitstream and debug files at:
   - `run/synth_qeciphy/synth_qeciphy.runs/impl_1/qeciphy_syn_wrapper.bit`
   - `run/synth_qeciphy/synth_qeciphy.runs/impl_1/qeciphy_syn_wrapper.ltx`

### Step 5: Integrate into Your Actual Design

#### Add QECIPHY Files to Your Project

Add all files listed in `src.f` and `xci.f` in your project.

#### Instantiate QECIPHY Module

```systemverilog
QECIPHY #(
    .GT_TYPE("GTY")  // Change based on your platform
) u_qeciphy (
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

### Step 6: Apply Timing Constraints and Run Synthesis

1. **Add Timing Constraints**: Copy the appropriate timing constraints from the [Timing Constraints](#timing-constraints) section below and add them to your project's XDC constraint file.

2. **Run Synthesis**: With QECIPHY integrated into your design and timing constraints applied, run synthesis with your complete design.

## Timing Constraints

You must add the following timing constraints to your project for proper operation.

We recommend instantiating the IP with the name `i_QECIPHY` or `u_QECIPHY`. The following constraints can then be applied based on the type of transceiver being used. These constraints handle the clock relationships within the QECIPHY.

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