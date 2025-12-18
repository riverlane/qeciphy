# QECIPHY Integration Guide

This document provides detailed instructions for integrating QECIPHY into your FPGA design. If you haven't already, please read the [README.md](README.md) for an overview of QECIPHY's features and capabilities.

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
4. **Status Monitoring**: Implement link status and error handling
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

### Design Requirements

Your design must include:
- Reset synchronization logic
- Status monitoring and error handling logic

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
- `transceiver.rx_rclk_src`: RX reference clock source
- `transceiver.tx_rclk_src`: TX reference clock source
- `transceiver.line_rate_gbps`: Transceiver line rate in Gbps (e.g., "12.5")
- `synth`: Synthesis configuration (optional, for standalone testing)

**Important:** Refer to your FPGA documentation for correct GT site assignments and available reference clock sources for your specific device and board.

### Step 3: Generate Platform-Specific IP

```bash
# Generate XCI cores for your profile
make generate-xci OPT_PROFILE=<your-profile>
```

This generates:
- Platform-specific XCI files needed by QECIPHY
- Transceiver IP cores configured for your hardware platform

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
    .TX_TDATA   (m_axis_tx_tdata),
    .TX_TVALID  (m_axis_tx_tvalid),
    .TX_TREADY  (m_axis_tx_tready),
    
    // RX Interface (to your design)
    .RX_TDATA   (s_axis_rx_tdata),
    .RX_TVALID  (s_axis_rx_tvalid), 
    .RX_TREADY  (s_axis_rx_tready),
    
    // Status and Control
    .STATUS     (qeciphy_status),
    .ECODE      (qeciphy_ecode),
    
    // Power Management (optional)
    .PSTATE     (power_state),
    .PREQ       (power_request),
    .PACCEPT    (power_accept),
    .PACTIVE    (power_active),
    
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
# Create generated clocks for GT wrapper clocks
create_generated_clock -name rx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTY_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gtye4_channel_gen.gen_gtye4_channel_inst[0].GTYE4_CHANNEL_PRIM_INST/TXOUTCLK}]

# Set asynchronous clock groups
set_clock_groups -asynchronous -group [get_clocks RCLK] -group [get_clocks {rx_clk gt_rx_clk}] -group [get_clocks {tx_clk gt_tx_clk}]

# Clock delay groups for timing closure
set_property CLOCK_DELAY_GROUP rx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/rx_clk || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gt_rx_clk}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/tx_clk || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gt_tx_clk}]

# Multicycle paths for GT wrapper internal timing
set_multicycle_path 2 -setup -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk]
set_multicycle_path 1 -hold  -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk]
set_multicycle_path 2 -setup -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk]
set_multicycle_path 1 -hold  -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk]
```

### GTH Transceiver Constraints

```tcl
# Create generated clocks for GT wrapper clocks
create_generated_clock -name rx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTH_transceiver.i_BUFG_rx_clk/O}]
create_generated_clock -name gt_rx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gthe4_channel_gen.gen_gthe4_channel_inst[0].GTHE4_CHANNEL_PRIM_INST/RXOUTCLK}]
create_generated_clock -name tx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gen_GTH_transceiver.i_BUFG_tx_clk/O}]
create_generated_clock -name gt_tx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper*channel_inst/gthe4_channel_gen.gen_gthe4_channel_inst[0].GTHE4_CHANNEL_PRIM_INST/TXOUTCLK}]

# Set asynchronous clock groups
set_clock_groups -asynchronous -group [get_clocks RCLK] -group [get_clocks {rx_clk gt_rx_clk}] -group [get_clocks {tx_clk gt_tx_clk}]

# Clock delay groups for timing closure
set_property CLOCK_DELAY_GROUP rx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/rx_clk || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gt_rx_clk}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/tx_clk || NAME =~ *QECIPHY*i_qeciphy_gt_wrapper/gt_tx_clk}]

# Multicycle paths for GT wrapper internal timing
set_multicycle_path 2 -setup -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk]
set_multicycle_path 1 -hold  -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk]
set_multicycle_path 2 -setup -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk]
set_multicycle_path 1 -hold  -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk]
```

### GTX Transceiver Constraints

```tcl
# Create generated clocks from MMCM outputs
create_generated_clock -name rx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_rx_clks*inst/mmcm_adv_inst/CLKOUT0}]
create_generated_clock -name gt_rx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_rx_clks*inst/mmcm_adv_inst/CLKOUT1}]
create_generated_clock -name tx_clk    [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_tx_clks*inst/mmcm_adv_inst/CLKOUT0}]
create_generated_clock -name gt_tx_clk [get_pins -hierarchical -filter {NAME =~ *QECIPHY*i_tx_clks*inst/mmcm_adv_inst/CLKOUT1}]

# Set asynchronous clock groups
set_clock_groups -asynchronous -group [get_clocks RCLK] -group [get_clocks {rx_clk gt_rx_clk}] -group [get_clocks {tx_clk gt_tx_clk}]

# Clock delay groups for timing closure
set_property CLOCK_DELAY_GROUP rx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_rx_clks/inst/clk_out || NAME =~ *QECIPHY*i_rx_clks/inst/clk_out_2x}]
set_property CLOCK_DELAY_GROUP tx_clk_dly_grp [get_nets -hierarchical -filter {NAME =~ *QECIPHY*i_tx_clks/inst/clk_out || NAME =~ *QECIPHY*i_tx_clks/inst/clk_out_2x}]

# Multicycle paths for clock domain timing
set_multicycle_path 2 -setup -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk]
set_multicycle_path 1 -hold  -end -from [get_clocks rx_clk] -to [get_clocks gt_rx_clk]
set_multicycle_path 2 -setup -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_rx_clk] -to [get_clocks rx_clk]
set_multicycle_path 2 -setup -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk]
set_multicycle_path 1 -hold  -end -from [get_clocks tx_clk] -to [get_clocks gt_tx_clk]
set_multicycle_path 2 -setup -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk]
set_multicycle_path 1 -hold  -start -from [get_clocks gt_tx_clk] -to [get_clocks tx_clk]

# GT location constraint (replace 'location' with actual GT site)
set_property LOC {location} [get_cells -hierarchical -filter {lib_cell =~ GTXE2_CHANNEL && NAME =~ *QECIPHY*}]
```

### Additional User Clocks

You must also define your user clocks:

```tcl
# Your reference clock (adjust period based on your frequency)
create_clock -period 6.400 -name RCLK [get_ports your_refclk_port]

# Your free-running clock (adjust period based on your frequency) 
create_clock -period 6.400 -name FCLK [get_ports your_freerun_clk_port]

# Your AXI stream clock
create_clock -period 4.000 -name ACLK [get_ports your_axi_clk_port]

# Optional: Set user clocks as asynchronous (QECIPHY handles all CDC internally)
set_clock_groups -asynchronous -group [get_clocks RCLK] -group [get_clocks FCLK] -group [get_clocks ACLK]
```

## Data Path Integration Examples

### Reset Synchronization

The `ARSTn` input requires a properly synchronized reset signal. The following example shows how to synchronize an external asynchronous reset (`async_rst_n`) to the AXI clock domain to create `aresetn` that is asynchronously deasserted and synchronously asserted:

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
assign busy = (m_axis_tx_tvalid & !m_axis_tx_tready);

// Your application logic generates data
always_ff @(posedge axi_clk) begin
    if (!aresetn) begin
        m_axis_tx_tvalid <= 1'b0;
        m_axis_tx_tdata  <= 64'h0;
    end else if (data_available && !busy) begin
        m_axis_tx_tvalid <= 1'b1;
        m_axis_tx_tdata  <= application_data;
    end else if (m_axis_tx_tready) begin
        m_axis_tx_tvalid <= 1'b0;
    end
end
```

### RX Data Path Example

```systemverilog
// Your application logic receives data
always_ff @(posedge axi_clk) begin
    if (!aresetn) begin
        s_axis_rx_tready <= 1'b1;  // Always ready to receive
    end else if (s_axis_rx_tvalid && s_axis_rx_tready) begin
        // Process received data
        process_received_data(s_axis_rx_tdata);
    end
end
```

### Status Monitoring Implementation

```systemverilog
// Status bit definitions
typedef enum logic [3:0] {
    STATUS_RESET          = 4'h0,  // PHY controller in reset
    STATUS_WAIT_FOR_RESET = 4'h1,  // Waiting for reset completion
    STATUS_LINK_TRAINING  = 4'h2,  // Link training in progress
    STATUS_RX_LOCKED      = 4'h3,  // Receiver locked to data pattern
    STATUS_LINK_READY     = 4'h4,  // Ready for data transfer
    STATUS_FAULT_FATAL    = 4'h5,  // Fatal fault detected
    STATUS_SLEEP          = 4'h6,  // Sleep state (power management)
    STATUS_WAIT_POWERDOWN = 4'h7   // Waiting for power down
} qeciphy_status_t;

// Monitor link status
always_ff @(posedge axi_clk) begin
    case (qeciphy_status)
        STATUS_LINK_READY: begin
            // Link is ready for data transfer
            link_ready <= 1'b1;
        end
        STATUS_FAULT_FATAL: begin
            // Handle error condition
            link_ready <= 1'b0;
            // Check ECODE for specific error type
        end
        default: begin
            // Link not ready yet
            link_ready <= 1'b0;
        end
    endcase
end
```

Note: If the QECIPHY enters FAULT-FATAL state, please reset the IP to get out of the fault condition.

## Interface Details

### Clocking and Reset
- **RCLK**: Reference clock for transceivers (e.g., 156.25 MHz)
- **FCLK**: Free-running clock (e.g., 100 MHz)
- **ACLK**: AXI4-Stream clock for TX/RX interfaces
- **ARSTn**: Active LOW asynchronous reset input, synchronized internally

**Note:** RCLK, FCLK and ACLK can all be asynchronous to each other.

### AXI4-Stream Protocol

QECIPHY uses standard AXI4-Stream protocol with 64-bit data width:

**Transmit Channel:**
- **TX_TDATA[63:0]**: Data payload (8 bytes per transfer)
- **TX_TVALID**: Source indicates valid data
- **TX_TREADY**: Destination can accept data

**Receive Channel:**
- **RX_TDATA[63:0]**: Data payload (8 bytes per transfer)
- **RX_TVALID**: Source indicates valid data
- **RX_TREADY**: Destination can accept data

**Important Note**: The QECIPHY does not need to support backpressure. User logic should always be able to consume RX data. Design your receive path accordingly.

### Status and Error Codes

#### STATUS[3:0] Values
- `4'h0`: RESET - PHY controller in reset
- `4'h1`: WAIT-FOR-RESET - Waiting for reset completion
- `4'h2`: LINK-TRAINING - Link training in progress  
- `4'h3`: RX-LOCKED - Receiver locked to data pattern
- `4'h4`: LINK-READY - Ready for data transfer
- `4'h5`: FAULT-FATAL - Fatal fault detected
- `4'h6`: SLEEP - Sleep state (power management)
- `4'h7`: WAIT-FOR-POWERDOWN - Waiting for power down

#### ECODE[3:0] Values
- `4'h0`: OK - No error
- `4'h1`: FAP-MISSING - Frame Alignment Packet missing
- `4'h2`: CRC-ERROR - CRC validation failed

### Power Management Interface

QECIPHY provides an optional P-channel interface for power state control, implementing the AMBA Low Power Interface Specification (P Channel Interface, Issue C):

- **PSTATE**: Requested power state (1=active, 0=low power)
- **PREQ**: Power state change request signal (active HIGH). Assert to request transition to the power state specified by PSTATE
- **PACCEPT**: Power state acknowledgment signal (active HIGH). Indicates acceptance of the requested power state transition
- **PACTIVE**: Power state request output from PHY (active HIGH). PHY asserts this signal when it is currently in low power state but detects new AXI-Stream data available on the TX channel, requesting to be transitioned to active power state

#### Always-On Mode
If you want to keep the transceivers always active (no power management):
- Tie PSTATE to `1'b1` (always ON)
- Tie PREQ to `1'b0` (no power state transitions requested)

```systemverilog
// Always-on configuration
assign power_state = 1'b1;    // Always ON
assign power_request = 1'b0;  // No transitions
```

## Support

For additional support, please refer to:
- [README.md](README.md) - Project overview and quick start
- [CONTRIBUTING.md](CONTRIBUTING.md) - Development guidelines
- [GitHub Issues](https://github.com/riverlane/qeciphy/issues) - Report issues or ask questions