# Formal Verification Guide

This document explains the formal verification infrastructure in the QECIPHY project, including file organization, required components, and how to run formal verification.

## Overview

The formal verification framework uses Synopsys VC Formal (VCF) to verify SystemVerilog Assertions (SVA) properties against the design. The infrastructure supports modular verification where each module can have its own set of checkers, binds, and test harnesses.

## Directory Structure

The formal verification files are organized in the following directory structure:

```
formal/
├── harness/                     # Test harnesses for each module
│   └── ...                      # Module harnesses
└── tcl/                         # Module-specific TCL configuration
    └── ...                      # Module TCL files

sva/                             # SystemVerilog Assertions
├── binds/                       # Bind statements to connect checkers to DUTs
│   └── ...                      # Module binds
└── checkers/                    # SVA property definitions
    └── ...                      # Module checkers

run/formal/                      # Runtime outputs (generated)
└── <module_name>/
    └── vcf_logs/                # VCF tool logs and reports
```

## Required Files for Adding Formal Verification

To add formal verification support for a new module, you need to create four files following the naming convention `<module_name>_*`:

### 1. Checker Module (`sva/checkers/<module_name>_checker.sv`)

This file contains the SystemVerilog Assertions that define the properties to be verified. The checker module should:

- Take all relevant signals from the DUT as inputs
- Define sequences and properties using SVA syntax
- Include assertions (`assert property`) to verify design behavior
- Use proper clocking and reset disable conditions

**Example structure:**
```systemverilog
module <module_name>_checker (
  input logic clk,
  input logic rst_n,
  // ... other DUT signals
);

  // Property definitions
  property <property_name>;
    @(posedge clk) disable iff (!rst_n)
      <assertion_logic>;
  endproperty

  // Assertions to verify design behavior
  <property_name>_A : assert property (<property_name>);
  
endmodule
```

### 2. Bind Module (`sva/binds/<module_name>_bind.sv`)

This file connects the checker module to the DUT using SystemVerilog bind statements:

```systemverilog
bind <module_name> <module_name>_checker i_<module_name>_bind (
  .clk(clk),
  .rst_n(rst_n),
  // ... signal connections
);
```

All checkers are bound unconditionally and are active in both simulation and formal verification.

### 3. Test Harness (`formal/harness/<module_name>_harness.sv`)

The harness instantiates the DUT and provides the formal verification environment with assumptions:

```systemverilog
module <module_name>_harness;
  // Signal declarations
  logic clk;
  logic rst_n;
  // ... other signals

  // DUT instantiation
  <module_name> dut (.*);

  // Assumptions to constrain input stimulus
  property realistic_input_sequence;
    @(posedge clk) disable iff (!rst_n)
      <assumption_logic>;
  endproperty

  realistic_input_sequence_A : assume property (realistic_input_sequence);
  
  // Additional environment constraints
endmodule
```

Assumptions placed in harnesses apply only during formal verification. They are not active during simulation, ensuring that simulation is not artificially constrained.

### 4. TCL Configuration (`formal/tcl/<module_name>.tcl`)

Module specific configuration for clocks, resets, and other formal verification settings:

```tcl
# Define clock and reset
create_clock clk -period 4
create_reset rst_n -sense low -clock clk

# Advanced formal verification configurations
# Black boxing, abstraction, cutpoints, waivers,
# bounded depth, induction hints, engine selection, etc.
```

### 5. Update File Lists

Add the new checker and bind files to `sva.f`:

```
sva/checkers/<module_name>_checker.sv
sva/binds/<module_name>_bind.sv
```

## Running Formal Verification

### Prerequisites

- Synopsys VC Formal (VCF) must be installed and available in PATH
- All required files must exist for the specified module

### Basic Usage

Run formal verification for a specific module:

```bash
make formal OPT_TOP=<module_name>
```

### Available Options

- **OPT_TOP**: Specifies the module name to verify (required)
- **OPT_MODE**: Execution mode
  - `batch` (default): Run in batch mode and generate reports
  - `gui`: Launch interactive GUI with Verdi

### Examples

```bash
# Run formal verification on CRC16 IBM3740 module
make formal OPT_TOP=qeciphy_crc16_ibm3740

# Run with GUI for interactive debugging
make formal OPT_TOP=qeciphy_crc16_ibm3740 OPT_MODE=gui
```

**Note:** When running formal verification on a top-level module, checkers for all instantiated submodules are automatically bound and verified.

## What to Expect

### Output Locations

- **Log Directory**: `run/formal/<module_name>/vcf_logs/`
- **Results File**: `run/formal/<module_name>/results.txt` (batch mode)

### Typical Results

- **PASS**: Assertions hold under all possible input conditions
- **FAIL**: Counterexample found showing assertion violation
- **INCONCLUSIVE**: Verification incomplete within time/resource limits
- **VACUOUS**: Property conditions never triggered during verification

### Debugging Failed Assertions

When running in GUI mode (`OPT_MODE=gui`), you can:

1. View waveforms showing counterexample traces
2. Examine signal values leading to assertion failures
3. Modify assumptions or constraints interactively
4. Add additional debug signals to the waveform viewer

## Best Practices

1. **Property Design**: Write clear, targeted properties that verify specific behaviors
2. **Assumptions**: Use assumptions to constrain input stimulus to realistic scenarios
3. **Clock Domains**: Properly specify clock and reset relationships in TCL files
4. **Documentation**: Comment properties to explain their intent
5. **Design Intent Rule**: If a rule would change when the module is integrated into a larger system, it belongs in the harness or TCL - not in the checker

## Getting Help

For additional support, refer to the Synopsys VCS Formal documentation or contact the QECIPHY maintainers.

- **Maintainers:** See [MAINTAINERS.md](MAINTAINERS.md) for contact information