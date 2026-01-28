# Contributing to QECIPHY

Thank you for your interest in contributing to QECIPHY! 

Before you start, please read through this guide to understand our contribution process, coding standards, and how to set up your development environment. Please also speak to the [maintainers](MAINTAINERS.md) if you plan to work on a large feature or change.

## Code of Conduct

This project adheres to the [Contributor Covenant Code of Conduct](CODE_OF_CONDUCT.md). By participating, you are expected to uphold this code.

## Quick Setup Test

```bash
# Verify development tools work
make clean
make lint
make format
make generate-xci OPT_PROFILE=zcu216
make sim OPT_PROFILE=zcu216 OPT_TOOL=xsim
make formal OPT_TOP=<module_name>
make synth OPT_PROFILE=zcu216
```

## How to Contribute

### Reporting Issues

Include in your issue report:
- Profile used 
- Tool version
- Complete error messages and reproduction steps

### Submitting Changes

1. **Create a branch:**
   ```bash
   git checkout -b <branch_name>
   ```

2. **Make your changes** following the coding standards below.

3. **Test your changes:**
   ```bash
   make distclean
   make format
   make lint
   # Run simulations and synthesis for affected profiles
   ```

4. **Commit your changes:**
   ```bash
   git add .
   git commit -m "<Descriptive commit message>"
   ```

5. **Push and create a pull request**
    ```bash
    git push origin <branch_name>
    ```
    Open a pull request on GitHub with a clear description of your changes.

6. **Address feedback** from maintainers and reviewers.

7. **Merge** your changes once approved and delete your branch.

## Coding Standards

### SystemVerilog Guidelines

- **Naming Convention:**
  - Modules: `snake_case` (e.g., `qeciphy_controller`)
  - Signals: `snake_case` with `_i/_o` suffixes for ports (e.g., `s_axis_tdata_i`, `m_axis_tvalid_o`)
  - Parameters: `UPPER_CASE` (e.g., `DATA_WIDTH`)
  - Constants: `UPPER_CASE` (e.g., `CRC_POLYNOMIAL`)

- **File Organization:**
  - One module per file
  - Filename matches module name

- **Combinational Logic Complexity:**
  - The `D`/`CE` input of any flip-flop must not be driven by combinational logic that depends on more than 20 registered signals.

### Example Module Template:

```systemverilog
// SPDX-License-Identifier: LicenseRef-LICENSE

module qeciphy_example #(
    parameter int DATA_WIDTH = 64,
    parameter int ADDR_WIDTH = 8
) (
    input  logic                    clk_i,
    input  logic                    rst_n_i,
    input  logic [DATA_WIDTH-1:0]   s_axis_tdata_i,
    input  logic                    s_axis_tvalid_i,
    output logic                    s_axis_tready_o,
    output logic [DATA_WIDTH-1:0]   m_axis_tdata_o,
    output logic                    m_axis_tvalid_o
);

    // Implementation here

endmodule
```

## Adding New Hardware Support

See [INTEGRATION.md](INTEGRATION.md) for detailed platform configuration. For contributors:

1. Add `config.json` profile with required fields
2. Create example design under `example_designs/your_platform/`
3. Test thoroughly - verify synthesis, timing closure, and successful operation on hardware
4. Update documentation as needed

## Documentation Updates

Update documentation when contributing:

- **README.md** for new features
- **INTEGRATION.md** for new platform support  
- **docs/architecture.md** for architectural changes
- **This file** for new development processes

## License

By contributing to QECIPHY, you agree that your contributions will be licensed under the project's license (see [LICENSE](LICENSE) file).

## Getting Help

- **Issues:** Use GitHub Issues for bugs and feature requests
- **Maintainers:** See [MAINTAINERS.md](MAINTAINERS.md) for contact information

Thank you for contributing to QECIPHY!