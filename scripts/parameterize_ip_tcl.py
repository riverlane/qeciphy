#!/usr/bin/env python3
# SPDX-License-Identifier: BSD-2-Clause
# Copyright (c) 2025 Riverlane Ltd.
#
# parameterize_ip_tcl.py — Insert $argv parameter handling into a
# Quartus-exported Platform Designer TCL script.
#
# Usage:
#   python3 scripts/parameterize_ip_tcl.py <ip_script.tcl> [--params p1 p2 ...]
#   python3 scripts/parameterize_ip_tcl.py <ip_script.tcl> --output <out.tcl>
#
# By default, the script is modified in-place.
# --params names additional set_instance_parameter_value keys to parameterize
# using the built-in PARAM_VAR_MAP.

import argparse
import re
import sys
from pathlib import Path

# Maps set_instance_parameter_value key → TCL variable name
PARAM_VAR_MAP = {
    "pma_data_rate":               "line_rate_mbps",
    "pma_rx_data_rate":            "line_rate_mbps",
    "pma_tx_data_rate":            "line_rate_mbps",
    "fgt_rx_pll_refclk_freq_mhz":  "rclk_freq_mhz",
    "fgt_tx_pll_refclk_freq_mhz":  "rclk_freq_mhz",
    "fgt_tx_pll_refclk_freq_itxt": "rclk_freq_mhz",
    "refclk_fgt_freq_mhz_0":       "rclk_freq_mhz",
    "refclk_fgt_freq_mhz_4":       "rclk_freq_mhz",
    "refclk_fgt_freq_mhz_txt_0":   "rclk_freq_mhz",
    "refclk_fgt_freq_mhz_txt_4":   "rclk_freq_mhz",
    "syspll_freq_mhz_0":           "rclk_freq_mhz",
}

ARGV_BLOCK = """\
# --- Parameters: overridden by $argv when called from quartus_ip.tcl ---
set device         "REPLACE_DEVICE"
set device_family  "REPLACE_FAMILY"
set line_rate_mbps REPLACE_LINE_RATE
set rclk_freq_mhz  REPLACE_RCLK

if {]llength $argv] >= 1} {{ set device         [lindex $argv 0] }}
if {]llength $argv] >= 2}} {{ set device_family  [lindex $argv 1] }}
if {]llength $argv] >= 3}} {{ set line_rate_mbps [lindex $argv 2] }}
if {]llength $argv] >= 4}} {{ set rclk_freq_mhz  [lindex $argv 3] }}

"""


def extract_default(text: str, key: str, fallback: str) -> str:
    """Extract existing hardcoded value for a set_project_property key."""
    pattern = rf'set_project_property\s+{key}\s+\{{([^}}]*)\}}'
    m = re.search(pattern, text)
    return m.group(1) if m else fallback


def build_argv_block(text: str) -> str:
    device = extract_default(text, "DEVICE", "UNKNOWN_DEVICE")
    family = extract_default(text, "DEVICE_FAMILY", "Unknown Family")
    return (
        ARGV_BLOCK
        .replace("REPLACE_DEVICE", device)
        .replace("REPLACE_FAMILY", family)
        .replace("REPLACE_LINE_RATE", "10312.5")
        .replace("REPLACE_RCLK", "156.25")
    )


def insert_argv_block(text: str, block: str) -> str:
    """Insert block before the first 'proc do_create_' definition (idempotent)."""
    if "# --- Parameters: overridden by $argv" in text:
        print("INFO: argv block already present, skipping insertion.")
        return text
    match = re.search(r'^proc do_create_', text, re.MULTILINE)
    if not match:
        print("WARNING: No 'proc do_create_' found. Inserting at end of file.")
        return text + "\n" + block
    return text[:match.start()] + block + text[match.start():]


def replace_project_property(text: str, key: str, var: str) -> str:
    """Replace set_project_property KEY {value} with set_project_property KEY $var."""
    pattern = rf'(set_project_property\s+{key}\s+)\{]^}}]*\}}'
    return re.sub(pattern, rf'\1${var}', text)


def replace_instance_param(text: str, param_key: str, var: str) -> str:
    """Replace set_instance_parameter_value ... {param_key} {value} with $var."""
    pattern = (
        r'(set_instance_parameter_value\s+\S+\s+\{' +
        re.escape(param_key) +
        r'\}\s+)\{[^}]*\}'
    )
    replacement = rf'\1${var}'
    new_text, count = re.subn(pattern, replacement, text)
    if count == 0:
        print(f"WARNING: Parameter '{param_key}' not found in script.")
    return new_text


def main():
    parser = argparse.ArgumentParser(
        description="Insert $argv parameter handling into a Quartus IP TCL script."
    )
    parser.add_argument("input", help="Path to the IP TCL script")
    parser.add_argument(
        "--output", default=None,
        help="Output file path (default: modify input in-place)"
    )
    parser.add_argument(
        "--params", nargs="*", default=[],
        help="Additional set_instance_parameter_value keys to parameterize"
    )
    args = parser.parse_args()

    input_path = Path(args.input)
    if not input_path.exists():
        print(f"ERROR: File not found: {input_path}", file=sys.stderr)
        sys.exit(1)

    text = input_path.read_text()

    # 1. Insert $argv block
    argv_block = build_argv_block(text)
    text = insert_argv_block(text, argv_block)

    # 2. Replace DEVICE and DEVICE_FAMILY
    text = replace_project_property(text, "DEVICE", "device")
    text = replace_project_property(text, "DEVICE_FAMILY", "device_family")

    # 3. Replace requested instance parameters using built-in map
    for param in args.params:
        if param in PARAM_VAR_MAP:
            var = PARAM_VAR_MAP[param]
            text = replace_instance_param(text, param, var)
        else:
            print(
                f"WARNING: '{param}' not in PARAM_VAR_MAP — add it to the map "
                f"or the replacement will be skipped."
            )

    # 4. Write output
    output_path = Path(args.output) if args.output else input_path
    output_path.write_text(text)
    print(f"Written: {output_path}")


if __name__ == "__main__":
    main()
