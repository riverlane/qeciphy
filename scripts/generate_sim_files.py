#!/usr/bin/env python3
"""
QECIPHY Simulation File Generator

This script generates simulation files for Xilinx IP cores (XCI files) by:
1. Running Vivado export_simulation to create simulator specific scripts
2. Parsing the generated shell scripts to extract HDL source files and include directories
3. Organizing the files in a flattened structure under tb/generated_sim_files/
4. Creating a simulation file list (generated_sim.f) for use with simulators
"""

import argparse
import logging
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path
from typing import List, Tuple


# Configuration constants
VIVADO_SIM_EXPORT_TCL = "scripts/vivado_sim_export.tcl"
GENERATED_SIM_FILES_DIR = "tb/generated_sim_files"
IP_SIM_EXPORT_DIR = "run/ip_sim_export"
GENERATED_SIM_F = "generated_sim.f"
XCI_DIR = "xci"

# HDL file extensions in priority order (longest first to avoid partial matches)
HDL_EXTENSIONS = ("vhdl", "vhd", "sv", "v")


def setup_logging() -> None:
    """Configure logging for the application."""
    logging.basicConfig(
        level=logging.INFO,
        format='%(levelname)s: %(message)s',
        stream=sys.stdout
    )


def run_vivado_generate_sim(part: str, xci_file: str, simulator: str, 
                          export_base_dir: str) -> bool:
    """
    Run Vivado to generate simulation files for a single XCI file.
    
    Args:
        part: FPGA part number (e.g., "xc7z030ffg676-3")
        xci_file: Path to the XCI file
        simulator: Target simulator (e.g., "vcs")
        export_base_dir: Base directory for exported simulation files
        
    Returns:
        bool: True if Vivado completed successfully, False otherwise
        
    Raises:
        FileNotFoundError: If the TCL script is not found
    """
    if not Path(VIVADO_SIM_EXPORT_TCL).exists():
        raise FileNotFoundError(f"TCL script not found: {VIVADO_SIM_EXPORT_TCL}")
        
    cmd = [
        "vivado", 
        "-mode", "batch", 
        "-source", VIVADO_SIM_EXPORT_TCL,
        "-tclargs", part, xci_file, simulator, export_base_dir
    ]
    
    logging.info(f"Running Vivado: {' '.join(cmd)}")
    
    try:
        result = subprocess.run(
            cmd, 
            stdout=subprocess.PIPE, 
            stderr=subprocess.PIPE, 
            universal_newlines=True, 
            check=True
        )
        logging.info("Vivado completed successfully")
        return True
        
    except subprocess.CalledProcessError as e:
        logging.error(f"Vivado failed with exit code {e.returncode}")
        if e.stdout:
            logging.error(f"Stdout: {e.stdout}")
        if e.stderr:
            logging.error(f"Stderr: {e.stderr}")
        return False


def parse_simulation_script(sh_path: str) -> Tuple[List[str], List[str]]:
    """
    Parse VCS simulation script to extract HDL files and include directories.
    
    This function parses the compile() function in Vivado generated simulator specific 
    shell scripts to extract HDL source files and include directory paths.
    
    Args:
        sh_path: Path to the VCS shell script
        
    Returns:
        Tuple containing:
        - List of HDL source file paths
        - List of include directory paths
        
    Raises:
        FileNotFoundError: If the shell script is not found
        IOError: If the script cannot be read
    """
    if not Path(sh_path).exists():
        raise FileNotFoundError(f"Simulation script not found: {sh_path}")
        
    try:
        with open(sh_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except IOError as e:
        logging.error(f"Failed to read simulation script {sh_path}: {e}")
        raise
    
    # Find the compile() function section by looking for the function definition
    compile_start = content.find('compile()')
    
    if compile_start == -1:
        logging.warning(f"Could not find compile() function in {sh_path}")
        return [], []
    
    # Find the opening brace after compile()
    brace_start = content.find('{', compile_start)
    if brace_start == -1:
        logging.warning(f"Could not find opening brace for compile() function in {sh_path}")
        return [], []
    
    # Find the matching closing brace
    brace_count = 0
    compile_end = brace_start
    for i, char in enumerate(content[brace_start:], brace_start):
        if char == '{':
            brace_count += 1
        elif char == '}':
            brace_count -= 1
            if brace_count == 0:
                compile_end = i + 1
                break
    else:
        # If we reach here, braces are unbalanced - this is an error
        raise IOError(f"Unbalanced braces in compile() function in {sh_path}")
    
    compile_section = content[compile_start:compile_end]
    
    # Extract HDL files using regex
    extensions_pattern = "|".join(HDL_EXTENSIONS)
    file_pattern = rf'["\']([^"\']*\.(?:{extensions_pattern}))["\']|([^"\'\s]*\.(?:{extensions_pattern}))'
    matches = re.findall(file_pattern, compile_section)
    
    sim_files = []
    for match in matches:
        # re.findall with multiple groups returns tuples, get the non-empty one
        file_path = match[0] if match[0] else match[1]
        if file_path and not file_path.startswith('$'):  # Skip shell variables
            sim_files.append(file_path)
    
    # Extract include directories
    incdir_pattern = r'\+incdir\+["\']?([^"\'\s]+)["\']?'
    incdir_matches = re.findall(incdir_pattern, compile_section)
    
    include_dirs = []
    for incdir in incdir_matches:
        if incdir and not incdir.startswith('$'):  # Skip shell variables
            include_dirs.append(incdir)
    
    # Remove duplicates while preserving order
    sim_files = list(dict.fromkeys(sim_files))
    include_dirs = list(dict.fromkeys(include_dirs))
    
    logging.debug(f"Found {len(sim_files)} simulation files and {len(include_dirs)} include directories")
    
    return sim_files, include_dirs



def copy_simulation_files(sim_files: List[str], script_dir: str, output_dir: str) -> int:
    """
    Copy simulation files to the output directory.
    
    Args:
        sim_files: List of simulation file paths
        script_dir: Directory containing the simulation script (for path resolution)
        output_dir: Destination directory for copied files
        
    Returns:
        int: Number of files successfully copied
    """
    copied_count = 0
    
    for sim_file in sim_files:
        logging.debug(f"Processing simulation file: {sim_file}")
        
        # Resolve file path
        if os.path.isabs(sim_file):
            abs_sim_file = sim_file
        else:
            abs_sim_file = os.path.abspath(os.path.join(script_dir, sim_file))
        
        if os.path.exists(abs_sim_file):
            dest_path = os.path.join(output_dir, os.path.basename(sim_file))
            try:
                shutil.copy2(abs_sim_file, dest_path)
                logging.debug(f"Copied {abs_sim_file} to {dest_path}")
                copied_count += 1
            except IOError as e:
                logging.error(f"Failed to copy {abs_sim_file}: {e}")
        else:
            logging.warning(f"Source file not found: {abs_sim_file}")
    
    return copied_count


def copy_include_files(include_dirs: List[str], script_dir: str, output_dir: str) -> int:
    """
    Copy include files from include directories to the output directory.
    
    Args:
        include_dirs: List of include directory paths
        script_dir: Directory containing the simulation script (for path resolution)
        output_dir: Destination directory for copied include files
        
    Returns:
        int: Number of files successfully copied
    """
    if not include_dirs:
        return 0
    
    includes_dir = os.path.join(output_dir, "includes")
    os.makedirs(includes_dir, exist_ok=True)
    
    copied_count = 0
    
    for include_dir in include_dirs:
        logging.debug(f"Processing include directory: {include_dir}")
        
        # Resolve include directory path
        if os.path.isabs(include_dir):
            abs_include_dir = include_dir
        else:
            abs_include_dir = os.path.abspath(os.path.join(script_dir, include_dir))
        
        if os.path.exists(abs_include_dir) and os.path.isdir(abs_include_dir):
            try:
                for include_file in os.listdir(abs_include_dir):
                    src_file = os.path.join(abs_include_dir, include_file)
                    if os.path.isfile(src_file):
                        dest_file = os.path.join(includes_dir, include_file)
                        shutil.copy2(src_file, dest_file)
                        logging.debug(f"Copied include file {src_file} to {dest_file}")
                        copied_count += 1
            except OSError as e:
                logging.error(f"Failed to process include directory {abs_include_dir}: {e}")
        else:
            logging.warning(f"Include directory not found or not a directory: {abs_include_dir}")
    
    return copied_count


def write_simulation_file_list(output_file: str, xci_files_dir: str, sim_files: List[str], 
                             include_dirs: List[str]) -> None:
    """
    Write simulation file paths to the generated simulation file list.
    
    Args:
        output_file: Path to the output file list
        xci_files_dir: Directory containing the XCI simulation files
        sim_files: List of simulation file paths
        include_dirs: List of include directory paths
    """
    try:
        with open(output_file, 'a', encoding='utf-8') as gen_f:
            # Write include directories
            if include_dirs:
                includes_path = os.path.join(xci_files_dir, 'includes')
                gen_f.write(f"+incdir+{includes_path}\n")
            
            # Write source files
            for sim_file in sim_files:
                dest_file_path = os.path.join(xci_files_dir, os.path.basename(sim_file))
                gen_f.write(f"{dest_file_path}\n")
    except IOError as e:
        logging.error(f"Failed to write to simulation file list {output_file}: {e}")
        raise


def process_xci_file(xci_file: str, part: str, simulator: str) -> bool:
    """
    Process a single XCI file to generate simulation files.
    
    Args:
        xci_file: Path to the XCI file
        part: FPGA part number
        simulator: Target simulator
        
    Returns:
        bool: True if processing was successful, False otherwise
    """
    xci_name = Path(xci_file).stem
    logging.info(f"Processing XCI file: {xci_file} (name: {xci_name})")
    
    # Create output directory
    xci_files_dir = os.path.join(GENERATED_SIM_FILES_DIR, xci_name)
    os.makedirs(xci_files_dir, exist_ok=True)
    logging.debug(f"Created directory: {xci_files_dir}")
    
    # Export directory for Vivado
    export_base_dir = os.path.join(IP_SIM_EXPORT_DIR, xci_name)
    
    # Run Vivado to generate simulation files
    if not run_vivado_generate_sim(part, xci_file, simulator, export_base_dir):
        logging.error(f"Failed to generate simulation files for {xci_name}")
        return False
    
    # Parse the generated simulation script
    sh_path = os.path.join(export_base_dir, f"temp_project_{xci_name}", "sim_export", 
                          xci_name, simulator, f"{xci_name}.sh")
    
    if not os.path.exists(sh_path):
        logging.error(f"Simulation script not found at: {sh_path}")
        return False
    
    logging.debug(f"Parsing simulation script: {sh_path}")
    
    try:
        sim_files, include_dirs = parse_simulation_script(sh_path)
    except (FileNotFoundError, IOError) as e:
        logging.error(f"Failed to parse simulation script: {e}")
        return False
    
    if not sim_files:
        logging.warning(f"No simulation files found for {xci_name}")
        return True
    
    # Copy files
    script_dir = os.path.dirname(sh_path)
    
    sim_copied = copy_simulation_files(sim_files, script_dir, xci_files_dir)
    inc_copied = copy_include_files(include_dirs, script_dir, xci_files_dir)
    
    logging.info(f"Copied {sim_copied} simulation files and {inc_copied} include files for {xci_name}")
    
    # Update simulation file list
    try:
        write_simulation_file_list(GENERATED_SIM_F, xci_files_dir, sim_files, include_dirs)
    except IOError as e:
        logging.error(f"Failed to update simulation file list: {e}")
        return False
    
    return True


def cleanup_temp_directories() -> None:
    """Clean up temporary export directories."""
    if os.path.exists(IP_SIM_EXPORT_DIR):
        try:
            shutil.rmtree(IP_SIM_EXPORT_DIR)
            logging.debug(f"Cleaned up temporary directory: {IP_SIM_EXPORT_DIR}")
        except OSError as e:
            logging.warning(f"Failed to clean up temporary directory {IP_SIM_EXPORT_DIR}: {e}")


def main() -> int:
    """
    Main function to process all XCI files and generate simulation files.
    
    Returns:
        int: Exit code (0 for success, 1 for failure)
    """
    parser = argparse.ArgumentParser(
        description="Generate simulation files for XCI files in QECIPHY",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s --part xc7z030ffg676-3 --simulator vcs  # Process with Zynq-7000 part and VCS
        """
    )
    
    parser.add_argument(
        '--part', 
        required=True,
        help='FPGA part number (e.g., xc7z030ffg676-3, xc7z020clg484-1, xczu9eg-ffvb1156-2-e)'
    )
    parser.add_argument(
        '--simulator', 
        required=True,
        choices=['vcs'],
        help='Target simulator (vcs)'
    )
    
    args = parser.parse_args()
    
    # Setup logging
    setup_logging()
    
    logging.info("Starting QECIPHY simulation file generation")
    
    # Check if XCI directory exists
    if not os.path.exists(XCI_DIR):
        logging.error(f"XCI directory not found: {XCI_DIR}")
        return 1
    
    # Create output directories
    os.makedirs(GENERATED_SIM_FILES_DIR, exist_ok=True)
    os.makedirs(IP_SIM_EXPORT_DIR, exist_ok=True)
    
    # Remove existing simulation file list
    if os.path.exists(GENERATED_SIM_F):
        os.remove(GENERATED_SIM_F)
    
    # Find XCI files
    xci_files = [f for f in os.listdir(XCI_DIR) if f.endswith('.xci')]
    
    if not xci_files:
        logging.warning(f"No XCI files found in {XCI_DIR}")
        return 0
    
    logging.info(f"Found {len(xci_files)} XCI files to process")
    
    # Process each XCI file
    success_count = 0
    for xci_file in xci_files:
        xci_path = os.path.join(XCI_DIR, xci_file)
        if process_xci_file(xci_path, args.part, args.simulator):
            success_count += 1
    
    # Clean up temporary directories
    cleanup_temp_directories()
    
    logging.info(f"Successfully processed {success_count}/{len(xci_files)} XCI files")
    
    if success_count == len(xci_files):
        logging.info("All XCI files processed successfully")
        return 0
    else:
        logging.error("Some XCI files failed to process")
        return 1


if __name__ == "__main__":
    sys.exit(main())