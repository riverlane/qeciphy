#!/bin/bash
set -e 
set -o pipefail

echo "=== QECIPHY Multi-Platform UVM VCS Simulation ==="

echo "Purging modules..."
module purge

echo "Loading Vivado and VCS..."
module load xilinx/vivado/2024.1
module load synopsys/vcs
module load synopsys/verdi
bash uvm/regression_run.sh
