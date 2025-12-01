#!/bin/bash
set -e 
set -o pipefail

echo "=== QECIPHY Multi-Platform VCS Simulation ==="

echo "Purging modules..."
module purge

echo "Loading Vivado and VCS..."
module load xilinx/vivado/2024.1
module load synopsys/vcs
module load synopsys/verdi

# Test all supported platforms
PROFILES=("zcu216" "zcu106" "kasliSoC")

for profile in "${PROFILES[@]}"; do
    echo ""
    echo "--- Testing profile: $profile ---"

    echo "Cleaning previous builds..."
    make distclean
    
    echo "Generating XCI cores for $profile..."
    make generate-xci OPT_PROFILE=$profile OPT_SIM_FILES=true
    SEED=$RANDOM

    echo "Running UVM VCS simulation for $profile..."
    make uvm_sim OPT_TOP=qeciphy_uvmtb OPT_TEST=qeciphy_txrx_test OPT_PROFILE=$profile OPT_SEED=$SEED
    if [[ ! -f "qeciphy_txrx_test.log" ]]; then
            echo "Log file not found! Test qeciphy_txrx_test may have failed to run."
            exit 1
    fi

    if grep -q "***FAILED***" "qeciphy_txrx_test.log"; then
        echo "qeciphy_txrx_test failed"
        FAIL=$((FAIL+1))
    else
        echo "qeciphy_txrx_test passed"
        PASS=$((PASS+1))
    fi

    echo "$profile UVM VCS simulation completed successfully!"
done

echo ""
echo "All platform UVM VCS simulations completed successfully!"