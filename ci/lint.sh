#!/bin/bash
set -e
set -o pipefail 

echo "=== QECIPHY Linting ==="

echo "Purging modules..."
module purge

echo "Loading Verilator..."
module load verilator/verilator

echo "Running render..."
make render-design OPT_PROFILE=zcu216

echo "Running lint..."
make lint

echo "Linting completed successfully!"
