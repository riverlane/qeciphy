#!/bin/bash
set -e 
set -o pipefail 

echo "=== QECIPHY Format Check ==="

echo "Purging modules..."
module purge

echo "Loading Verible formatter..."
module load verible/verible

echo "Checking if code is properly formatted..."

# Run format and capture any changes
echo "Running make format..."
make format

# Check if there are any uncommitted changes after formatting
if ! git diff --quiet --exit-code; then
    echo ""
    echo "FORMATTING CHECK FAILED!"
    echo ""
    echo "The following files need formatting:"
    git diff --name-only
    echo ""
    echo "Please run 'make format' locally and commit the changes:"
    echo "  make format"
    echo "  git add ."
    echo "  git commit -m 'Applied code formatting'"
    echo "  git push"
    echo ""
    exit 1
fi

echo "All files are properly formatted!"
