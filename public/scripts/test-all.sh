#!/bin/bash
set -eou pipefail

# Directory containing Python files
DIRECTORY="./Bench" # You can change this to your specific directory

# Timeout duration in seconds
TIMEOUT_DURATION=1200

echo "Running Nagini on Python files in $DIRECTORY"

# Iterate over each Python file in the directory
for file in "$DIRECTORY"/*.py; do
  if [[ -f "$file" ]]; then
    echo "Running Nagini on $file"
    # rm -rf .mypy_cache
    timeout "$TIMEOUT_DURATION" nagini "$file"
  else
    echo "No Python files found in $DIRECTORY"
  fi
done