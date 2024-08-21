#!/bin/bash

# Directory containing Python files
DIRECTORY="./" # You can change this to your specific directory

echo "Running Nagini on Python files in $DIRECTORY"

# Iterate over each Python file in the directory
for file in "$DIRECTORY"/*.py; do
  if [[ -f "$file" ]]; then
    echo "Running Nagini on $file"
    nagini "$file"
  else
    echo "No Python files found in $DIRECTORY"
  fi
done