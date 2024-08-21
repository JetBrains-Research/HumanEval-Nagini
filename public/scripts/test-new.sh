#!/bin/bash
set -eou pipefail

DIRECTORY="./Bench" # You can change this to your specific directory

# Timeout duration in seconds
TIMEOUT_DURATION=600

file_count=0
echo "New files found:"
for f in $1; do
    # Check if the file is in the known directory
    if [[ $f == $directory/* ]]; then
        if [[ $f == *.py ]]; then
            echo $f
            file_count=$((file_count+1))
        fi
    fi
done

echo "Staring the check"
for f in $1
do
    # Check if the file is in the known directory
    if [[ $f == $directory/* ]]; then
        if [[ $f == *.py ]]; then
            file_no=$((file_no+1))
            echo "Running dafny on $(basename "$f") ($file_no/$file_count)"
            timeout "$TIMEOUT_DURATION" nagini "$file"
        fi
    fi
done

# # Iterate over each Python file in the directory
# for file in "$DIRECTORY"/*.py; do
#   if [[ -f "$file" ]]; then
#     echo "Running Nagini on $file"
#     timeout "$TIMEOUT_DURATION" nagini "$file"
#   else
#     echo "No Python files found in $DIRECTORY"
#   fi
# done