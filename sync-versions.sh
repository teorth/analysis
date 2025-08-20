#!/bin/bash

set -e

# This repository uses the library `SubVerso` to extract information
# from the code respository and use it in the website. SubVerso is
# compatible with every Lean release, allowing the book to use a
# different version than the Mathlib development. The versions of the
# library must match, however.
#
# The CI script '.github/workflows/check-version-consistency.yml' makes
# sure that the versions match. If they do not, this script can be used
# to fix the situation.

echo "Extracting SubVerso version from book/lake-manifest.json..."
if ! expected_version=$(jq -r '.packages[] | select(.name == "subverso") | .rev' book/lake-manifest.json 2>/dev/null); then
    echo "Error: Failed to extract 'subverso' hash from book/lake-manifest.json"
    exit 1
fi

if [[ -z "$expected_version" || "$expected_version" == "null" ]]; then
    echo "Error: No 'subverso' package found or empty hash in book/lake-manifest.json"
    exit 1
fi

echo "Version: $expected_version"

# Check if analysis/lake-manifest.json exists
if [[ ! -f "analysis/lake-manifest.json" ]]; then
    echo "Error: analysis/lake-manifest.json does not exist"
    exit 1
fi

# Get current version from analysis/lake-manifest.json
if ! current_version=$(jq -r '.packages[] | select(.name == "subverso") | .rev' analysis/lake-manifest.json 2>/dev/null); then
    echo "Error: Failed to extract 'subverso' hash from analysis/lake-manifest.json"
    exit 1
fi

if [[ -z "$current_version" || "$current_version" == "null" ]]; then
    echo "Error: No 'subverso' package found in analysis/lake-manifest.json"
    exit 1
fi

echo "Version in analysis/lake-manifest.json: $current_version"

# Check if versions already match
if [[ "$current_version" == "$expected_version" ]]; then
    echo "Versions already match. No changes needed."
    exit 0
fi


# Use sed to replace the current hash with the expected hash
echo "Updating subverso version in analysis/lake-manifest.json..."
if ! sed -i.tmp "s/$current_version/$expected_version/g" analysis/lake-manifest.json; then
    echo "Error: sed replacement failed"
    # Restore from sed's backup if it exists
    if [[ -f "analysis/lake-manifest.json.tmp" ]]; then
        mv analysis/lake-manifest.json.tmp analysis/lake-manifest.json
    fi
    exit 1
fi

# Verify the change was made correctly
if ! updated_version=$(jq -r '.packages[] | select(.name == "subverso") | .rev' analysis/lake-manifest.json 2>/dev/null); then
    echo "Error: Failed to verify updated hash"
    mv analysis/lake-manifest.json.backup analysis/lake-manifest.json
    exit 1
fi

if [[ "$updated_version" != "$expected_version" ]]; then
    echo "Error: Hash update verification failed"
    echo "Expected: $expected_version"
    echo "Found: $updated_version"
    # Restore from sed's backup if it exists
    if [[ -f "analysis/lake-manifest.json.tmp" ]]; then
        mv analysis/lake-manifest.json.tmp analysis/lake-manifest.json
    fi
    exit 1
fi

# Count the number of changes made using sed's backup
changes=$(diff -u analysis/lake-manifest.json.tmp analysis/lake-manifest.json | grep "^[-+]" | grep -v "^[-+][-+][-+]" | wc -l)
if [[ $changes -ne 2 ]]; then
    echo "Warning: Expected exactly 2 diff lines (one removal, one addition), but found $changes"
    echo "This might indicate multiple occurrences of the hash were replaced - is there a dependency hash collision?"
fi

# Clean up sed's backup file
rm -f analysis/lake-manifest.json.tmp

echo "✓ Successfully updated subverso version in analysis/lake-manifest.json"
echo "  From: $current_version"
echo "  To:   $expected_version"
