#!/bin/bash

# This script builds the project's Lean code.

set -e -o pipefail # stop if a command or pipeline fails

lake exe cache get
lake build