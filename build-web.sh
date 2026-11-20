#!/bin/bash

# This script builds the project's web page, including documentation.

set -e -o pipefail # stop if a command or pipeline fails

cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

lake exe cache get
lake -R -Kenv=dev build Analysis:docs
lake build
lake build :literateHtml
