#!/bin/bash

# This script builds the project's web page, including documentation.

set -o pipefail # stop if any command fails

lake exe cache get
lake -R -Kenv=dev build Analysis:docs
lake build
lake build :literateHtml
