#!/bin/sh
set -eu
cd "$(dirname "$0")/.."
mkdir -p .lake/build/lib/lean
lake env lean -j 2 -M 8192 -o .lake/build/lib/lean/Erdos12AllParts.olean Erdos12AllParts.lean
lake env lean Audit.lean
lake env lean -j 2 -M 8192 -o .lake/build/lib/lean/Submission.olean Submission.lean
