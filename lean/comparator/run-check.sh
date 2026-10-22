#!/usr/bin/env bash
# Linux production path: actual upstream CLI and real Landlock sandbox.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
tool_dir="${COMPARATOR_TOOLS:-$repo/.local-check/tools}"
tool_dir="$(cd "$tool_dir" && pwd)"
test "$(uname -s)" = Linux
export COMPARATOR_LANDRUN="$tool_dir/landrun-bin"
export COMPARATOR_LEAN4EXPORT="$tool_dir/lean4export/.lake/build/bin/lean4export"
test -x "$COMPARATOR_LANDRUN"
test -x "$COMPARATOR_LEAN4EXPORT"
mkdir -p "$repo/runtime-results"
cd "$repo/lean"
lake env "$tool_dir/comparator/.lake/build/bin/comparator" comparator.json 2>&1 |
  tee "$repo/runtime-results/comparator.log"
lake env lean -M4096 -j2 -DElab.async=false FCAudit.lean 2>&1 |
  tee "$repo/runtime-results/axioms.log"
lake env lean -M4096 -j2 -DElab.async=false SpecificationReadback.lean 2>&1 |
  tee "$repo/runtime-results/specification.log"

