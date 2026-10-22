#!/usr/bin/env bash
# Installs immutable checker sources into one reusable, ignored directory.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here/../.." && pwd)"
tool_dir="${COMPARATOR_TOOLS:-$repo/.local-check/tools}"
mkdir -p "$tool_dir"
tool_dir="$(cd "$tool_dir" && pwd)"
pin() { python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])' "$here/pins.json" "$1"; }
checkout() {
  local name="$1" url="$2" rev="$3"
  if [[ ! -d "$tool_dir/$name/.git" ]]; then
    git clone --no-checkout "$url" "$tool_dir/$name"
    git -C "$tool_dir/$name" checkout --detach "$rev"
  fi
  test "$(git -C "$tool_dir/$name" rev-parse HEAD)" = "$rev"
  test -z "$(git -C "$tool_dir/$name" status --porcelain)"
}
checkout comparator "$(pin comparator_repository)" "$(pin comparator_commit)"
checkout lean4export "$(pin lean4export_repository)" "$(pin lean4export_commit)"
checkout landrun "$(pin landrun_repository)" "$(pin landrun_commit)"
test "$(cat "$tool_dir/comparator/lean-toolchain")" = "$(pin lean_toolchain)"
test "$(cat "$tool_dir/lean4export/lean-toolchain")" = "$(pin lean_toolchain)"
(cd "$tool_dir/comparator" && lake build comparator)
(cd "$tool_dir/lean4export" && lake build lean4export)
(cd "$tool_dir/landrun" && go build -mod=readonly -o "$tool_dir/landrun-bin" ./cmd/landrun)
printf 'Tools installed in %s\n' "$tool_dir"

