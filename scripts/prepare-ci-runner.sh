#!/usr/bin/env bash
# Only for a disposable GitHub-hosted Linux VM, never a user's checkout/host.
set -euo pipefail
test "${GITHUB_ACTIONS:-}" = true
test "${1:-}" = github-hosted
test "$(uname -s)" = Linux
mkdir -p runtime-results
exec > >(tee runtime-results/fc-runner-resources.log) 2>&1
df -h "$RUNNER_TEMP"
free -h
# These preinstalled SDKs are unused by Lean, the C toolchain and Go.
unused_sdks=(/usr/local/lib/android /usr/share/dotnet /usr/local/.ghcup
             /opt/ghc /opt/hostedtoolcache/CodeQL)
sudo du -sk "${unused_sdks[@]}" 2>/dev/null || true
sudo rm -rf "${unused_sdks[@]}"
available_kib=$(df -Pk "$RUNNER_TEMP" | awk 'NR == 2 {print $4}')
# A selected import closure is fetched instead of the whole Mathlib cache.
# Report exact KiB: df -h rounds 29.x GiB to "30G".
echo "Available disk after cleanup: $available_kib KiB"
if [ "$available_kib" -lt 25165824 ]; then
  echo "Fewer than 24 GiB free after removing unused SDKs" >&2
  df -h "$RUNNER_TEMP"
  exit 1
fi
# Keep the hosted image's existing swap; do not reserve more disk for swap.
df -h "$RUNNER_TEMP"
free -h
