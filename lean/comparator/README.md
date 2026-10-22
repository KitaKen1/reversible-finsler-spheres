# Comparator checks

The primary configuration, [comparator-fc.json](../comparator-fc.json), checks
`ReversibleFinslerSpheres.infinitely_many_prime_closed_geodesics` using the
definitions and full target type extracted from the standalone FC file.
[FCExactSolution.lean](../FCExactSolution.lean) proves this target. Run
`python3 scripts/generate-fc-target.py --check` from the repository root to
verify the extraction. Module visibility and FC metadata are omitted for
compatibility with the existing proof library; the mathematical declarations
are copied unchanged. The other three FC statements are not imported.

The exact-target Linux command sequence is:

```bash
python3 scripts/fetch-target-cache.py --project lean
python3 scripts/build-serial.py --project lean FCExactChallenge
python3 scripts/build-serial.py --project lean FCExactSolution FCExactAudit
bash lean/comparator/install-tools.sh
bash lean/comparator/run-fc-check.sh
```

The [exact-target workflow](../../.github/workflows/fc-target.yml) performs a
source build and invokes the unmodified upstream CLI with real `landrun`.
Its run status is recorded separately from local API checks.
Only the required dependency import closure is cached; compressed downloads
are removed automatically. On the disposable hosted VM, unused preinstalled
SDKs are removed before downloading dependencies, requiring at least 24 GiB
of disk headroom. The runner preparation script refuses local/self-hosted use.
Project build artifacts are preserved even after a build failure, so later
runs can validate and reuse unchanged artifacts instead of restarting every
module. The cache key fixes the toolchain, dependency pins and build settings;
Lake validates source traces, and `runtime-results/fc-build-cache.json` records
whether the hosted build started fresh or incrementally. The full Comparator
kernel replay is required in either case.

For an existing matching local build, use:

```bash
python3 scripts/check-fc-comparator.py \
  --source-build /path/to/existing/Lean \
  --comparator /path/to/pinned/comparator \
  --exporter /path/to/pinned/lean4export/.lake/build/bin/lean4export \
  --replay-seconds 3600
```

This compiles the exact target and audit separately in both proof variants,
then runs upstream type/definition comparison, axiom checking and built-in
kernel replay. Every phase must pass. Temporary oleans and export streams
are removed on success or failure. The source-hashed receipt is
`verification/local/fc-target-comparator-receipt.json`. The reused core oleans
are not a fresh source build; the local API route has no OS sandbox.

## Earlier coordinate targets

The configuration compares two theorem names in `Challenge` and `FCSolution`.
The fixed definitions have no holes; `definition_names` is empty.
The only permitted target axioms are `propext`, `Classical.choice`, `Quot.sound`.

## Linux CLI (full upstream path)

Install Lean/elan and Go 1.24 or newer, then from the repository root:

```bash
cd lean
lake exe cache get
cd ..
python3 scripts/build-serial.py --project lean Challenge
python3 scripts/build-serial.py --project lean
bash lean/comparator/install-tools.sh
bash lean/comparator/run-check.sh
```

The scripts use immutable revisions in [pins.json](pins.json), including a
Comparator and lean4export that both use Lean 4.35.0-rc3 without patching.
The CLI compares target types and dependent definitions, audits target axioms
and replays the exported solution in Lean's built-in kernel. Real `landrun`
is required by this path. Nanoda / a second kernel implementation is not used.

Build the trusted challenge before loading a solution from an untrusted party.
This repository contains the author's solution, not an arbitrary-submission
sandbox service.

The CI workflow is prepared for manual dispatch. Its existence does not imply
a completed hosted run; consult [the actual status](../../verification/STATUS.md).

## Local incremental check

To avoid duplicating a large dependency cache, the publication was also tested
against a matching existing project build:

```bash
python3 scripts/local-check.py \
  --source-build /path/to/existing/Lean \
  --fc-source /path/to/formal-conjectures \
  --comparator /path/to/pinned/comparator \
  --exporter /path/to/pinned/lean4export/.lake/build/bin/lean4export \
  --replay-seconds 180
```

The script checks source hashes against both shipped trees, compiles the
publication entry points, the FC draft and specification checks, then exports
the challenge and solution. [CompareExports.lean](CompareExports.lean) calls
the **actual pinned upstream** `Comparator.compareAt` and
`Comparator.checkAxioms` APIs. A separate bounded attempt calls the upstream
built-in kernel replay.

These local checks have **no OS sandbox** and reuse existing dependency/proof
oleans. Source-hash agreement is not proof that the reused oleans were rebuilt
from that source in this run. The structural comparison, axiom audit and
kernel replay each have their own status; a timeout does not count as a pass.
A successful partial local API check is not labeled a successful full CLI run.

Runtime artifacts use a single ignored `.local-check/` directory. Export
streams are deleted after the comparison attempt; the script does not create
whole-project temporary rebuild copies. Local evidence is written under
`verification/local/`; after intentionally rerunning it, the publication
manifest must be resealed to describe the new evidence.

