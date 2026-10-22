# Verification evidence

- [STATUS.md](STATUS.md): scope and outcome of checks actually performed.
- [STATEMENT-CORRESPONDENCE.md](STATEMENT-CORRESPONDENCE.md): prose-to-Lean review.
- [local/receipt.json](local/receipt.json): commands' exit status, duration and log locations.
- [local/fc-target-comparator-receipt.json](local/fc-target-comparator-receipt.json): exact FC n ≥ 3 target, both proof variants, upstream Comparator comparison and built-in kernel replay; each phase has its own measured outcome.
- [local/fc-target-before-memory-refactor/receipt.json](local/fc-target-before-memory-refactor/receipt.json): historical exact-target run and timeout before the proof-only memory refactor.
- [local/fc-kernel-time-budget-extension.json](local/fc-kernel-time-budget-extension.json): the local replay's bounded timeout extension and final monitor resumption.
- [local/native-suffix-memory-receipt.json](local/native-suffix-memory-receipt.json): proof-only refactoring of the source-build memory failure, with before/after source hashes and measured compilation.
- [local/memory-regression-receipt.json](local/memory-regression-receipt.json): bounded recompilation of the replacement, a direct dependent and the exact FC solution/audit in both variants.
- [local/fc-four-statements-receipt.json](local/fc-four-statements-receipt.json): updated four-statement FC elaboration, type readback and round-metric check, with input hashes.
- [FCStatementReadback.lean](FCStatementReadback.lean): the four standalone FC types and metadata, checked with Mathlib dependencies only.
- [FCDefinitionCorrespondence.lean](FCDefinitionCorrespondence.lean): equivalence of the independent FC definitions and proof targets, round-metric nonvacuity, and ten transitive axiom audits.
- [DIMENSION-TWO.md](DIMENSION-TWO.md): proved surface-proof components, arithmetic proof and remaining geometric obligations.
- [TwoSphereReadback.lean](TwoSphereReadback.lean): the n = 2 criteria, repeated-loop and connector families, relative pause removal, explicit base-slide filling, critical-value extraction, nonzero local critical classes, excision, polygon-to-loop comparison, actual geodesic splitting models, small maximal disks from local product forms and kernel maxima, spectral coordinates, actual nonlinear phase charts and transverse Hessian splitting, transverse iteration with kernel equivalence and reduced-maximum transport along stable odd progressions, actual local energy retractions and point-critical homology injections, stable base iterates for zero mean index, energy-decreasing deformations, actual iteration isomorphisms and the stable base-period rotation action, bounded-chain-index vanishing, actual zero-mean index vanishing and positive-index growth, original-geodesic isomorphisms and rotation action without a stabilizing base iterate, the rotation-invariant local detector and mapping-torus fibre injection, concrete degenerate saddle, phase and S² iteration examples, and 288 transitive axiom audits in each variant.
- [local/two-sphere-receipt.json](local/two-sphere-receipt.json): source hashes, compilation and audit results for the new components in both variants.
- [proof-source-manifest.json](proof-source-manifest.json): SHA-256 of each original proof file.
- [../PUBLICATION-MANIFEST.json](../PUBLICATION-MANIFEST.json): sealed publication inventory.

Reproduce static checks with `python3 scripts/check-package.py` from the root.
Local incremental compilation and optional Comparator checks are documented in
[the Comparator README](../lean/comparator/README.md).
The two-sphere components can be checked separately with
`python3 scripts/check-two-sphere.py --source-build /path/to/matching/Lean --record`.

After intentionally changing publication documentation or rerunning local checks,
use `python3 scripts/seal-package.py`, then run the checker again. Sealing records
bytes; it does not itself validate a proof or update the original proof-source pins.
The included local receipt must not be relabeled as GitHub CI or independent
human review.
