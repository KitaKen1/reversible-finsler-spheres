# Standalone Lean proof without Comparator

This directory contains the same `Finsler/` sources, fixed target definitions,
proved targets, axiom audit and statement readback as `../lean/`.
It does not contain or import a Comparator challenge.
The main entry, [FCExactSolution.lean](FCExactSolution.lean), proves the n ≥ 3
target using the exact mathematical definitions from the single-file FC
submission. [FCExactAudit.lean](FCExactAudit.lean) checks its complete axiom closure.

```bash
lake exe cache get
lake build
```

The default `lake build` targets are `FCExactSolution` and `FCExactAudit`.
The separately available `FCTwoSphere` contains proved length-spectrum and point-covering
criteria with explicit geometric hypotheses, not a complete n = 2 proof.
Keep `lake-manifest.json`,
`lean-toolchain` and `LICENSE` with this directory when copying it out.

The allowed transitive target axioms are `propext`, `Classical.choice` and
`Quot.sound`. The publication-level checker verifies byte identity of all
shared proof sources between the two variants.

