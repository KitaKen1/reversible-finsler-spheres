# Lean proof with Comparator interface

The proof entry is [FCExactSolution.lean](FCExactSolution.lean).
The independent reference is [FCExactChallenge.lean](FCExactChallenge.lean).
Both use the exact mathematical definitions and n ≥ 3 target type extracted
from the single-file FC submission. Only the reference has a proof placeholder.
The solution connects these definitions to the underlying proof through
[FCSolution.lean](FCSolution.lean).

```bash
lake exe cache get
lake build
```

The default build checks `FCExactSolution` and `FCExactAudit`.
For serial project compilation, use
`python3 scripts/build-serial.py --project lean FCExactSolution FCExactAudit`
from the repository root. The complete project sources and pinned dependencies
are included here; this directory can also be copied out on its own.

[FCImplications.lean](FCImplications.lean) connects the four FC statements.
[FCTwoSphere.lean](FCTwoSphere.lean) and
[HingstonArithmetic.lean](HingstonArithmetic.lean) contain the proved
length-spectrum and point-covering criteria for the two-sphere development.
Their geometric hypotheses are still explicit; they do not prove the
unconditional n = 2 assertion. Build these historical modules explicitly if needed.

See [Comparator instructions](comparator/README.md), the
[publication README](../README.md) and the
[record of checks actually run](../verification/STATUS.md).

