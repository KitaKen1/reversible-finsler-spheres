# Natural-language / Lean statement correspondence

**Review date:** 21 October 2026. **Reviewer:** Codex, local AI-assisted
definition review with executable Lean readback. This document is not a
human sign-off or an upstream Formal Conjectures acceptance.

The natural-language claim is [PROBLEM.md](../PROBLEM.md). The machine target
is [FCSolution.lean](../lean/FCSolution.lean), using the fixed
[FCTargetDefinitions.lean](../lean/FCTargetDefinitions.lean).

## Correspondence

| Natural-language phrase | Actual Lean object / condition | Executable or source evidence |
| --- | --- | --- |
| Every dimension n ≥ 3 | `(n : ℕ) (hn : 3 ≤ n)` | Complete target type is printed by `FCAudit.lean`; no hidden section hypotheses |
| Standard sphere Sⁿ | Unit sphere in `EuclideanSpace ℝ (Fin (n + 1))` | Definitional equality in `SpecificationReadback.lean` |
| Tangent bundle of that sphere | `TangentBundle (𝓡 n) (Sphere n)` and `TangentSpace (𝓡 n) x` | `Finsler/Definitions/Sphere.lean` |
| Finsler metric | `ReversibleMetric n`: continuous value, zero at zero, positive off zero, nonnegative positive homogeneity | Structure fields and executable field projections |
| Smooth off the zero section | `ContMDiffOn … ∞ value {p | p.2 ≠ 0}` | Smooth field readback; the manifold and slit bundle are actual definitions |
| Strong convexity | Positive second Fréchet derivative of ½F² on every nonzero direction at every nonzero velocity | The full Hessian expression is checked, not an opaque convexity flag |
| Reversibility | `F.value ⟨x, -v⟩ = F.value ⟨x, v⟩` | Executable projection of the reversible field |
| Smooth closed geodesic | Smooth one-periodic sphere loop, nonzero actual velocity, `CoordinateEuler F γ` | Expanded published image set; actual chart residual and coordinate Lagrangian readback |
| Ordinary geodesic equation | Position derivative minus the time derivative of momentum for F² is zero in each relevant chart | `coordinateResidual`, `coordinateLagrangian_eq`; no synthetic substitute for the geodesic equation |
| Equivalent variational meaning | Zero derivative at zero of actual integral energy under every smooth periodic family through γ | `HasDerivAt … 0 0`; `assertion_iff` and equality of ordinary/variational image sets |
| Prime | Every positive period T satisfies 1 ≤ T, and the curve already has period 1 | `Primitive` unfolded in executable readback |
| Geometrically distinct | Equality / inequality of `Set.range γ` | Target is a set of subsets of the sphere, not a set of parameterized curves |
| Iteration, phase and reversal do not create a new image | Three image-equality theorems for positive iteration, shift and reverse | Explicit executable applications in `SpecificationReadback.lean` |
| Infinitely many | `(PrimeClosedGeodesicImages F).Infinite` | Full target type, definitional set expansion and equality with ordinary `primeImages` |
| Every such metric; no genericity assumption | Only dimension, its lower bound and the metric are theorem arguments | Printed target types; round metric establishes `Nonempty (ReversibleMetric n)` |

The two final theorem statements have no extra hypotheses for filling bounds,
resonance, a chosen prime geodesic, finiteness of prime images, or an
unconstructed topology interface. Such conditional intermediate arguments
are discharged in the proof. The final dependency-axiom audit checks that a
proof placeholder or custom assumption has not been smuggled in as an axiom.

## Mathematical interpretation checks

- The prime period is a normalization of the parameter. It does **not** impose
  unit length, unit speed, or a numerical bound on geodesic length.
- A regular loop has strictly positive actual integral energy. Constant loops
  cannot supply the asserted prime closed geodesics.
- Strong convexity is checked for all nonzero tangent directions. Smoothness
  is checked away from zero, where this Hessian is meaningful.
- The coordinate equation uses F² while the metric Hessian uses ½F².
  The constant positive scale changes neither stationarity nor the zero
  Euler–Lagrange residual.
- `toOrdinary` and `toVariational` preserve the exact same loop. The
  comparison of image sets does not merely preserve a numerical count.
- The proved entry points concern n ≥ 3. Their statements introduce no
  irreversible-metric claim, curvature restriction or nondegeneracy restriction.

## Four-statement FC presentation

The separate [FC-style draft](../FClikelean/ReversibleFinslerSpheres.lean) contains
four statements, all using the independent `PrimeClosedGeodesicImages` definition
in [the FC package](../FClikelean/ReversibleFinslerSpheres.lean).
It uses FC’s standard `public import FormalConjecturesUtil`. All problem-specific
definitions are in that one file, inside `ReversibleFinslerSpheres`: three `def`s,
one structure and two abbreviations. Smoothness, periodicity, regularity, primeness
and variation conditions are written directly on ordinary functions. The separate
[correspondence proof](FCDefinitionCorrespondence.lean) constructs an equivalence
between metric records and proves equality of the image sets. Its proofs use no
FC placeholder theorem, as enforced by the transitive axiom audit. The equivalence of the universally quantified
Finsler and Riemannian assertions holds at every dimension:

| Statement | Formal dimension and metric conditions | Local proof status |
| --- | --- | --- |
| OpenAI's Riemannian sphere assertion | n : ℕ, 2 ≤ n; `ReversibleMetric n`; `IsRiemannian F` | n ≥ 3 specialization proved; n = 2 supplied by literature outside local Lean scope |
| Reversible Finsler spheres in all dimensions at least two | n : ℕ, 2 ≤ n; `ReversibleMetric n` | Combination from an explicit n = 2 hypothesis proved; literature supplies that case mathematically |
| Reversible Finsler two-spheres | `ReversibleMetric 2` | Literature result [DPMMS22]; outside local Lean proof scope |
| Reversible Finsler spheres in dimensions at least three | n : ℕ, 3 ≤ n; `ReversibleMetric n` | Equivalent to the proved entry point via the checked correspondence |

`IsRiemannian F`, defined inside the standalone FC package, requires,
at each point of the actual sphere, a real bilinear
form on its actual tangent fiber, symmetric and positive on every nonzero
diagonal, whose diagonal equals F². Smoothness of its local coefficients follows
mathematically by polarization from the already smooth slit-bundle norm.
This interpretation has not been turned into a Lean equivalence with Mathlib's
Riemannian bundle API. [FCStatementReadback.lean](FCStatementReadback.lean)
checks all four complete theorem types in isolation. The separate correspondence
module proves that the round metric satisfies the independent predicate and
checks eight proofs for transitive axioms. Its `stationary_iff` theorem
bundles and unbundles smooth variations; `primeImages_eq` then uses the existing
proof-side equivalence with the Euler–Lagrange equation for regular smooth loops; `primeImages_eq` preserves prime periods and exact images.
These checks do not prove the four placeholder statements.

The FC metadata is also read back from Lean's environment: each declaration
has the upstream `research solved` category and AMS subject 53. This is
mathematical classification metadata, not a local proof-completion flag.

[FCImplications.lean](../lean/FCImplications.lean) formalizes the relation
between the statements without importing the FC draft. It proves
`FinslerAllDimensionsAssertion ↔ FinslerTwoSphereAssertion` using the existing
n ≥ 3 result, and
`FinslerAllDimensionsAssertion → RiemannianAllDimensionsAssertion` by applying
the Finsler theorem to the same metric. No change of geodesics or image sets
is involved. [FCImplicationsReadback.lean](FCImplicationsReadback.lean) checks
the exact quantifiers and audits the six proofs' transitive axioms. The
two-sphere assertion is an explicit input to the conditional all-dimensional
proofs, not a discharged premise.

## Historical two-sphere research

The previous [two-sphere criteria](../lean/FCTwoSphere.lean) and their
[readback](TwoSphereReadback.lean) are retained as research artifacts.
They are not an unconditional n = 2 proof and are no longer requirements
for the four-statement presentation. See [DIMENSION-TWO.md](DIMENSION-TWO.md).

## Result and limits

The local definition review found the wording of [PROBLEM.md](../PROBLEM.md)
consistent with the explicit Lean target. The precise executable results and
logs are in [STATUS.md](STATUS.md).

Lean checks the stated formal equalities and proofs. The interpretation of
English mathematical prose is a reviewed judgment, not itself a
kernel theorem. Comparator checks agreement between a fixed formal challenge
and the solution; it does not independently interpret prose.

This review does not certify every intermediate mathematical construction
against its textbook meaning, nor the older PDF line by line. It does not
replace the original project's pending independent verification or human
semantic acceptance process. No original acceptance file was modified.

## Reproduce the executable part

After building either Lean project:

```bash
cd lean
lake env lean -M4096 -j2 -DElab.async=false FCAudit.lean
lake env lean -M4096 -j2 -DElab.async=false SpecificationReadback.lean
```

The Comparator challenge and solution have identical signatures, checked by
`scripts/check-package.py`. The independent FC definition is related to them
by the Lean correspondence proof, not by text equality. After building `lean/`:

```bash
python3 scripts/check-fc-statements.py --fc-source /path/to/formal-conjectures
```

This cross-version check expands only the standard FC import; the mathematical
body is unchanged. `check-fc-upstream.py` separately checks the original file
with FC's toolchain, full standard import and Lake options; see the
[FC guide](../FClikelean/README.md).
