# Four statements for Formal Conjectures

Submit only [ReversibleFinslerSpheres.lean](ReversibleFinslerSpheres.lean).
It uses the FC module format and the standard `public import FormalConjecturesUtil`.
Every mathematical definition specific to this problem is in that file.
There are no local helper imports, bundled utility implementations or proof imports.

| Statement | Mathematical source | Lean proof supplied here |
| --- | --- | --- |
| 1. Riemannian spheres, n ≥ 2 | OpenAI [OAI26] | n ≥ 3 specialization |
| 2. Reversible Finsler spheres, n ≥ 2 | [DPMMS22] plus this repository's n ≥ 3 result | Combination conditional on the cited n = 2 theorem |
| 3. Reversible Finsler spheres, n = 2 | [De Philippis–Marini–Mazzucchelli–Suhr (2022)](https://arxiv.org/abs/2002.00415) | Literature result; outside this repository's Lean proof scope |
| 4. Reversible Finsler spheres, n ≥ 3 | This repository | [FCExactSolution.lean](../lean/FCExactSolution.lean), with and without Comparator |

All four declarations retain their `@[category research solved, AMS 53]` tags
and intentional `sorry` bodies. `solved` describes the mathematical status;
it does not certify a completed Lean proof. The cited literature is not
introduced as a Lean axiom. The draft has not been accepted by FC.
The original Kenta Kitamura copyright and short Apache 2.0 header are retained
by author preference; FC’s specific copyright-header linter expects its own
header and reports a style warning for this choice.

## Minimal definitions

There are **three `def`s**: `IsRiemannian`, `energy` and
`PrimeClosedGeodesicImages`; **one structure**, `ReversibleMetric`; and
**two abbreviations**, `Sphere` and `Fiber`. Everything is inside the single
`ReversibleFinslerSpheres` namespace.
Smooth curves and variations are ordinary functions. Smoothness, periodicity,
nonzero velocity, least positive period and zero first variation are written
directly in the image-set definition. No loop/variation records, coercion
instances or utility lemmas are needed.

The [FC contribution guide](https://github.com/google-deepmind/formal-conjectures/blob/main/CONTRIBUTING.md)
allows explanatory definitions and variants in the same file. Its standard
utility import provides the official metadata and linters. “One file” here
means one problem submission using the existing FC environment.

## Checking

The separate [exact-target proof](../lean/FCExactSolution.lean) and
[Comparator reference](../lean/FCExactChallenge.lean) copy this file's
mathematical definitions and complete n ≥ 3 statement. The generator verifies
that only FC metadata and the other three statements are removed. The module
system and public visibility are retained. Run `python3 scripts/generate-fc-target.py --check`
from the repository root to check this correspondence. This submission file
itself is not rewritten by that process.

Inside a Formal Conjectures checkout, copy the file to
`FormalConjectures/Other/ReversibleFinslerSpheres.lean` and run:

```bash
lake build FormalConjectures.Other.ReversibleFinslerSpheres
```

The [recorded upstream check](../verification/local/fc-upstream-receipt.json)
passed with FC's Lean **v4.33.1** and its pinned Mathlib,
with read-only dependency caches and an automatically removed temporary build:

```bash
python3 scripts/check-fc-upstream.py --fc-source /path/to/formal-conjectures \
  --dependency-build /path/to/matching-cached-project --record
```

The separate proof project uses **v4.35.0-rc3**. Its correspondence check expands
only the standard import into the official attribute module and the Mathlib
modules used by this file; the mathematical body is unchanged:

```bash
python3 scripts/check-fc-statements.py --source-build /path/to/matching/Lean \
  --fc-source /path/to/formal-conjectures --record
```

[FCDefinitionCorrespondence.lean](../verification/FCDefinitionCorrespondence.lean)
proves metric equivalence and exact equality with the proof target's geodesic
image set, including the period and variational conditions. Eight correspondence
theorems are audited for transitive axioms; only `propext`, `Classical.choice`
and `Quot.sound` are allowed. None uses an FC placeholder theorem.
See [verification status](../verification/STATUS.md) for executed checks.
