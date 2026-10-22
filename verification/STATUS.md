# Verification status

Updated: **22 October 2026**. The hosted exact-FC-target workflow has passed. Local macOS checks and
hosted Linux CI outcomes are recorded separately; the current local kernel
replay timeout is retained. Earlier general proof results remain historical evidence.

## Public main verification

The verified proof package was published to
[reversible-finsler-spheres](https://github.com/KitaKen1/reversible-finsler-spheres)
on public `main`, code commit `be3aaf6949fd931d61aef749ed59207fc6ef21a6`.
The exact-target workflow now runs on pushes to `main`, using the same
mathematical sources, dependency pins, memory settings, Comparator and landrun
as the successful private run below. The first public run,
[39703676590](https://github.com/KitaKen1/reversible-finsler-spheres/actions/runs/39703676590),
started on 22 October 2026 at 01:05 UTC (10:05 JST). Its source inventory check
passed; the initial observation records an in-progress run with no project
cache. See the live run for its current result. A public-run success is not
claimed by this initial record.

## Hosted exact FC target: PASS

[Run 39700419746](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/39700419746)
completed successfully on **22 October 2026, 00:54 UTC (09:54 JST)**, testing code
commit `8522da6e32808f4d35a3a6a056fcb2bea8b9fd46` on Ubuntu 24.04.

| Hosted check | Result |
| --- | --- |
| Sealed sources and exact FC definition extraction | PASS |
| Independent reference build | PASS |
| Source build and transitive axiom audit | PASS; 2,001 cached project modules validated by Lake, four entry modules checked |
| Pinned Comparator, lean4export and real landrun installation | PASS |
| Unmodified upstream Comparator CLI: target and dependent definitions | PASS |
| Built-in Lean kernel replay | PASS: `Lean default kernel accepts the solution` |
| Post-Comparator exact target axiom audit | PASS: only `propext`, `Classical.choice`, `Quot.sound` |

The [archived Comparator log](ci/39700419746/fc-target-comparator.log) ends with
`Your solution is okay!`; the [axiom log](ci/39700419746/fc-target-axioms.log)
records the exact target. The combined Comparator/post-audit step took 812
seconds. That is a combined step duration, not a kernel-only measurement.
The source-build step took 23 seconds after cache validation.
The [hosted receipt](ci/39700419746/receipt.json) identifies the tested commit,
checker pins, source hashes and every archived artifact file. The downloaded
artifact ZIP matched GitHub's SHA-256 digest before extraction.

This is an incremental hosted build using Lake-validated artifacts, followed by
the actual pinned CLI and Linux sandbox. No independent kernel implementation
was run. The certified statement is the complete n ≥ 3 FC target; n = 2 remains
a literature result outside this Lean proof scope.

## Earlier hosted failures and corrections

The target remains
`ReversibleFinslerSpheres.infinitely_many_prime_closed_geodesics`, with the
unchanged mathematical definitions and full n ≥ 3 statement from the single-file
FC submission. The generator preserves the module system and public visibility;
it omits only FC metadata and the other three theorem statements.
The submission's SHA-256 remains
`aef1b8bc5e007a1acdf47d9ee53ea8c43e20be4c816c201dddc901ce2b1ceeff`.
The n = 2 case is cited from DPMMS22 and remains outside the Lean proof scope.

Both hosted runs of code commit
`34da8dca82738a260105761ef3c38ffd908d5b6a` failed:
[run 39617179314](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/39617179314)
and [run 39617355700](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/39617355700).
Both passed all 2,002 preceding source modules and then exceeded Lean's
4 GiB memory limit while compiling `FCSolution` (module 2,003 of 2,005).
Comparator was skipped. The [first log](ci/39617179314-source-failure.log)
and [second log](ci/39617355700-source-failure.log) preserve the actual diagnostics.
The earlier `NativeSequentialSuffixMiddle.common_eq` memory refactor passed
in both hosted builds; these are subsequent failures at a different entry.

The corrected code commit `bd32c720439644485485e76fe4e0fd5a4c44c3e4`
passed hosted source compilation and the exact-target axiom audit in
[run 39699630290](https://github.com/KitaKen1/ci-test-sandbox/actions/runs/39699630290).
Lake validated 2,001 cached project modules and compiled the four entry modules
in 26 seconds. See the [source-build log](ci/39699630290-source-pass.log).
The subsequent tool-installation stage failed because the installer ran
`go build .` in the landrun repository root, which has no Go sources. Both
Comparator and lean4export had built successfully. The installer now targets
landrun's actual `./cmd/landrun` package with `-mod=readonly`; checker pins are
unchanged. The [failure log](ci/39699630290-landrun-build-path-failure.log) is retained.
The installer correction and all remaining checks passed in the hosted run
recorded above.

### Current import-memory correction

The short legacy entry files requested private import data and interpreter code
from thousands of transitive modules. The replacement keeps Lean's `module` /
`public import` interface. The exact FC bridge now uses Tau Ceti's public
velocity formulas and an explicit energy equality instead of unfolding hidden
dependency implementations. No metric condition, target type or proof-library
statement is changed. Both publication variants contain identical replacements.

| Local CI-style compile | Legacy wrapper RSS | Current wrapper RSS | Current result |
| --- | --- | --- | --- |
| `FCTargetDefinitions` | 2,790,178,816 bytes | 1,332,314,112 bytes | PASS |
| `FCSolution` | 3,885,891,584 bytes | 1,861,255,168 bytes | PASS |
| `FCExactSolution` | 3,911,663,616 bytes | 1,886,339,072 bytes | PASS |
| `FCExactAudit` | 3,894,083,584 bytes | 1,867,972,608 bytes | PASS; only the three permitted axioms |

The [measurement receipt](local/entry-import-memory-receipt.json) records the
source and log hashes. These macOS runs used `-M4096 -j2 -DElab.async=false`,
Lake-format import artifact maps, and `.olean`, `.ilean` and C output.
The legacy wrapper also passed locally: the hosted Linux failure is not
misrepresented as a locally reproduced failure. The measurements establish the
large reduction; the hosted success above supplies the corresponding Linux check.
The local exact-target verifier now uses these import maps and C output for
both variants, closing the gap in the previous entry compilation checks.
Both variants' nine entry compilations, both exports, the upstream structural
comparison and axiom check passed (13 phases). Structure/axioms took 285.982
seconds. The current local built-in kernel replay timed out at 600.095 seconds
at its unchanged 600-second deadline. The [current receipt](local/fc-target-comparator-receipt.json)
records this as a timeout, not as a successful kernel check or a mathematical
rejection. Temporary exports were removed. The actual hosted CLI/kernel check
passed, as recorded above. The matching
[direct post-Comparator audit command](local/ci-audit-command-receipt.json) also
passed locally without a setup override; this separate check retains its log.

### Previous successful local Comparator result

The [preserved receipt](local/fc-target-before-module-import-refactor/receipt.json)
records all fourteen successful phases for the previous wrappers: structure /
axioms in 142.604 seconds and built-in kernel replay from an empty environment
in 432.554 seconds, within a 600-second budget. Only `propext`,
`Classical.choice` and `Quot.sound` occur. This is a pinned upstream API check on
macOS, with source-matched incremental dependencies and no OS sandbox. Its
result is not relabeled as a replay of the current wrapper sources.

The still earlier [receipt](local/fc-target-before-memory-refactor/receipt.json)
retains the 3,602-second kernel replay timeout before the `common_eq` proof-only
memory refactor. Its source manifest and timeout extension record are retained.
The [native-suffix regression receipt](local/native-suffix-memory-receipt.json)
and [bounded recompilations](local/memory-regression-receipt.json) describe that
separate fix. Neither historical result substitutes for the current CI result.

### Cache validation and serial builds

Both failed hosted runs successfully saved partial project artifacts. On retry,
Lake first validates the entire `Finsler.Residual.FillRel` import closure with
`--no-build`. Only a successful Lake trace/artifact check permits omitting
per-module invocations for that closure. Otherwise the full serial build is used.
This avoids roughly 1.5 hours of repeated Lake startup on an unchanged cache.
It does not skip source validation or Comparator.

The [real-Lake regression](local/build-cache-regression-receipt.json) passed a
cold build, a valid-cache build, and invalidation after changing the cached core
to an invalid proof. That last case correctly fell back to source compilation
and rejected the false proof. Temporary test outputs were removed.

The hosted workflow uses the unmodified pinned Comparator CLI and real Linux
`landrun` after source compilation and axiom audit. The independent challenge
retains one intentional placeholder; no solution imports any FC placeholder.
The canonical FC submission retains four statements, one namespace, three
definitions, one structure and two abbreviations.

## Exact FC environment check, 21 October

The unchanged submission file compiled with the full `public import
FormalConjecturesUtil`, FC's Lean v4.33.1, matching cached Mathlib dependencies
and the selected checkout's Lake options. All 228 FC support modules were built
from source into temporary output; the four types and research-solved / AMS 53
metadata were read back successfully. The source-hashed
[receipt](local/fc-upstream-receipt.json) identifies the exact checkout revision
and every input; the [log](local/fc-upstream.log) retains the diagnostics.
The check took 227 seconds and removed its approximately 44 MB temporary output.
It reused dependency caches and is not a clean Mathlib build or upstream CI run.

The submission/readback diagnostics contain copyright-header style warnings
and the four intended FC `sorry` warnings. The original Kenta Kitamura header
is retained by author preference. Thus successful elaboration is recorded;
a warning-free FC style check or upstream acceptance is not claimed.

## Checks actually executed

| Check | Result | Evidence |
| --- | --- | --- |
| Existing source ↔ both publication proof trees | ✅ 2,056 source files per variant match | [source hashes](proof-source-manifest.json) |
| With-Comparator proved targets | ✅ PASS (23.3 s) | [log](local/lean-FCSolution.log) |
| Without-Comparator proved targets | ✅ PASS (14.1 s) | [log](local/without-FCSolution.log) |
| Comparator reference (2 intended placeholders) | ✅ PASS (5.7 s) | [log](local/lean-Challenge.log) |
| Original one-statement FC draft (superseded) | ✅ PASS (6.5 s) | [historical log](local/fc-statement.log) |
| Pinned upstream FC attribute implementation | ✅ PASS | [source hashes in the receipt](local/fc-four-statements-receipt.json), [log](local/fc-four-statements.log) |
| Current four-statement FC draft (4 intended placeholders) | ✅ PASS | [log](local/fc-four-statements.log) |
| FC definitions, four types and category/AMS metadata, isolated from proof modules | ✅ PASS | [source](FCStatementReadback.lean), [receipt](local/fc-four-statements-receipt.json) |
| Independent FC definitions ↔ proof targets; round metric; eight axiom audits | ✅ PASS | [source](FCDefinitionCorrespondence.lean), [log](local/fc-four-statements.log) |
| n ≥ 3 solution with the shared Riemannian definition | ✅ PASS | [log](local/fc-four-statements.log) |
| Six proved FC implications/specializations and transitive axiom audit | ✅ PASS | [source](FCImplicationsReadback.lean), [log](local/fc-four-statements.log) |
| Two-sphere families, phase charts, transverse splitting and iteration, homology comparison, filling and criteria, canonical variant | ✅ PASS (384.3 s across thirty stages) | [source](TwoSphereReadback.lean), [log](local/two-sphere.log) |
| Same two-sphere checks, without-Comparator variant | ✅ PASS (364.8 s across thirty stages) | [receipt](local/two-sphere-receipt.json) |
| Transitive axiom audit: 2 public targets + 2 final project theorems | ✅ PASS (20.5 s) | [log](local/lean-FCAudit.log) |
| Same axiom audit, without-Comparator variant | ✅ PASS (19.1 s) | [log](local/without-FCAudit.log) |
| 26 executable specification checks | ✅ PASS (16.0 s) | [log](local/lean-SpecificationReadback.log) |
| Same 26 checks, without-Comparator variant | ✅ PASS (16.8 s) | [log](local/without-SpecificationReadback.log) |
| Upstream Comparator: target types, dependent definitions and target axioms | ✅ PASS (295.2 s) | [log](local/comparator-structure-and-axioms.log) |
| Upstream Comparator: built-in Lean kernel replay | ⏱ TIME LIMIT (180.1 s) | [log](local/comparator-builtin-kernel-replay.log) |

Allowed transitive target axioms: **propext, Classical.choice, Quot.sound**.
The two intentional challenge placeholders and the four FC draft placeholders
are excluded from the solution dependency graph. No other proof placeholders
or project axiom declarations were found by the publication source scan.

The separate kernel replay attempt did not complete within its 180-second
budget, which includes parsing the exported environment. No successful fresh
kernel replay is claimed, and the timeout is not a mathematical rejection.

## Prose correspondence

✅ The local AI-assisted definition review found the English problem
statement consistent with the formal target. The executable readback checks
26 statements in each variant, covering the sphere, actual metric conditions,
geodesic equation, prime period, images, equivalent variational formulation,
nonvacuity and the complete theorem quantifiers. See the
[definition-by-definition review](STATEMENT-CORRESPONDENCE.md).

The interpretation of prose remains a reviewed mathematical judgment; it is
not a machine theorem about natural language or an independent human sign-off.

The FC presentation now contains four theorem statements: Riemannian spheres
for n ≥ 2, reversible Finsler spheres for n ≥ 2, the reversible Finsler
two-sphere case, and reversible Finsler spheres for n ≥ 3. The original receipt
and `fc-statement.log` concern the earlier one-statement draft. The separate
[four-statement receipt](local/fc-four-statements-receipt.json) records the
new draft's source hashes, nine compilation stages and their measured times.
The first four compile the official FC attribute modules, the statement body
and four type/metadata examples with only Mathlib dependencies available.
For this v4.35 cross-version check, the standard FC umbrella import is expanded
into the official attribute module and the used Mathlib modules. The exact
FC import and v4.33.1 environment are a separate check (see the FC guide). The remaining stages check its correspondence
with the proof definitions, round-metric nonvacuity, and the existing solution
and implications. The correspondence proves metric equivalence and exact equality
of the counted image sets; its eight theorem dependency graphs passed the axiom
audit. These checks do not prove the placeholder statements.
The separate `FCImplications` module proves the Riemannian n ≥ 3
specialization, the equivalence of all-dimensional Finsler infinitude with
the missing two-sphere case, and the implication from the Finsler assertion
to the Riemannian assertion. Six theorem dependency graphs passed the axiom
audit without `sorryAx`. The module is identical in both proof projects;
this additional compilation/audit used the canonical `lean/` copy.
The unconditional n = 2 theorem has no Lean proof here and is outside the
current scope; it is cited as a literature result. See [DIMENSION-TWO.md](DIMENSION-TWO.md).
The earlier coordinate Comparator targets are unchanged. The shared 2,056-file
core now includes the proof-only memory refactor described below; the exact FC
target above is an additional interface.

## Historical two-sphere development (outside current proof scope)

The additional two-sphere development proves the finite-spectrum obstruction
in DPMMS Lemma 5.5, its application to the actual geodesic definitions, and
the point-covering criterion. It extracts actual closed geodesics from
noninjective relative homology inclusions using Birkhoff descent, and proves
a disk-filling criterion using Tau Ceti's homology calculation.
The repeated-block construction now gives continuous H¹ families, recovers
all input blocks, agrees exactly with integer iteration on the diagonal,
and preserves embeddings for compact injective input parameterizations.
Its energy formula, strict maximum and positive boundary deficit uniform in
the block count are proved. A map of actual parameter/boundary pairs into
the genuine Sobolev energy sublevels is constructed as well.
The connector extension joins two independently based groups by actual short
minimizing paths and their reversals. It proves continuity, the exact energy
identity, arbitrarily small uniform connector budgets, both boundary estimates,
and the threshold for large groups. The actual equal-endpoint connector is
proved constant. A strong H¹ homotopy removes both diagonal pauses through
zero duration while decreasing energy, preserving both sublevel cuts and
inducing the same relative singular homology map. At the repeated center its
endpoint is exactly the sum iterate. The enlarged family with two interval
base parameters is now constructed with all boundary bounds. An explicit
slide to the second interval endpoint proves that its diagonal, and hence
the ordinary repeated family, induces zero on relative homology. The map
in a smaller cut is constructed and its inclusion is identified exactly.
A nonzero induced map in that smaller cut therefore produces an actual
closed geodesic strictly above the repeated length.
The local critical class is now constructed from a maximal disk, a continuous
coordinate projection and a central-fiber minimum of the energy. It is
nonzero both in the full coordinate neighborhood and in the strict lower
sublevel with just the critical point adjoined. Excision identifies its
localization to any open neighborhood when the energy is continuous.
Two executable examples use the degenerate saddle z² − ‖x‖⁴ over Z/2Z.
The polygon-to-loop comparison now uses the actual sampling map as a left
inverse to the broken-geodesic map. Both maps preserve the critical pair,
so polygon local homology injects into genuine H¹ loop local homology.
Excision transfers a maximal-disk class from an open polygon neighborhood
before this injection. Every closed geodesic has an actual critical polygon
model whose broken path agrees with its parametrized Sobolev loop. Additional
readback examples check the proper open-neighborhood inclusion of the saddle,
the S² model construction and the split injection over rational coefficients.
The new local splitting model has no zero edges and is constructed for
every closed geodesic. Its chart is on the actual open short-polygon space
and satisfies the reduced-energy plus Hessian identity. A separate theorem
constructs a small maximal disk and radial detector from a local product
form with the required reduced maximum and transverse minimum. It gives
an embedded H¹ family and a nonzero loop local class. The new examples
check a degenerate saddle in an open coordinate ball, the dimension-zero
detector, and the S² splitting model.
The spectral bridge constructs complementary nonpositive/positive coordinates,
proves the quadratic sign and zero-set identities, and constructs a maximal
disk from strict maximality of the reduced function on the kernel. The
actual restriction perpendicular to a kernel vector is symmetric; removing
one nonzero direction decreases nullity by exactly one. New readback examples
check a two-dimensional quartic maximum with zero Hessian and the nullity of
the restricted zero operator in dimension three.
The actual phase geometry now constructs one uniformly fine polygon model
for all rotations of a closed geodesic. Its nonzero tangent is proved to
lie in the actual Hessian kernel. The inverse function theorem straightens
this curve into a nonlinear phase/transverse chart with its original phase
parameter. The phase-zero slice has exactly the original polygon and H¹
broken-loop energy. Its projected gradient is C², represents the derivative
on a neighborhood, and has the restricted operator as its derivative at
zero. This operator is therefore the genuine transverse Hessian, with
nullity exactly one less. The degenerate splitting lemma applies on the
slice without an isolation or nondegeneracy hypothesis. Three new readback
examples check the nonlinear curve t↦t+t², the actual S² Hessian/nullity
identities, and the broken-loop energy of the constructed slice.
The transverse iteration module now proves that phase removal preserves the
negative index and that projection commutes with the actual conformal
iteration map. Under stable nullity, this map gives a continuous linear
equivalence of the actual transverse kernels. The corresponding reduced
energies scale by the square of the iteration count, so a strict reduced
maximum propagates. Splitting and maximal disks are constructed using the
same compared reduction maps. Monodromy supplies a bounded-gap odd
progression preserving nullity for every base iterate, and sampling supplies
the twist hypothesis. Three additional readback examples check the energy
and Hessian identities, the actual S² progression and the resulting maximal
disk with its base-maximum hypothesis explicit.
The actual iteration homology module constructs a local energy retraction
of sphere polygons under index and nullity preservation. Excision on both
point-critical pairs proves that the actual iteration map is injective on
homology in every degree. For a given zero-mean geodesic, the actual index
function is bounded by the dimension and monotone under divisibility. A
positive base iterate attaining its maximum therefore has stable index.
Combining this construction with monodromy supplies the actual injections
along an odd progression, without separate stability hypotheses. New
readback examples check a degenerate saddle on a proper open square and the
actual S² zero-mean endpoint over mod-two coefficients, including bounded
gaps. No existence of a suitable zero-mean geodesic or nonvanishing in orbit
and upper-sublevel pairs is asserted.
The iteration equivalence module constructs an energy-decreasing local
homotopy onto the actual repeated polygons. Its induced critical-pair map
factors the neighborhood inclusion through iteration; excision proves
surjectivity and hence an isomorphism. The actual rotation by one base period
fixes the repeated image, so surjectivity forces its homology action to be
the identity. The zero-mean endpoint is upgraded to isomorphisms on the odd
progression. New examples use a nonlinear normal chart on a bounded domain,
the actual S² iteration/rotation maps over rational coefficients, and the
rational zero-mean progression with bounded gaps. These results do not prove
the orbit exact sequence or identify the smaller prime-period action when
the chosen base is itself an iterate.
The chain-index module proves superadditivity for based variations with no
dimension error, the exact fixed two-edge cost of cutting a repeated
variation, and vanishing of all iterate indices whenever the sequence is
bounded. On actual geodesic data this proves that zero mean implies zero
index at every positive iterate. Positive index at any iterate instead
forces positive mean and eventual growth beyond every fixed bound.
The original sampled geodesic is retained in the new odd-progression
isomorphism and rotation endpoint, resolving the smaller-period issue in
the zero-mean branch when the original geodesic is prime. No orbit-inclusion
exact sequence is claimed. The new readback examples test a two-vertex
quadratic chain whose first based form is nonnegative but whose third
repetition has a negative based variation, actual S² index growth, and the
original-geodesic rational isomorphisms with bounded gaps and rotation action.
The local orbit-model module proves that the actual sphere-chart repetition
projection is invariant under the base-period vertex rotation. A finite
intersection supplies an invariant open neighborhood. The projection then
descends continuously through Tau Ceti's mapping-torus quotient, including
the actual strict lower subspace. The energy-decreasing homotopy and excision
make this detector injective on local critical homology; its descended map
proves injectivity of the height-zero fibre inclusion. This applies in every
degree over every field. A new endpoint discharges the index/nullity
hypotheses along an odd progression of a given zero-mean geodesic. New S²
readback examples check nonzero-class preservation by the actual quotient
map and the original-geodesic rational endpoint. This does not identify
the model with the actual Sobolev critical-orbit pair; that geometric
comparison and upper-cut nonvanishing remain open.
288 public theorem dependency graphs passed the axiom audit in each
variant, using only `propext`, `Classical.choice` and `Quot.sound`. The original
local family with the required reduced extremum conditions for a selected
base geodesic,
preservation of their classes in the orbit and larger sublevel pairs, and the
remaining surface-dynamics branches are still missing. Hence the
full n = 2 assertion has not been proved. The receipt explicitly records
`full_two_sphere_assertion_proved: false`.

The real `research solved` tags express this draft's mathematical
classification, not formal proof completion or upstream acceptance.
The pinned FC revision uses Lean v4.33.1; the checks here use v4.35.0-rc3.

## Exact scope

- Compilation reused the existing build whose source files match this snapshot.
  The two publication entry points, their audits and their specification checks
  were compiled separately. A clean rebuild of both packaged projects was not run.
- The local Comparator route calls the pinned upstream APIs from Lean and has
  no OS sandbox. It does not claim execution of the complete Linux sandboxed CLI.
- The historical structural comparison has a 600-second limit. Its kernel replay, when
  attempted, has a separate 180-second limit. A time limit is not a successful check.
- No Nanoda or other independent kernel implementation was run.
- The historical checks did not include hosted GitHub Actions. The new private
  exact-target run is recorded separately above. No upstream FC submission or
  independent human semantic review is claimed.
- The original development acceptance records were left unchanged. This report
  does not certify the separate original v188 acceptance workflow.
- The older PDF was preserved unchanged; a line-by-line PDF/proof audit was not run.
- General proof/Comparator logs replace only machine-specific path prefixes. Raw log hashes are
  retained in the receipt; the check outcomes and mathematical messages are unchanged.

## Integrity and reproduction

Run `python3 scripts/check-package.py` at the repository root to check the
sealed file inventory, proof hashes, shared-file identity and allowed placeholders.
It also verifies the four FC declarations in order, the standalone FC import
closure, and the common n ≥ 3 signature in the challenge and solution. The
independent FC definitions are related to that target by Lean theorems rather
than a textual signature comparison. Run
`python3 scripts/check-fc-statements.py --fc-source /path/to/formal-conjectures`
after building `lean/` to reproduce
the updated FC elaboration and readback. Its small temporary build is deleted
on completion or failure. See [the Comparator instructions](../lean/comparator/README.md)
for local incremental checks and the separately prepared Linux CLI path.

Run `python3 scripts/check-two-sphere.py --source-build /path/to/matching/Lean --record`
for the separate two-sphere arithmetic, repeated-family, connector, relative pause-removal and explicit filling constructions,
homological extraction, polygon-to-loop comparison, local splitting and
maximal-disk construction, actual phase geometry and transverse splitting,
zero-mean index vanishing and original-geodesic iteration isomorphisms,
invariant local detectors, mapping-torus fibre injections,
and criteria check in both variants.
This reuses a source-matched build, compiles ten
additional Tau Ceti modules with checked source hashes in a temporary overlay,
and removes that overlay and all temporary compiled modules afterward.
