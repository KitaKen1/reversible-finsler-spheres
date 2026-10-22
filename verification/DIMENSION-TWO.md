> **Scope update, 21 October 2026:** The publication now cites DPMMS22 for n = 2.
> A local Lean proof of that case is outside the current scope. The partial
> development and plans below are historical research, not pending publication requirements.

# The remaining two-dimensional proof

The unconditional n ≥ 2 Finsler theorem is **not yet proved in this package**.
The new [FCImplications.lean](../lean/FCImplications.lean) isolates the exact
remaining obligation as `FinslerTwoSphereAssertion`, with the same metric and
prime-image definitions as FC statement 3. Its combination with the existing
n ≥ 3 theorem, and its implication to the Riemannian assertion, are proved
without importing any FC placeholder.

## Implemented surface-proof components

[HingstonArithmetic.lean](../lean/HingstonArithmetic.lean) now proves the
finite-spectrum arithmetic obstruction behind DPMMS Lemma 5.5, for any
relatively dense set of integers and in particular for odd integers.
[FCTwoSphere.lean](../lean/FCTwoSphere.lean) connects it to the actual regular
stationary geodesics and the FC Euler–Lagrange prime-image set.
[SurfaceMinimax.lean](../lean/SurfaceMinimax.lean) now extracts actual closed
geodesics from relative homology and reduces homology death to a disk filling.
[HingstonBlocks.lean](../lean/HingstonBlocks.lean) constructs the continuous
repeated-block families and proves their embedding and energy properties.
[HingstonConnectors.lean](../lean/HingstonConnectors.lean) constructs the
short-connector extension and proves its exact energy and boundary bounds.
[HingstonPause.lean](../lean/HingstonPause.lean) removes diagonal pauses,
preserves relative homology and identifies the repeated center exactly.
[HingstonFilling.lean](../lean/HingstonFilling.lean) constructs the enlarged
interval-base family, slides the diagonal to its boundary and proves
relative homology vanishing for the ordinary repeated family.
[SurfaceLocalHomology.lean](../lean/SurfaceLocalHomology.lean) constructs
nonzero local critical classes from a maximal disk, coordinate projection
and central-fiber energy minimum, and proves the neighborhood excision step.
[SurfacePolygonHomology.lean](../lean/SurfacePolygonHomology.lean) proves
that these classes inject from polygon neighborhoods into the genuine H¹
loop critical pair. It also constructs an exact critical polygon model of
every parametrized closed geodesic.
[SurfaceMorseData.lean](../lean/SurfaceMorseData.lean) constructs regular
polygon models and actual local splitting charts for every closed geodesic.
For a local product normal form with a strict reduced maximum and a transverse
minimum, it constructs a small maximal disk, its detector, an embedded loop
family and a nonzero loop local class.
[SurfaceSpectralDisk.lean](../lean/SurfaceSpectralDisk.lean) now obtains that
disk from a symmetric splitting and strict maximality of the reduced function
on the kernel. It constructs the nonpositive/positive product coordinates,
proves the required quadratic inequalities, and computes the disk dimension.
It also constructs the actual Hessian restriction perpendicular to a kernel
vector and proves that removing one nonzero direction decreases nullity by one.
[SurfacePhaseGeometry.lean](../lean/SurfacePhaseGeometry.lean) constructs
one polygon model for all phases of an actual closed geodesic, proves that
the nonzero phase tangent is a Hessian kernel vector, and straightens the
phase curve by the inverse function theorem. The phase-zero slice has the
original polygon and broken-loop energy; its actual Hessian is the restricted
operator and admits a degenerate splitting.
[SurfaceIteration.lean](../lean/SurfaceIteration.lean) restricts the actual
iteration map to the phase slices, proves kernel equivalence under stable
nullity, and transports the reduced maximum using the genuine energy
identity. It constructs maximal disks with the same reduction maps and
provides a bounded-gap odd progression of stable iterates from monodromy.
[SurfaceIterationHomology.lean](../lean/SurfaceIterationHomology.lean) constructs
an actual local energy retraction onto repeated polygons when index and
nullity are preserved. Excision proves injectivity of the actual iteration
map on point-critical homology. For a given zero-mean geodesic, it chooses a
positive base iterate with stable index and obtains these injections along
an odd monodromy progression without a separate stability hypothesis.
[SurfaceIterationEquivalence.lean](../lean/SurfaceIterationEquivalence.lean)
constructs an energy-decreasing local deformation onto the actual repeated
polygons. This upgrades the iteration injection to an isomorphism and proves
that rotation by one base period acts trivially on point-critical homology
when index and nullity are preserved. It also upgrades the given zero-mean
geodesic endpoint to isomorphisms along the odd progression.
[SurfaceChainIndex.lean](../lean/SurfaceChainIndex.lean) proves that bounded
periodic indices force all of them to vanish. Repetition and cutting at one
vertex incur only a fixed two-edge cost, and independent based variations
force linear growth of index. [SurfaceZeroMeanIndex.lean](../lean/SurfaceZeroMeanIndex.lean)
transfers this to the actual sampled geodesic: zero mean implies zero index
at every positive iterate, while positive index at one iterate implies
eventual growth beyond any bound. The original geodesic can now be retained
in the isomorphism and rotation-action endpoint.
[SurfaceOrbitModel.lean](../lean/SurfaceOrbitModel.lean) constructs a
rotation-invariant local detector and proves injection into the explicit
period-rotation mapping torus. The actual Sobolev critical-orbit comparison
remains open. All eighteen modules are also present, identically, in
`leanWithoutComparator/`.

| Component | Implementation | Status |
| --- | --- | --- |
| Invariant repetition projection in actual centered sphere charts | `tanProj_shiftL`, `centeredPolygonChart_periodRotation` | Proved |
| Nonvanishing in the actual local period-rotation mapping torus | `exists_polygon_torus_injection` | Proved under the geometric index/nullity equalities; the detector and homology injection are constructed |
| Original-geodesic odd-progression mapping-torus injections | `exists_original_torus_injections` | Proved for a given zero-mean geodesic; actual Sobolev critical-orbit comparison still open |
| Symmetric density → forward bounded gaps | `forward_dense_of_symmetric_dense` | Proved |
| Finite positive length spectra leave a uniform gap above some point in each sufficiently long progression block | `finite_spectrum_progression_gap` | Proved |
| Dense-index and odd-index approximation contradict finite spectra | `finite_spectrum_not_dense_approximated`, `finite_spectrum_not_odd_approximated` | Proved |
| DPMMS Lemma 5.5 with actual closed geodesics | `infinite_prime_images_of_dense_length_approximation` and its odd specialization | Proved, with the lemma's length-production hypothesis explicit |
| A closed geodesic through every point forces uncountably many prime images | `prime_images_not_countable_of_geodesic_cover` and its infinitude consequence | Proved, with the point-cover hypothesis explicit |
| An interval without closed geodesics preserves relative homology | `level_deformation_of_no_geodesic`, `inclusion_bijective_of_no_geodesic` | Proved, for n ≥ 1 and any field of coefficients |
| A dying relative class forces an actual regular closed geodesic in the length interval | `exists_geodesic_of_not_injective` | Proved, with the noninjectivity input explicit |
| A nonzero disk class factoring through a disk of a different dimension dies | `not_injective_of_disk_filling`, `exists_geodesic_of_disk_filling` | Proved using Tau Ceti's disk homology; the maps and nonzero local class remain inputs |
| Homology death just above large odd multiples forces infinitely many prime images | `infinite_prime_images_of_odd_homology_death` | Proved, with the homology-death input explicit |
| Continuous concatenation of arbitrarily many loops at a varying common basepoint | `continuous_concat`, `concat_injective`, `family` | Constructed on the actual strong H¹ loop space |
| The repeated center is the actual integer iterate, with its parametrization | `concat_diagonal`, `family_diagonal` | Proved |
| A compact injective local family gives an embedded repeated family with strict maximum | `family_isClosedEmbedding`, `energy_family_lt` | Proved; the original local family remains an input |
| Exact repeated energy and a positive boundary deficit uniform in the block count | `energy_concat`, `energy_concat_deficit`, `exists_boundary_deficit` | Proved |
| Repeated family as a map of actual parameter/boundary and energy-sublevel pairs | `familyPairMap`, `family_mem_lev`, `family_boundary_mem` | Constructed; nonvanishing on homology remains open |
| Two independently based loop groups joined by actual minimizing paths and their reversals | `shortLoop`, `blockLoop`, `continuous_loop`, `continuous_shortData` | Constructed as continuous H¹ families |
| Connector energy and both transverse and base-boundary estimates | `energy_blockLoop`, `blockLoop_boundary_lt`, `blockLoop_base_boundary_lt` | Proved with explicit energy bounds on the input families |
| Connector budgets chosen before the block counts, and the large-group threshold | `exists_uniform_budget`, `exists_base_boundary_threshold`, `blockLoop_mem_lev` | Proved; a uniform geometric neighborhood is constructed |
| Equal-endpoint minimal segment is the actual constant H¹ path | `shortPath_self` | Proved |
| Two-pause removal with joint strong H¹ continuity through zero duration | `continuous_value`, `diagonalHomotopy` | Constructed; starts at the actual connector family |
| Energy decreases and both interior and boundary cuts are preserved | `energy_value_mono`, `diagonalHomotopy_mem_lev`, `pairHomotopy` | Proved |
| The relative singular homology map is unchanged by pause removal | `family_homology_eq` | Proved in every degree over any field |
| The repeated center ends at the exact sum iterate | `join_iterates`, `diagonalHomotopy_iterates_end` | Proved with the original parametrization |
| Disk filling up to homotopy detects a closed geodesic | `exists_geodesic_of_homotopic_disk_filling` | Proved; the filling and nonzero class remain inputs |
| Explicit two-base extension with all base and transverse faces controlled | `enlargedFamily_mem_lev`, `enlargedFamily_boundary_mem` | Constructed from the local family and quantitative energy bounds |
| Slide the diagonal to the second base endpoint | `slidePairHomotopy`, `slide_homology_eq_zero` | Proved for actual energy-sublevel pairs |
| Ordinary repeated family induces zero on relative homology | `block_homology_eq_zero` | Proved in every degree, with no filling-map hypothesis |
| Ordinary family in any cut above the repeated length, with literal inclusion compatibility | `energy_blockPairMap_le`, `lowerBlockPairMap_comp` | Proved; center is the exact sum iterate |
| Nonzero repeated local class gives a nearby longer closed geodesic | `exists_geodesic_of_block_filling` | Proved; only the family bounds and nonzero class remain inputs |
| Disk/boundary → disk/puncture preserves homology | `isIso_boundaryToPunctured`, `puncturedClass_ne_zero` | Proved in every dimension using Tau Ceti's radial deformation and disk calculation |
| Construct a nonzero class from coordinate and energy data | `localClass_ne_zero`, `product_class_ne_zero`, `chart_class_ne_zero` | Proved; the maximal disk and central-fiber minimum are geometric inputs, including degenerate maxima |
| The class is nonzero in the lower sublevel with only the critical point adjoined | `criticalClass_ne_zero` | Proved; no higher-energy points or assumed nonzero homology class are used |
| Restrict the critical carrier to any open neighborhood of the point | `isIso_critical_excision`, `excisedClass_ne_zero` | Proved with explicit continuous-energy and open-cover hypotheses |
| Include a neighborhood's critical pair in the full critical pair | `isIso_criticalInclusion` | Proved for the actual inclusion, with the nested subtype identifications |
| Broken geodesics and sampling preserve the critical pairs and compose to the identity | `brokenPair_samplePair` | Proved for the actual polygon and strong H¹ loop spaces |
| Polygon local homology injects into loop local homology | `brokenPair_homology_injective`, `brokenPair_class_ne_zero` | Proved in every degree over any field, using the actual sampling left inverse |
| A maximal disk in an open polygon neighborhood gives a nonzero loop local class | `localDiskToLoops_class_ne_zero` | Proved from coordinate and energy conditions by excision and the split injection |
| Every closed geodesic admits a critical polygon model with exactly the same parametrized broken loop | `nonempty_geodesicModel` | Constructed by sufficiently fine sampling below any strictly larger squared energy cut |
| Fine sampling has no zero edges, so polygon energy is smooth near the geodesic | `nonempty_regularGeodesicModel` | Constructed for every closed geodesic below the prescribed cut |
| Analytic splitting on the actual open short-polygon space | `exists_short_splitting`, `nonempty_geodesicMorseModel` | Constructed, including the exact center and reduced-energy plus Hessian identity |
| A local product normal form supplies its own small disk and detector | `nonempty_maximalDiskData_of_normalForm` | Proved from a germ of strict reduced maximality and a transverse minimum |
| The constructed disk gives an embedded H¹ family with the correct center and strict maximum | `diskLoopFamily_isClosedEmbedding`, `diskLoopFamily_center`, `diskLoopFamily_strict_max` | Proved using sampling and the disk detector |
| The local product normal form produces a nonzero loop local class | `exists_nonzero_loopClass_of_normalForm` | Proved; the suitable product form and its extremum conditions remain geometric inputs |
| Negative and zero directions form a complementary factor to the positive directions | `splitEquiv`, `diskCoordinates`, `finrank_nonpositive` | Constructed from Tau Ceti's spectral subspaces and Mathlib's orthonormal bases |
| A strict reduced maximum on the kernel supplies the whole maximal disk | `reducedPart_strict_max`, `nonempty_maximalDiskData_of_spectralSplitting` | Proved; the reduced maximum is still an input, appropriate to a phase-transverse chart |
| Restrict the Hessian perpendicular to one nonzero kernel direction | `phaseRestriction_symmetric`, `phaseKernelEquiv`, `phaseRestriction_nullity` | Constructed; nullity decreases by exactly one |
| All rotations of an actual geodesic admit one uniformly fine short-polygon model | `nonempty_geodesicPhaseModel`, `phasePoint_broken`, `phasePoint_energy` | Constructed; exact parametrized reconstruction, criticality, nonzero edges and constant energy |
| The actual regular phase tangent lies in the actual Hessian kernel | `phaseVector_ne_zero`, `phaseVector_mem_ker`, `actual_phase_nullity` | Proved by differentiating the stationary phase curve |
| A nonlinear phase/transverse chart preserves the original phase parameter | `exists_phaseChart`, `exists_phaseChart_energy` | Constructed by the inverse function theorem, including exact polygon and H¹ energy on the phase-zero slice |
| The transverse operator is the actual Hessian of the restricted energy | `transverseGradient_hasFDerivAt`, `transverseHessian_eq_operator` | Proved by differentiating the projected gradient; nullity is one less |
| Degenerate splitting on the actual transverse slice | `exists_transverse_splitting` | Constructed for every closed geodesic; no reduced maximum is asserted |
| Phase removal preserves the negative index | `phaseRestriction_index`, `operator_index` | Proved for the actual restricted symmetric operator |
| Actual iteration commutes with phase projection and the projected gradient | `phase_projection_map`, `gradient_iteration`, `operator_iteration` | Proved for conformal iteration, including vectors outside the phase slice |
| Stable full nullity gives an actual equivalence of transverse kernels | `sliceKernelEquiv`, `kernelEquiv_apply` | Constructed with the actual iteration map as its forward map |
| Compare the reduced functions and preserve a strict reduced maximum | `reduced_energy_iteration`, `reduced_max_iteration` | Proved with exact squared energy scaling; the base maximum is explicit |
| Construct splitting and maximal disks using the same compared reduction | `ReductionData.exists_splitting`, `iterated_maximalDisk` | Proved; disk dimension is the full negative index plus transverse nullity |
| Obtain stable odd iterates uniformly for every base iterate | `exists_stable_odd_progression`, `odd_progression_bounded_gaps` | Proved from monodromy; the twist condition is supplied by actual geodesic sampling |
| Maximal disks on the stable odd progression | `exists_stable_odd_maximalDisks` | Proved from a base reduced maximum; no orbit or upper-sublevel nonvanishing is asserted |
| Construct an energy-nonincreasing local retraction onto repeated polygons | `normal_nonneg_of_index_eq`, `eventually_energy_projection_le`, `exists_polygon_retraction` | Proved using the actual product sphere charts and normal form, under index and nullity preservation |
| Actual iteration injects on point-critical homology | `criticalMap_injective_of_local_retraction`, `polygonIterationPair_homology_injective`, `polygonIterationPair_class_ne_zero` | Proved in every degree over any field, with excision on both critical pairs |
| Choose a stable base iterate for a zero-mean geodesic | `iteration_index_mul_le`, `index_le_dimension_of_zero_mean`, `exists_stable_base_of_zero_mean` | Proved from actual sampled index comparison and the attained maximum of a bounded natural-valued index |
| Obtain actual point-critical homology injections along a bounded-gap odd progression | `exists_zero_mean_iteration_injections` | Proved for a given zero-mean geodesic; no extra index/nullity or homology-comparison hypothesis |
| Deform actual polygons to their repeated projection without raising energy | `exists_normal_deformation`, `exists_polygon_deformation` | Constructed locally in actual sphere charts; fixes the repeated critical point |
| Upgrade the actual point-critical iteration map to an isomorphism | `polygonIterationPair_homology_surjective`, `polygonIterationPair_homology_bijective`, `isIso_polygonIterationPair` | Proved under index/nullity preservation, in every degree over any field |
| Rotation by one base period acts trivially on the whole point-critical homology | `polygonIterationPair_periodRotationPair`, `periodRotationPair_homology_eq_id` | Proved by surjectivity and the actual fixed-image identity; no orientation formula is assumed |
| A given zero-mean geodesic supplies isomorphisms along the odd progression | `exists_zero_mean_iteration_equivalences` | Proved with a constructed stable base iterate; existence of a suitable geodesic and its nonzero class remain open |
| Independent based variations give linear growth of negative index | `basedIndex_add`, `mul_basedIndex_le` | Proved with actual joined variations and no dimension loss |
| A negative periodic variation gives a negative based variation after repetition | `form_update_zero`, `exists_negative_based_repeat` | Proved with an exact two-edge correction independent of the repeat count |
| Bounded periodic indices force every positive-iterate index to vanish | `form_nonneg_of_bounded`, `idx_eq_zero_of_bounded` | Proved for actual finite chain forms |
| Zero mean index gives zero index at every actual geodesic iterate | `index_eq_zero_of_zero_mean` | Proved through sampled polygon Hessians; no index-growth hypothesis |
| Positive index at any iterate forces eventual growth beyond every bound | `mean_pos_of_index_pos`, `index_eventually_gt_of_index_pos` | Proved for actual geodesic iteration data |
| Retain the original geodesic for the odd-progression isomorphisms and rotation action | `exists_original_nullity_progression`, `exists_original_iteration_equivalences` | Proved; no stabilizing base iterate, and the original period is the prime period if the given geodesic is prime |
| Produce the required geodesics for every reversible Finsler two-sphere | Surface minimax and dynamics | Still missing |

The proved components do not prove the last row. In particular, no assertion that
every reversible Finsler two-sphere satisfies the length-production hypothesis
has been introduced. The audit checks 288 public theorems in each
variant, accepting only `propext`, `Classical.choice` and `Quot.sound`.
See [TwoSphereReadback.lean](TwoSphereReadback.lean) and the
[execution receipt](local/two-sphere-receipt.json).

### Arithmetic proof

Let a finite set of positive generators be given, and fix a bound W on the
distance between two integer targets. Choose an integer C such that
W + 1 < C L for every generator L. There are only finitely many values
|d L − k| with d ≤ C and k ≤ W. Choose a positive δ below all the nonzero
values, and choose ε small enough that ε < δ, ε < 1 and C ε < 1.

Suppose two distinct integer targets p < q, with q − p ≤ W, are hit by the
same generator: p < a L ≤ p + ε and q < b L ≤ q + ε. Then a < b. Set
d = b − a and k = q − p. The length bounds give 0 < d ≤ C and
|d L − k| < ε. The choice of δ forces d L = k. But then

\[
0 < d(aL-p) = ak-pd \le d\varepsilon < 1,
\]

contradicting the fact that ak − pd is an integer. Thus a generator cannot hit
two of those intervals. Pigeonhole gives the contradiction when a bounded
block of targets contains more points than there are generators. Forward
bounded gaps supply such blocks uniformly far out.

This proof avoids the rational/irrational split in the cited arithmetic
argument. Its geometric application reuses
`CriticalLevels.primeLevels_finite`, `Geodesics.exists_prime_representative`
and `LoopEnergy.energy_iterate`: finitely many prime images give finitely many
positive prime lengths, and every closed geodesic length is an integer
multiple of one of them. Dividing by the reference length reduces the
length-production hypothesis to the proved arithmetic contradiction.

The point-cover criterion separately reuses
`AvoidPoint.exists_point_not_mem_closedGeodesic`, which already applies in
dimension two. No new assumption about curve shortening is used in that step.

### Constructing the repeated local family

Let φ : X × Y → Λ be a continuous family of actual H¹ loops, with basepoint
depending only on x ∈ X. For k ≥ 1, the implementation constructs

\[
\Phi_k(x,y_1,\ldots,y_k)
=\phi(x,y_1)*\cdots*\phi(x,y_k)
\]

with each loop occupying exactly 1/k of the unit period. The Lean indexing
uses `k = m + 1` to exclude the empty concatenation. Recursively, a block of
m + 1 loops is joined to the last loop at time (m + 1)/(m + 2). The existing
strong H¹ continuity of the two-loop join proves joint continuity, including
variation of x. Restriction to the first and second time intervals recovers
both joined loops; induction therefore recovers every block. Thus Φ_k is
injective whenever φ is. If X and Y are compact, continuity and injectivity
make Φ_k a closed topological embedding.

The center is checked at the level of paths, not just their energies:
Φ_k(x,y,…,y) is exactly `SobolevIteration.iterateSphere (φ(x,y)) k`.
The proof compares the H¹ representatives on the two time intervals and uses
the original loop's period to identify the last block.

The two-loop energy identity gives, by induction,

\[
E(\Phi_k(x,\mathbf y))=k\sum_{i=1}^k E(\phi(x,y_i)).
\]

If every input has energy ≤ L and one input has energy ≤ L − δ, the output
has energy ≤ k²L − kδ. In particular a unique strict maximum of the original
family remains a unique strict maximum at its repeated center: when the
original center has energy L, the exact formula gives energy k²L there. For a compact
boundary set B ⊆ Y on which E(φ(x,y)) < L, with X compact, the maximum of
E ∘ φ on X × B is strictly below L. This produces δ > 0 **before k is
chosen**. Every product face with at least one y_i ∈ B then has the same
amplified deficit kδ, uniformly for all k.

There is also a constructed map of topological pairs. Given an original
boundary subset S ⊆ X × Y on which E ∘ φ < l², with E ∘ φ ≤ l² everywhere,
define the product boundary by the existence of an i with (x,y_i) ∈ S.
For every a > kl, `familyPairMap` maps the entire parameter domain into t_a
and this boundary into t_(kl). Thus the family supplies a genuine relative
homology map. The code does not assume its energy filtration or replace the
pair by a formal symbol. Nonvanishing on homology remains a separate step.

These are constructions and estimates for genuine loop families. They do
not construct the initial surface family φ, identify its topological class
as the required nonzero class in the loop-space sublevel, or establish the
needed Morse charts for all its iterates. The connector and explicit filling
steps below are implemented. The local-class construction below supplies a
generator once the geometric coordinate and energy conditions are verified.

### Constructing the nonzero local critical class

Let D be the closed unit disk in R^q and S its boundary. Write D* = D \\ {0}.
The identity of D and the inclusion S → D* form a map of pairs

\[
(D,S) \longrightarrow (D,D^*).
\]

Radial deformation makes S → D* a homotopy equivalence. Tau Ceti's
relative-homology comparison theorem, applied to this equivalence and the
identity of D, proves that the displayed pair map induces an isomorphism
in every degree. Tau Ceti also identifies H_q(D,S;K) with K. Define u as
the inverse image of 1. Since K is a field, u ≠ 0, and its image in
H_q(D,D*;K) is nonzero. This includes q = 0, where S and D* are empty.

Now let E : X → R, f : D → X and r : X → D be continuous maps where
required, with r ∘ f = id. Assume E(f(x)) < c on S and

\[
r(y)=0 \quad\Longrightarrow\quad c\le E(y).
\]

Every point of A = {E < c} therefore projects into D*. The actual maps of
pairs (D,S) → (X,A) → (D,D*) compose to the map above. If f_*u were zero,
its projection would also be zero, contradicting the disk calculation.
`localClass_ne_zero` proves this argument. No nonzero class or homology
injectivity is included among its hypotheses.

In product coordinates X = D × Z, take f(x) = (x,z₀) and r(x,z) = x.
It suffices for E(·,z₀) to have a strict maximum at 0 and for E(0,·) to
have a minimum at z₀. The transverse space Z is arbitrary; the maximum
can be degenerate. `chart_class_ne_zero` transports this construction
through a homeomorphism to the original energy coordinates. The executable
readback verifies the concrete degenerate saddle E(x,z) = z² − ‖x‖⁴
with q = 2 and coefficients K = Z/2Z.

If f has its strict maximum at the center p = f(0), every other disk point
has energy below E(p). Thus f already takes values in C = {E < E(p)} ∪ {p}.
Restricting the same detector proves a nonzero class in H_q(C,{E < E(p)};K),
not merely in the full coordinate neighborhood. This is
`criticalClass_ne_zero`, also checked on the concrete degenerate saddle.
If E is continuous and U is an open neighborhood of p, U ∩ C and
{E < E(p)} are open in C and cover C. Tau Ceti's excision theorem gives

\[
H_q(U\cap C, U\cap\{E<E(p)\};K)
\cong H_q(C,\{E<E(p)\};K).
\]

`isIso_critical_excision` constructs this isomorphism as the map induced
by the actual inclusion. Neither this result nor the coordinate detector
proves that the class remains nonzero in an arbitrary larger energy
sublevel. For the surface theorem, the remaining work includes constructing
the needed geometric charts for the repeated family and proving the passage
from local classes to the orbit and sublevel pairs used by the filling.

### From polygon neighborhoods to actual loop local classes

Fix a polygon model valid below the energy cut a². Let b send a short
polygon to its broken geodesic, and let s sample an H¹ loop at the vertices.
The existing geometric construction proves

\[
s\circ b=\operatorname{id},\qquad E(bq)=E_{\mathrm{poly}}(q),
\qquad E_{\mathrm{poly}}(su)\le E(u).
\]

For a reference polygon p with E_poly(p)<a², the loop critical carrier
C_b={E<E(bp)}∪{bp} is entirely below a², so s is defined there. The strict
energy inequality sends its lower part to the polygon lower part; at the
distinguished point, s(bp)=p exactly. Thus b and s give actual maps of
critical pairs whose composition is the identity on the polygon pair.
Applying relative singular homology proves that b_* has a left inverse,
hence is injective in every degree over any field.

Suppose the coordinate detector and maximal disk are available only in an
open polygon neighborhood U of p. First apply `criticalClass_ne_zero` in U.
The explicit `criticalInclusion` flattens the nested subtypes and induces an
isomorphism by excision. Composing it with b gives `localDiskToLoops`; its
underlying loop at a disk point x is exactly b(f(x)). Injectivity of both
homology maps proves `localDiskToLoops_class_ne_zero`. The input hypotheses
are the geometric maximum, central-fiber minimum and coordinate identities,
not an assumed nonzero class or an assumed comparison map.

Finally, for any actual closed geodesic g below a², choose the number of
vertices larger than the thresholds for uniform short spacing, criticality
of the sampled polygon and exact reconstruction. Their maximum plus one
satisfies all three requirements. This constructs `GeodesicModel F g a`:
the polygon is critical, has energy E(g)<a² and its broken loop equals the
original Sobolev representative of g, including parametrization.

These results establish the passage from polygon local classes to loop
point-local classes. The required maximal disks at the geodesic iterates,
their passage to orbit-local and upper-sublevel classes, and the surface
minimax/dynamics alternatives remain to be proved. In particular, this
split injection alone does not imply the n = 2 infinitude assertion.

### Actual splitting charts and small maximal disks

`nonempty_regularGeodesicModel` strengthens the exact polygon construction:
the sampled polygon has no zero edges. The uniform sample facts for all
phases of a regular closed geodesic supply this condition. Taking the maximum
of their sampling threshold and the energy-cut spacing threshold provides
both properties at once. This makes the existing smooth polygon splitting
lemma applicable without a nondegeneracy assumption.

Restrict the product sphere chart to the open space of short polygons,
translate its central coordinate to zero, and compose it with the analytic
splitting homeomorphism. `exists_short_splitting` gives a chart e on that
actual polygon space and a reduction map σ with σ(0)=0 such that

\[
E_{\mathrm{poly}}(x)
=E_{\mathrm{chart}}\bigl(b+\sigma(P_0 e(x))\bigr)
 +\tfrac12\langle H e(x),e(x)\rangle.
\]

Here b is the original central coordinate, H its Hessian and P₀ the
orthogonal projection onto ker H. `GeodesicMorseModel` packages these data
together with the exact original parametrized broken loop and strict energy
cut. Its existence is proved for every actual closed geodesic.

The disk-construction theorem starts from a local product chart e with
e(p)=(0,z₀) and E(x)=R(e(x)₁)+Q(e(x)₂), a strict maximum germ of R at zero,
and Q(z₀)≤Q(z) whenever (0,z) lies in the chart target. Choose ε>0 such that
every (v,z₀) with ‖v‖<ε lies in that target and satisfies the maximum
condition. Put ρ=ε/2 and define

\[
f(u)=e^{-1}(\rho u,z_0),\qquad
r(x)=\operatorname{clip}(\rho^{-1}e(x)_1),\qquad
\operatorname{clip}(v)=\frac{v}{\max(1,\lVert v\rVert)}.
\]

Radial clipping is continuous, fixes the closed unit disk and takes the
value zero exactly at zero. Thus f is defined on the whole closed disk,
f(0)=p, r∘f=id, E(f(u))<E(p) for u≠0, and r(x)=0 implies E(p)≤E(x).
These are the actual fields of `MaximalDiskData`; neither map is an input
to `nonempty_maximalDiskData_of_normalForm`. The readback constructs such
data for the degenerate saddle z²−‖v‖⁴ in a proper open coordinate ball,
and separately checks radial clipping in dimension zero.

Composing f with broken geodesics gives an H¹-continuous family. Sampling
and r recover its disk parameter, so it is injective. Compactness of the
disk makes it a closed embedding. Its center and strict energy maximum
are exact. Excision and the polygon-to-loop injection then give the nonzero
class in the loop critical pair, as proved by
`exists_nonzero_loopClass_of_normalForm`.

The two constructions have distinct hypotheses. An arbitrary geodesic's
Hessian splitting does **not** assert that its reduced energy has the
required strict maximum. The phase-transverse chart and splitting are now
constructed below. Proving the extremum conditions for the selected geodesic and its iterates,
and carrying the class into the orbit and upper-sublevel pairs remain open.
The surface minimax and dynamics must also produce and cover those cases.

### Spectral coordinates and removal of one phase direction

Let T be a symmetric operator on a finite-dimensional real inner product
space V. In its ordered orthonormal eigenbasis, write λᵢ for the eigenvalues
and xᵢ for the coordinates of x. The new module proves

\[
\langle Tx,x\rangle=\sum_i\lambda_i x_i^2.
\]

Let U be the span of the eigenvectors with λᵢ≤0, and W the positive spectral
subspace. Disjoint coordinate supports make U and W orthogonal. Their sum
is V, so addition U×W→V is an actual continuous linear equivalence.
Moreover, U=V⁻⊕ker T and dim U=dim V⁻+dim ker T. The quadratic form is
nonpositive on U and nonnegative on W. On U it vanishes exactly when Tx=0:
every summand is nonpositive, so a zero sum forces every nonzero-eigenvalue
coordinate to vanish.

Suppose an open chart e sends a point p to zero and gives

\[
E(x)=R(P_0 e(x))+\tfrac12\langle Te(x),e(x)\rangle,
\]

where P₀ is the actual orthogonal projection onto ker T. Assume R restricted
to ker T has a strict local maximum at zero. For u∈U put

\[
A(u)=R(P_0u)+\tfrac12\langle Tu,u\rangle.
\]

If P₀u≠0, strict maximality of R and the nonpositive quadratic term give
A(u)<A(0), for small u. If P₀u=0 and u≠0, then Tu≠0, since a vector in the
kernel equals its kernel projection. The quadratic term is therefore
strictly negative, giving the same inequality. This proves a germ of strict
maximality on all of U, including when the kernel is zero-dimensional.

The kernel projection vanishes on W. Invariance and orthogonality remove the
mixed quadratic terms, giving the product form

\[
E(e^{-1}(u+w))=A(u)+\tfrac12\langle Tw,w\rangle.
\]

An orthonormal basis identifies U with the standard Euclidean disk model.
The previously proved small-disk theorem now constructs the disk and
detector from these coordinates; the transverse minimum follows from
positivity on W. Neither a disk map nor a central-fiber minimum is an extra
input to this spectral theorem. An executable example checks the genuinely
degenerate maximum −‖x‖⁴ on ℝ², with T=0 and disk dimension exactly two.

For phase removal, fix v≠0 with Tv=0 and set S=v⊥. Symmetry implies
⟨Tw,v⟩=⟨w,Tv⟩=0. Thus T restricts to a continuous symmetric operator T_S
on S. An explicit linear equivalence identifies ker T_S with the orthogonal
complement of v inside ker T. The dimension theorem for an orthogonal
complement then gives

\[
\dim\ker T_S+1=\dim\ker T.
\]

The second executable example starts with the zero operator on ℝ³ and
checks that its actual restriction perpendicular to any nonzero vector has
nullity exactly two.

### The actual phase curve and transverse splitting

For a regular closed geodesic γ, choose one sufficiently fine N that works
uniformly for every phase. The polygon qθ has vertices γ(i/N+θ). Uniform
sampling proves that it is short, has no zero edges, is stationary, and that
its broken geodesic is exactly the shifted original loop. Its energy is
therefore independent of θ. In the fixed product sphere chart at q₀ set

\[
c(\theta)=\operatorname{chart}_{q_0}(q_\theta)-b,\qquad
v=c'(0),\qquad b=\operatorname{chart}_{q_0}(q_0).
\]

Smoothness of γ and the sphere charts makes c smooth. Regularity at the
zeroth vertex implies v≠0. Stationarity is proved in this fixed chart, not
only in a moving chart centered at qθ. Differentiating
∇E(b+c(θ))=0 at zero gives Hv=0 for the actual polygon Hessian H.

Let S=v⊥. The derivative at (0,0) of (θ,w)↦c(θ)+w is
(τ,w)↦τv+w, a continuous linear equivalence ℝ×S→V. Mathlib's inverse
function theorem supplies a local inverse. Composing with the actual
short-polygon chart gives a nonlinear phase/transverse chart e with

\[
e(q_\theta)=(\theta,0),\qquad
\operatorname{chart}_{q_0}(e^{-1}(0,w))=b+w.
\]

Consequently the phase-zero energy f(w)=E(b+w) is exactly the polygon
energy and the Sobolev energy of its broken loop. This does not assert
phase independence away from the critical axis.

The projected gradient G_S(w)=P_S∇E(b+w) represents df on a neighborhood
of zero. It is C², vanishes at zero, and has derivative
P_SH|_S=H|_S: symmetry and Hv=0 imply that H already maps into S.
Uniqueness of derivatives identifies H|_S with the genuine Hessian of f.
Its nullity is exactly one less than that of H. Applying the existing
degenerate splitting lemma on S produces a reduction σ and a local
homeomorphism Ξ such that

\[
f(w)=f\bigl(\sigma(P_{\ker H_S}\,\Xi(w))\bigr)
      +\tfrac12\langle H_S\Xi(w),\Xi(w)\rangle.
\]

These constructions require no nondegeneracy or isolation hypothesis.
Readback checks a nonlinear curve t↦t+t², the actual Hessian/nullity
identities on S², and the exact broken-loop energy on the constructed slice.

### Comparing the actual transverse reductions under iteration

Let J_m repeat the polygon-coordinate vector m times. The existing polygon
identities give

\[
\langle J_mx,J_my\rangle=m\langle x,y\rangle,\quad
H_mJ_m=mJ_mH,\quad E_m(b_m+J_mx)=m^2E(b+x).
\]

The iterated phase vector is J_mv, which is nonzero by injectivity. Set
S=v⊥ and S_m=(J_mv)⊥. Conformality gives J_m(S)⊆S_m and
P_{S_m}J_m=J_mP_S. For the latter identity, decompose x into its S-component
and a multiple of v; their images are respectively perpendicular and parallel
to J_mv. Thus the genuine slice gradients and Hessians satisfy

\[
G_m(J_mw)=mJ_mG(w),\qquad A_mJ_m=mJ_mA.
\]

Both full kernels lose exactly one dimension on restriction. When full
nullity is preserved, the injective restricted map therefore induces an
actual continuous linear equivalence J_m:ker A→ker A_m. This constructs
the map, rather than choosing an unrelated equivalence of equal-dimensional
spaces. Restriction also preserves the negative index: the removed line
lies in the kernel and contributes no negative quadratic direction.

Write P₀ for the kernel projection. Choose a reduction σ using the local
inverse of x↦P₀x+(1−P₀)G(x), and similarly σ_m for the iterate.
The stored inverse identities, projected-gradient
identity and uniqueness of the local inverse give

\[
f_m(\sigma_m(J_mz))=m^2f(\sigma(z)),\qquad z\in\ker A
\]

near zero. The kernel equivalence carries a neighborhood onto a neighborhood,
and m²>0, so a strict maximum of the base reduced function propagates to the
iterated reduced function. The splitting lemma is applied to these same
chosen reductions. It supplies a maximal disk for the actual iterated slice
energy, of dimension ind(H_m)+dim ker H_m−1. No change of reduced function
is silently made between the comparison and the disk construction.

Finally the monodromy theorem provides L≥1 such that nullity depends only
on gcd(k,L). For every positive base iterate d and every j≥0,

\[
\gcd\bigl(d(2Lj+1),L\bigr)=\gcd(d,L).
\]

Hence m_j=2Lj+1 preserves the nullity of that base iterate. These multipliers
are odd, and for every t≥0 some m_j lies in [t,t+2L+1]. Sampling the actual
geodesic already supplies the twist condition used by monodromy. Consequently
one base reduced maximum gives the maximal disks along this entire
bounded-gap progression; no separate maximum is assumed for each iterate.

The readback instantiates these constructions on S², checks exact equality
with the earlier transverse energy and Hessian, and derives the odd progression
without a nullity-period hypothesis.

**Remaining geometric work.** A suitable base geodesic and its reduced
maximum still have to be obtained. The required index-growth and orientation
control, nonvanishing in orbit and upper-sublevel pairs, and the surface
minimax and dynamics branches also remain open. A class on a transverse slice
does not automatically give the required class in those larger pairs.

### Actual iteration on point-critical homology

For a continuous energy E and a critical point p, the point-critical pair is

\[
C(E,p)=(\{E<E(p)\}\cup\{p\},\{E<E(p)\}).
\]

Suppose f sends p to p' and the strict lower part into the strict lower
part. If f has an energy-compatible left inverse on an open neighborhood
V of p', restrict the source to U=f⁻¹(V). Excision identifies both local
critical pairs with the global point-critical pairs. The local maps satisfy
r∘f=id, so their homology maps compose to the localization isomorphism.
It follows that the actual global map f induces an injection. The proof
constructs these maps and checks their commutative diagrams; injectivity
is not an input.

For repeated polygons, let L be actual repetition in centered product
sphere coordinates, and let π be orthogonal projection onto its image
followed by its inverse there. The polygon iteration normal form gives,
near the repeated polygon,

\[
E_m(z)=m^2 E_0(\pi z)+\tfrac12\langle H_m w(z),w(z)\rangle,
\qquad w(z)\in(\operatorname{im}L)^\perp.
\]

Nullity preservation supplies this normal form. Index additivity and index
preservation make the normal quadratic form nonnegative. Therefore
m²E₀(πz)≤E_m(z). Choose an open neighborhood on which this inequality holds
and π lands in the base chart. Composing π with the genuine product sphere
charts gives a continuous local retraction r of sphere polygons. It satisfies
r∘iteration=id and m²E₀(r(y))≤E_m(y). Since m>0 and the center energy scales
exactly by m², the retraction preserves the strict lower parts. The preceding
excision argument gives `polygonIterationPair_homology_injective` in every
homology degree over any field.

For a geodesic with mean index Δ=0, the iteration estimate gives I(m)≤n.
The actual sampled Hessians prove I(d)≤I(dm) for positive d,m. A bounded
natural-valued index attains a maximum; choose a positive d attaining it.
Then I(dm)=I(d) for every positive m. Monodromy supplies an integer L≥1 with
nullity depending only on gcd(k,L). Thus m=2Lj+1 preserves the nullity of
the d-fold iterate, because gcd(dm,L)=gcd(d,L). One sufficiently fine actual
sampled model supports all these comparisons. Applying the local retraction
proves `exists_zero_mean_iteration_injections`. The readback also checks
that this odd progression has bounded forward gaps.

These are point-critical homology statements. They neither construct a
zero-mean geodesic with the required nonzero class nor prove that its class
survives in a critical-orbit pair or an upper energy sublevel. In particular,
this result cannot yet be substituted for the geometric nonvanishing input
of the filling argument. The concrete readback tests the local retraction
on the degenerate saddle y²−x⁴ using a proper open square, and specializes
the zero-mean endpoint to actual S² geodesics with mod-two coefficients.

### A local deformation and the period-rotation action

The stronger iteration result uses the same normal form, now retaining its
local inverse. Write P for orthogonal projection onto repeated directions,
N=1−P, and e for the inverse-function-theorem chart supplied by the normal
form. In centered coordinates it satisfies

\[
f(z)=f(Pz)+\tfrac12 Q(Ne(z)),\qquad Pe(z)=Pz,
\]

with Q nonnegative on the normal space. Choose a ball in the target of e
whose inverse image lies in the domain of these identities and in the
prescribed sphere-chart domain. Shrink the source so that both e(z) and
e(Pz) belong to the ball. Define

\[
H(t,z)=e^{-1}\big((1-t)e(z)+t e(Pz)\big).
\]

Convexity of the ball keeps H defined throughout the interval. The projection
identity gives PH(t,z)=Pz. Applying the energy identity to Pz gives
Q(Ne(Pz))=0. For a nonnegative quadratic form,

\[
Q((1-t)x+ty)=(1-t)Q(x)+tQ(y)-t(1-t)Q(x-y)\le Q(x)
\]

when Q(y)=0 and 0≤t≤1. Consequently f(H(t,z))≤f(z). The endpoints are z
and Pz, and zero is fixed throughout. This argument needs no separate proof
that e fixes the repeated directions, and even allows a semidefinite Q.

Composing this deformation with the actual product sphere charts gives a
homotopy from the neighborhood inclusion to iteration followed after its
local retraction. It fixes the distinguished point and preserves the strict
lower part, so it is a homotopy of the actual point-critical pairs. Excision
makes the neighborhood inclusion an isomorphism. Its factorization on
homology proves surjectivity of iteration; the previous injection therefore
becomes an isomorphism, with no inverse on homology assumed.

For m repetitions of an N-vertex polygon, let ρ rotate by N vertices.
It preserves the actual polygon energy and fixes every repeated polygon.
Thus ρ∘iteration=iteration already as maps of pairs. Surjectivity of the
iteration homology map yields ρ*=id. This is a direct alternative to a sign
calculation for this stable case.

The rotation here is by the period of the chosen base polygon. If that base
is itself an iterate, this does not identify the action of the smaller prime
period. Nor does it prove that inclusion into the full critical orbit is
injective. The zero-mean argument below removes the base change and hence
resolves this smaller-period issue when starting with a prime zero-mean
geodesic. The orbit exact sequence, rotation comparisons in other branches,
upper-cut nonvanishing, and geometric existence steps remain open. The relevant
orbit-inclusion criterion is [DPMMS, Lemma 4.4](https://arxiv.org/html/2002.00415v2#S4.SS3),
which uses an isolated prime geodesic and odd iterates with rational coefficients.
The readback checks the nonlinear normal energy (x+x²)²/2 on a bounded domain,
actual stable S² polygon iteration and rotation over rational coefficients,
and the zero-mean odd progression with its bounded gaps.

### Zero mean index without changing the geodesic

Let the unnormalized chain form be

\[
Q_N(w)=\sum_{j\in\mathbb Z/N}\beta_j(w_j,w_{j+1}),
\qquad N\ge2,
\]

and let I(m) be the negative index of its m-period repetition. Denote by
J(m) the negative index after requiring w₀=0. Joining two based variations
has no endpoint matching constraint and preserves the direct-sum quadratic
form. The actual joining map is injective, so

\[
J(m)+J(k)\le J(m+k),\qquad kJ(m)\le J(km)\le I(km).
\]

If every I(r)≤B, taking k=B+1 proves J(m)=0 for every positive m. Hence
every based chain form is nonnegative.

Suppose a periodic variation w has Q_N(w)<0. Repeat w m times, then replace
only vertex zero by zero. The repeated value before this cut is mQ_N(w).
Only the outgoing and incoming edges at the cut change, giving exactly

\[
Q_{mN}(\widehat w)=mQ_N(w)+C(w),
\]

where

\[
\begin{aligned}
C(w)={}&\beta_0(0,w_1)-\beta_0(w_0,w_1)\\
 &+\beta_{-1}(w_{-1},0)-\beta_{-1}(w_{-1},w_0).
\end{aligned}
\]

The correction is independent of m. A sufficiently large integer m makes
the expression negative, contradicting J(m)=0. Thus Q_N is nonnegative.
Apply the same argument to the pair forms of every positive iterate;
the existing exact reindexing of iterated chains identifies its subsequent
indices with I(dm). It follows that I(d)=0 for all d≥1.

For a closed geodesic, the existing mean-index estimate gives
|I(m)−mΔ|≤n. If Δ=0, all positive-iterate indices are at most n. The new
chain result, applied to actual uniformly sampled polygon Hessians,
therefore proves I(m)=0 for every m≥1. Conversely, positive index at one
iterate forces Δ>0, and the lower estimate I(k)≥kΔ−n proves eventual
growth beyond every fixed bound.

Monodromy supplies an odd progression 2Lj+1 preserving nullity from the
original polygon. Since both indices are zero, the actual deformation and
homology comparison apply directly. The point-critical isomorphism is now between the chosen polygon models
of γ and γ^(2Lj+1), without replacing γ by a maximizing base iterate.
Rotation by the original base period fixes all these polygon classes. When γ is prime,
this is exactly its prime-period rotation. The mapping-torus detector below
provides the next local topological step; the actual orbit comparison and
existence/nonvanishing inputs are still required.

The readback tests an explicit boundary-cost obstruction: for
β(x,y)=(x−y)²−x²/2 on a two-vertex chain, the based form is nonnegative,
but repeating the constant variation three times and cutting vertex zero
gives value −1/2. Further examples check eventual index growth and the
original-geodesic S² isomorphism/rotation endpoint over rational coefficients,
including the odd progression and bounded gaps.

### An invariant detector on the period-rotation mapping torus

Let P be the sampled original polygon and let Q be its m-fold repetition.
Assume that their index and nullity agree. The existing normal-form
construction supplies an open neighborhood V of Q, a retraction r to the
base polygon space, and an energy-decreasing homotopy H from the inclusion
of V to i ∘ r, where i is actual polygon repetition. In centered product
sphere coordinates, the retraction is exactly

\[
r(y)=e_P^{-1}\bigl(\operatorname{res}\,
  \pi_{\mathrm{rep}} e_Q(y)\bigr).
\]

Here π_rep is orthogonal projection onto the repeated vectors, and res
keeps their first period. Rotation R by N vertices is an isometry in these
coordinates and fixes every repeated vector. For w in the repeated
subspace, ⟨Rz,w⟩=⟨z,w⟩; uniqueness of orthogonal projection gives
π_rep Rz=π_rep z. The centered sphere chart intertwines these two rotations.
Consequently r(Ry)=r(y) whenever both points belong to V.

Replace V by the finite intersection W of its inverse images under all
base-period rotations. This is an open neighborhood of Q, contained in V
and invariant under R. Restrict r and H to W. Write

\[
C=\{y\in W:E(y)<E(Q)\}\cup\{Q\},\qquad
A=\{y\in W:E(y)<E(Q)\}.
\]

The restriction μ=R|C is a genuine homeomorphism. Form the topological
mapping torus T_μ=(C×ℝ)/((μx,t+1)∼(x,t)), relative to the image of A×ℝ.
Tau Ceti supplies this quotient, its topology and its height-zero fibre
inclusion j. Invariance of r constructs the continuous detector
r̄([x,t])=r(x), with the strict lower subspace mapped to the base lower
subspace. Thus r̄ ∘ j=r as maps of pairs, before applying homology.

The energy-decreasing homotopy gives J_*=i_* r_*, where J is the inclusion
of the local point-critical pair into the global polygon point-critical
pair. Excision makes J_* an isomorphism, so r_* is injective. The identity
r̄_* j_*=r_* then proves that j_* is injective in every degree over every
field. This proof needs neither a Wang sequence nor an orientation-sign
formula. The actual projection and the homotopy, rather than an assumed
homology injection, supply the detector.

For a given zero-mean geodesic, the preceding zero-index theorem and
monodromy supply these geometric hypotheses along one odd bounded-gap
progression starting from the original geodesic. The readback checks the
S² endpoint over ℚ and preservation of an arbitrary nonzero local class
by the actual quotient fibre map.

**Scope:** this is an explicit local polygon mapping torus. A comparison
which carries this detector to the actual Sobolev critical-orbit pair has
not been constructed. In particular, an injective map into this model
alone does not prove that a subsequent map to the loop-space orbit pair
is injective. Upper-cut nonvanishing, the required geodesic and local
class, and the remaining surface dynamics are also still open.

### Short connectors and the enlarged family

The existing `SegmentContinuity.exists_segment_path` supplies a uniform
neighborhood of the diagonal and an H¹-continuous shortest path w from P to Q.
Its energy is the actual `SphereDistance.minEnergy F P Q`. The new construction
uses w and its reverse to connect loops u at P and v at Q. For positive
durations a, b, c it follows u, w, v, reverse(w), allocating times a, c, b, c
before rescaling to one period. Endpoint matching proves that this is a
sphere loop. Three applications of the existing H¹ concatenation operator
prove continuity. Reversibility gives the exact identity

\[
E(\Psi)=(a+b+2c)\left(\frac{E(u)}a+\frac{E(v)}b+
                     \frac{2E(w)}c\right).
\]

For groups of a and b loops, the repeated-block identity cancels the
denominators: E(u)/a and E(v)/b become sums of original block energies.
Write k=a+b and H=2c(1+L+2c). If E(w)≤c², k≥1, and the two sums total at
most kL−D with D≥0, the proved estimate is

\[
E(\Psi)\le k^2L+k(H-D).
\]

Thus a transverse face with one block losing δ has energy below k²L when
H<δ. On a base face, every block in one group loses δ, so D=aδ or bδ.
The code supplies N with H<(r+1)δ for every r≥N. This controls both base
faces once both groups are large enough. With L=l² and H<2lε, the entire
family lies in the actual sublevel t_(kl+ε).

The connector hypotheses can be realized uniformly: choose c>0 with H
below the desired positive budgets, then use the existing quadratic bound
on minimal path energy to construct ρ>0. Whenever the basepoints are less
than ρ apart, the chosen connector has energy <c². Both c and ρ are chosen
before the block counts. No abstract energy function replaces the actual
loop energy in these statements.

### Removing the diagonal pauses

On the diagonal P=Q, the chosen minimal connector has energy zero.
`shortPath_self` turns it into an actual periodic H¹ loop and uses the
existing zero-energy rigidity theorem to prove that it is exactly the
constant path at P. This establishes equality of paths, not just energies.

For d≥0, let u_d be u with a terminal pause occupying d/(a+d) of the
normalized period, and similarly let v_d use d/(b+d). Join these loops at
split (a+d)/(a+b+2d). Existing strong H¹ padding continuity includes d=0;
existing variable-split continuity applies since the split remains strictly
between zero and one. Their composition gives joint continuity in d,u,v,
including variation of the common basepoint. Its actual energy is

\[
E(H_d(u,v))=(a+b+2d)\left(\frac{E(u)}a+\frac{E(v)}b\right).
\]

Set d=(1-t)c for t∈[0,1]. The coefficient in parentheses is nonnegative,
so energy never exceeds its starting value. The equality of the constant
connector paths identifies H_c with the diagonal of `shortLoop`. At t=1,
zero-padding identities identify H_0 with the ordinary weighted join of
u and v. No continuity assertion is inferred merely from an energy bound.

For any parameter family φ:X→{(u,v):u(0)=v(0)} and boundary B⊆X, assume
H_c∘φ lies in t_L on X and t_l on B, with 0<l≤L. The construction supplies
an actual homotopy of maps of pairs (X,B)→(t_L,t_l). Tau Ceti's homotopy
invariance therefore proves equality of the induced relative singular
homology maps in every degree. This is the boundary compatibility needed
to transport a class through the pause removal.

Finally, when u and v are respectively the k-fold and l-fold iterates of
one loop and a=k, b=l, the final weighted join is exactly the (k+l)-fold
iterate. The proof compares the H¹ representatives on each time interval;
periodicity removes the integer shift on the second interval. The concrete
S² readback checks unequal groups k=2 and l=3, giving the five-fold iterate.

### Explicit filling by sliding the second base interval

For the surface branch, use an interval I for the transverse base parameter
and a transverse parameter space Y with specified boundary BY. Set
k=r+1, h=s+1 and m=k+h. The actual enlarged family has domain

\[
I\times I\times Y^k\times Y^h.
\]

It joins the two repeated groups with the already constructed short paths.
`EnergyBounds` records a bound E(φ(x,y))≤l², positive deficits on the
transverse and interval-endpoint faces, and the inequalities that make those
deficits pay the connector overhead. The nearby-basepoint condition and
uniform connector-energy bound remain explicit. The preceding budget
lemmas provide the duration/radius choices and eventual block thresholds.
The implemented extension ψ maps the whole domain into t_{ml+ε} and every
boundary face into t_{ml}.

On the diagonal domain D=I×Y^k×Y^h, let B consist of either endpoint of I
or a transverse boundary coordinate. Define

\[
H(t,(x,\mathbf y,\mathbf z))
 =\psi(x,(1-t)x+t,\mathbf y,\mathbf z).
\]

At t=0 this is the diagonal connector family. At t=1 the second base
coordinate is an endpoint, so the entire image is in t_{ml}. If a point
starts on B, its first base coordinate or its transverse boundary coordinate
stays fixed, so H preserves the lower sublevel throughout. This is an
explicit homotopy of pairs, not an assumed filling or a dimension count.

The endpoint's ambient map factors through the lower sublevel. The relative
singular chain map is therefore zero: after precomposing with the quotient
from ambient chains, naturality factors it through the chains of the
subspace, which the relative quotient kills. The quotient is an epimorphism,
so cancellation proves the chain-map equality. Homology functoriality and
homotopy invariance then kill the diagonal map in every degree over any field.
The proved pause homotopy transfers the same vanishing to the ordinary
weighted join. No homeomorphism from a product of disks to a larger disk is
needed for this filling step.

The ordinary family has energy at most m²l². It consequently defines a map
into (t_a,t_{ml}) for every a>ml. Raising the cut to ml+ε gives exactly the
map just proved zero on homology. If the map into (t_a,t_{ml}) is nonzero,
the sublevel inclusion cannot be injective. The extraction theorem supplies
an actual closed geodesic with ml<a≤length≤ml+ε. The concrete S² readback
uses k=2, h=3 and coefficients Z/2.

**Remaining geometric work.** The initial local family with the stated
quantitative bounds and a nonzero induced local class still has to be
produced for the required iterates. The simple-curve minimax and remaining
surface-dynamics branches are also required for the full theorem.

### Homological extraction and the disk-filling shortcut

Write `t_a` for the actual H¹ loop space sublevel √E < a together with the
constant loops. Fix c ≤ a ≤ b with a > 0. Suppose no regular closed geodesic
has length in [a,b]. The proved critical-loop regularity theorem then rules
out every tangent-critical H¹ loop with energy in [a²,b²]. Polygonal Birkhoff
descent supplies a homotopy of `t_b`, decreasing energy at every time, whose
endpoint maps `t_b` into `t_a`. Every lower sublevel is preserved throughout.
Consequently the inclusion of pairs

\[
(t_a,t_c) \longrightarrow (t_b,t_c)
\]

is a homotopy equivalence. Tau Ceti's homotopy invariance makes its relative
singular homology map an isomorphism over any field. Contrapositively, a
nonzero class killed by this inclusion gives a regular stationary closed
geodesic of length in [a,b]. There is no finite-spectrum or nondegeneracy
assumption in this extraction theorem.

The filling step uses a further library shortcut. Let a map of pairs
`f : (D^q,∂D^q) → (t_a,t_c)` induce a nonzero map on H_q. Suppose its
composition into `(t_b,t_c)` factors as

\[
(D^q,\partial D^q) \xrightarrow{j}
(D^r,\partial D^r) \xrightarrow{G} (t_b,t_c),
\qquad r\ne q.
\]

Tau Ceti proves H_q(D^r,∂D^r) = 0. Functoriality forces the composite to
vanish, so the sublevel inclusion cannot be injective. This avoids writing
an explicit singular chain filling. It does **not** construct `f`, `j` or
`G`, establish the energy bounds encoded by their target pairs, or prove
that `f` induces a nonzero map. Those are geometric obligations.

The equality of the filling diagram may now be replaced by an actual
homotopy of pairs between the two composites. The proved pause removal is
compatible with this form of the criterion: relative homotopy invariance
makes the induced homology maps equal, and the same zero-target-homology
argument gives noninjectivity and then an actual closed geodesic.

For the odd-iterate criterion, take `c = m l`, choose `m l < a ≤ b ≤ m l + ε`,
and provide such a dying class for every sufficiently large odd m. Extraction
gives `m l < √E(g) ≤ m l + ε`; the already proved arithmetic criterion then
gives infinitely many prime images. The strict inequality is preserved by
choosing the lower extraction cut strictly above `m l`, rather than assuming
that a geodesic at the iterate's original length is a new one.

## Why changing the dimension bound is insufficient

The existing construction writes n = m + 1 and requires 2 ≤ m. Two concrete
uses of that restriction are:

- [NativeConstantUnitFromPathMV.lean](../lean/Finsler/Loop/NativeConstantUnitFromPathMV.lean)
  constructs `original_UNIT` using
  [PathSphereHomologyGap.path_top_zero](../lean/Finsler/Loop/PathSphereHomologyGap.lean).
  The latter theorem requires 2 ≤ m; it does not supply the needed two-sphere
  construction at m = 1.
- [FullHRAbs.mod_one](../lean/Finsler/Residual/FullHRAbs.lean) uses
  `(c * m + 1) % m = 1` for 2 ≤ m to separate residue classes in the resonance
  argument. At m = 1 its left-hand side is 0, so this exact lemma cannot extend
  to that case. A surface proof must replace this argument, not just weaken its
  hypothesis.

## A mathematical source, not a formal proof import

[De Philippis, Marini, Mazzucchelli and Suhr](https://arxiv.org/abs/2002.00415),
Theorem 1.5, prove infinitude for reversible Finsler two-spheres. Their surface
argument uses simple closed geodesics, Birkhoff annulus dynamics and an
iteration/local-homology criterion. A formalization must establish those
constructions for this project's actual metric and Euler–Lagrange equation,
and connect the resulting periodic orbits to its normalized prime image set.

The length-spectrum conversion and prime-image counting steps are now
implemented as above. The missing geometric inputs are still substantial:
the simple-curve minimax construction with its degree-three local homology,
the Birkhoff return-map and twist branch, the original local family and the
coordinate/energy hypotheses needed for its local class, preservation of the
class in the required orbit and sublevel pairs, and any remaining Bangert-branch constructions.
Repeated-block construction, short connectors, all boundary energy bounds,
diagonal pause removal, the explicit interval-base filling, exact polygon
models of closed geodesics, the polygon-to-loop local homology injection,
and extraction of nearby longer geodesics from nonzero repeated classes
are implemented.
The existing polygon shortening on all
loops does not by itself supply the embedded-curve deformation required by
the surface minimax argument.

No matching ready-made theorem was found in the locally pinned Mathlib,
Tau Ceti or Lean Pool sources, or in the inspected OpenAI formalization index.
This is a search result for those sources, not a claim that no formalization
exists elsewhere. Citing the paper does not discharge a Lean goal.

A further search found
[alok/JordanCurveTheorem](https://github.com/alok/JordanCurveTheorem), whose
README describes a formal Jordan separation theorem on Lean v4.33.1. It is a
candidate for the surface separation steps, not a geodesic theorem. Its
sources have not been imported, ported or checked in this package.

## Full implementation roadmap

Status as of 19 October 2026. Difficulty uses a five-point scale. Times are
estimates of remaining active mathematical/formalization work, not elapsed
deadlines or guarantees; unresolved geometric arguments may change them.
The final theorem is not complete, and counting proved lemmas is not a
reliable percentage measure of its completion.

| Stage | Status | Difficulty | Remaining work estimate |
| --- | --- | --- | --- |
| n ≥ 3 theorem and correspondence with the fixed target | ✅ Complete | 5/5 | 0 h |
| Surface length-spectrum obstruction, repeated families, connectors, filling and critical-value extraction | ✅ Complete as component theorems; geometric inputs explicit | 4/5 | 0 h |
| Actual phase slice, transverse Hessian and reduced-maximum iteration | ✅ Complete as component theorems; base maximum explicit | 4/5 | 0 h |
| Zero index at every iterate of a given zero-mean geodesic, original-geodesic point-critical isomorphisms and original-period rotation action | ✅ Complete as component theorems | 4/5 | 0 h |
| Local polygon mapping-torus injection from a rotation-invariant detector | ✅ Complete as a component theorem | 4/5 | 0 h |
| Pass the required transverse/point class to the critical-orbit pair | 🟨 Local mapping-torus injection proved in the zero-mean branch; Sobolev orbit comparison and other branches open | 5/5 | 24–64 h |
| Prove nonvanishing in the upper sublevel needed by the filling argument | ⬜ Open | 5/5 | 24–64 h |
| Construct the simple-curve minimax geodesic and its required local class | ⬜ Open | 5/5 | 60–160 h |
| Formalize the Birkhoff annulus/return-map and remaining Bangert branches | ⬜ Open | 5/5 | 100–260 h |
| Combine all surface branches into the unconditional n = 2 theorem | ⬜ Open | 5/5 | 16–40 h |
| Discharge the proved implications to all n ≥ 2 Finsler and the Riemannian assertion | 🟨 Implications complete; n = 2 input pending | 2/5 | 1–3 h |
| Complete the self-contained FC single file, check the four statements and prose, audit and package both proof variants | ⬜ Open | 3/5 | 8–24 h |
| **Total remaining** | **Unconditional n = 2 still open** | | **233–615 h** |

## Completed connection

The checked theorems are
`finsler_all_dimensions_iff_two_sphere`,
`riemannian_all_dimensions_of_finsler` and
`riemannian_all_dimensions_of_two_sphere`.
They make the remaining assumption visible in the type. Once a proof of
`FinslerTwoSphereAssertion` is supplied, the last theorem yields the full
Riemannian assertion by direct application. Until then, only the n ≥ 3
Finsler theorem and its Riemannian specialization are unconditional local
proofs. The [axiom audit](FCImplicationsReadback.lean) confirms that the
connection uses no `sorryAx` or new axiom.

To reproduce the new checks using a matching existing build:

```bash
python3 scripts/check-two-sphere.py --source-build /path/to/matching/Lean --record
```

This compiles both copies, checks the actual n = 2 criterion types and audits
all 288 theorem dependency graphs in each copy. Ten additional pinned
Tau Ceti modules, including `Singular.DiskSphere`,
`Homotopy.PuncturedStarConvex`, and `Topology.MappingTorus` with its
uncached dependencies, are compiled in the temporary directory;
cached siblings are reused by symlink, and all ten source hashes are checked
against the pinned inputs. Temporary compiled
modules and symlinks are removed; no project or dependency tree is copied.
