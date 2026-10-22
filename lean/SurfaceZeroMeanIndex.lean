import SurfaceChainIndex
import SurfaceIterationEquivalence

/-!
# Zero mean index without replacing the base geodesic

The chain-form cutting argument proves that all indices of a zero-mean
closed geodesic vanish. Thus the original sampled geodesic, without a
preliminary stabilizing iterate, has index-preserving iterations. Combined
with monodromy and the actual local deformation, this gives point-critical
homology isomorphisms and identity action of rotation by the original base
period along a bounded-gap odd progression.

No existence of a zero-mean geodesic or injection into a critical-orbit pair
is asserted here.
-/

namespace Finsler.SurfaceZeroMeanIndex

open CategoryTheory Module QuadraticMap
open Finsler.Geometry Finsler.SphereGeometry Finsler.GeodesicFrames
open Finsler.PolygonHessian Finsler.PolygonIterate Finsler.PolygonSampling
open Finsler.PolygonIndex Finsler.PolygonLoop Finsler.PolygonIterateReduction
open Finsler.SurfacePhaseGeometry Finsler.SurfaceIteration Finsler.PolygonModel
open Finsler.SurfaceIterationHomology Finsler.SurfaceIterationEquivalence
open Finsler.SamplePhase Finsler.PhaseNullity
open scoped ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

section Polygon
variable {n N : ℕ} [NeZero N] {F : ReversibleMetric n} (P : PolygonSlice F N)

/-- Bounded indices of all actual polygon repetitions force the original
polygon Hessian to have no negative direction. -/
theorem polygon_index_eq_zero_of_bounded (hN : 2 ≤ N) (B : ℕ)
    (hbound : ∀ m : ℕ, ∀ [NeZero m],
      index F (P.iterated m).point (P.iterated m).symmetric ≤ B) :
    index F P.point P.symmetric = 0 := by
  rw [index_eq_sigNeg F P.segments.smooth P.short P.nonzero_edges]
  apply (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero _).mp
  apply SurfaceChainIndex.form_nonneg_of_bounded N (pairForm F P.point) hN B
  intro m hm
  change iterIndex F P.point m ≤ B
  rw [← iterIndex_eq F P.segments.smooth P.short P.nonzero_edges m (P.iterated m).symmetric]
  exact hbound m

/-- The odd monodromy progression can start at the original polygon.
The identity iterate is compared through the actual monodromy operator. -/
theorem exists_original_nullity_progression (htw : PolygonNullity.Twist F P.point) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ j : ℕ,
      nullity F (P.iterated (2 * L * j + 1)).point = nullity F P.point := by
  let T := JacobiChain.mono (PolygonMonodromy.coeff F P.segments.smooth
    P.short P.nonzero_edges htw)
  obtain ⟨L, hL, hper⟩ := PeriodicKernel.exists_period T
  refine ⟨L, hL, fun j => ?_⟩
  change nullity F (PolygonIterate.iterate (2 * L * j + 1) N P.point) = _
  rw [PolygonMonodromy.nullity_iterate (2 * L * j + 1) F P.segments.smooth
    P.short P.nonzero_edges htw,
    PolygonMonodromy.nullity_eq F P.segments.smooth P.short P.nonzero_edges htw]
  change finrank ℝ (PeriodicKernel.fixedPow T (2 * L * j + 1)) =
    finrank ℝ (PeriodicKernel.fixedPow T 1)
  rw [hper (2 * L * j + 1) (by omega), hper 1 le_rfl]
  have he : 2 * L * j + 1 = 1 + (2 * j) * L := by ring
  rw [he, Nat.gcd_add_mul_right_left]

end Polygon

section Geodesic
variable {n : ℕ} {F : ReversibleMetric n} {g : Geodesics.ClosedGeodesic F}
  (D : IterData g)

/-- A zero mean index forces the intrinsic index of every positive
iterate to vanish. The proof uses actual sampled Hessians and does not
assume an index-growth theorem. -/
theorem index_eq_zero_of_zero_mean (hzero : D.Δ = 0) (m : ℕ) (hm : 1 ≤ m) : D.I m = 0 := by
  have : NeZero m := ⟨by omega⟩
  obtain ⟨δ, hδ, hs⟩ := EnergySphereSmooth.exists_ambientMinEnergy_contDiffAt F
  obtain ⟨N₀, hN₀⟩ := D.data δ hδ
  let N := N₀ + 1
  have : NeZero N := ⟨by dsimp [N]; omega⟩
  have hf := hN₀ N (by dsimp [N]; omega) 0
  let q := samplePoly (2 * N) (SmoothSobolev.ofSmooth (Loops.shift g.loop 0))
  have hidx : ∀ k : ℕ, ∀ [NeZero k], iterIndex F q k = D.I k := by
    intro k hk
    let hsym := hessian_isSymmetric F hs (shortPolygon_iterate k (2 * N) hf.1)
      (iterate_ne k (2 * N) hf.2.1)
    rw [← iterIndex_eq F hs hf.1 hf.2.1 k hsym]
    exact (hf.2.2.2.1 k).2 hsym
  rw [← hidx m]
  exact SurfaceChainIndex.idx_eq_zero_of_bounded (2 * N) (pairForm F q)
    (by dsimp [N]; omega) n (fun k _ => by
      change iterIndex F q k ≤ n
      rw [hidx k]
      exact index_le_dimension_of_zero_mean D hzero k (Nat.pos_of_neZero k)) m

/-- A negative direction at any positive iterate forces positive mean
index. This excludes a bounded but positive-index surface branch. -/
theorem mean_pos_of_index_pos {m : ℕ} (hm : 1 ≤ m) (hi : 0 < D.I m) : 0 < D.Δ := by
  apply lt_of_le_of_ne D.mean_nonneg
  intro hz
  rw [index_eq_zero_of_zero_mean D hz.symm m hm] at hi
  exact Nat.lt_irrefl 0 hi

/-- Positive index at one iterate implies that the indices of all
sufficiently large iterates exceed every prescribed bound. -/
theorem index_eventually_gt_of_index_pos {m : ℕ} (hm : 1 ≤ m) (hi : 0 < D.I m)
    (B : ℕ) : ∃ M : ℕ, 1 ≤ M ∧ ∀ k : ℕ, M ≤ k → B < D.I k := by
  have hΔ := mean_pos_of_index_pos D hm hi
  obtain ⟨M, hM⟩ := exists_nat_gt (max 1 (((B : ℝ) + n) / D.Δ))
  have hMpos : 1 ≤ M := by exact_mod_cast ((le_max_left _ _).trans_lt hM).le
  refine ⟨M, hMpos, fun k hk => ?_⟩
  have hkpos : 1 ≤ k := hMpos.trans hk
  have hmul : (B : ℝ) + n < (M : ℝ) * D.Δ :=
    (div_lt_iff₀ hΔ).mp ((le_max_right _ _).trans_lt hM)
  have hmk : (M : ℝ) * D.Δ ≤ (k : ℝ) * D.Δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hΔ.le
  have hlow := (abs_le.mp (D.mean k hkpos)).1
  have : (B : ℝ) < D.I k := by linarith
  exact_mod_cast this

/-- The sampled original geodesic has simultaneous index and nullity
preservation along one odd progression. These are geometric equalities of
actual polygon Hessians, available before taking homology. -/
theorem exists_original_stable_progression (hzero : D.Δ = 0)
    {a : ℝ} (ha : SobolevEnergy.energy F (SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ G : GeodesicPhaseModel F g a, ∃ L : ℕ, 1 ≤ L ∧ ∀ j : ℕ,
      nullity F ((PolygonSlice.ofGeodesic G).iterated (2 * L * j + 1)).point =
        nullity F (PolygonSlice.ofGeodesic G).point ∧
      index F ((PolygonSlice.ofGeodesic G).iterated (2 * L * j + 1)).point
          ((PolygonSlice.ofGeodesic G).iterated (2 * L * j + 1)).symmetric =
        index F (PolygonSlice.ofGeodesic G).point (PolygonSlice.ofGeodesic G).symmetric := by
  obtain ⟨S⟩ := exists_segmentData F
  obtain ⟨N₀, hN₀⟩ := exists_sample_spacing F (δ := S.δ) (a := a) S.pos
  obtain ⟨N₁, hN₁⟩ := exists_sample_facts_all S g
  obtain ⟨N₂, hN₂⟩ := D.data S.δ S.pos
  let N := max (max N₀ N₁) N₂ + 1
  have hN : 0 < N := by dsimp [N]; omega
  have : NeZero N := ⟨by omega⟩
  let M : PolygonModelData F a (2 * N) := PolygonModelData.mk S
    (hN₀ (2 * N) (by dsimp [N]; omega) (by omega))
  let G : GeodesicPhaseModel F g a :=
    ⟨2 * N, M, fun t => hN₁ t (2 * N) (by dsimp [N]; omega), ha⟩
  let P := PolygonSlice.ofGeodesic G
  have hpoint : P.point = samplePoly (2 * N) (SmoothSobolev.ofSmooth (Loops.shift g.loop 0)) :=
    phasePolygon_eq_sample (2 * N) g.loop 0
  have hf := hN₂ N (by dsimp [N]; omega) 0
  have hidx : ∀ m : ℕ, ∀ [NeZero m], index F (P.iterated m).point (P.iterated m).symmetric = 0 := by
    intro m hm
    have h := (hf.2.2.2.1 m).2
    rw [← hpoint] at h
    exact (h (P.iterated m).symmetric).trans
      (index_eq_zero_of_zero_mean D hzero m (Nat.pos_of_neZero m))
  have hbase : index F P.point P.symmetric = 0 :=
    polygon_index_eq_zero_of_bounded P (by change 2 ≤ 2 * N; omega) 0
      (fun m _ => (hidx m).le)
  obtain ⟨L, hL, hnull⟩ := exists_original_nullity_progression P (PolygonSlice.ofGeodesic_twist G)
  exact ⟨G, L, hL, fun j => ⟨hnull j, (hidx (2 * L * j + 1)).trans hbase.symm⟩⟩

/-- The original geodesic is retained: no maximizing base iterate is
chosen. Along an odd bounded-gap monodromy progression, actual iteration
is an isomorphism and rotation by its original period acts trivially.
If the original geodesic is prime, this is the prime-period action. -/
theorem exists_original_iteration_equivalences (hn : 1 ≤ n) (hzero : D.Δ = 0)
    {a : ℝ} (ha : SobolevEnergy.energy F (SmoothSobolev.ofSmooth g.loop) < a ^ 2) :
    ∃ G : GeodesicPhaseModel F g a, ∃ L : ℕ, 1 ≤ L ∧
      ∀ (j : ℕ) (K : Type) [Field K] (q : ℕ),
        Function.Bijective (TopPair.singularHomologyMap
          (polygonIterationPair (PolygonSlice.ofGeodesic G) (2 * L * j + 1))
          (ModuleCat.of K K) q) ∧
        TopPair.singularHomologyMap
          (periodRotationPair (PolygonSlice.ofGeodesic G) (2 * L * j + 1))
          (ModuleCat.of K K) q = 𝟙 _ := by
  obtain ⟨G, L, hL, hstable⟩ := exists_original_stable_progression D hzero ha
  refine ⟨G, L, hL, fun j K _ q => ?_⟩
  exact ⟨polygonIterationPair_homology_bijective (PolygonSlice.ofGeodesic G)
      (2 * L * j + 1) hn (hstable j).1.le (hstable j).2 K q,
    periodRotationPair_homology_eq_id (PolygonSlice.ofGeodesic G)
      (2 * L * j + 1) hn (hstable j).1.le (hstable j).2 K q⟩

end Geodesic
end
end Finsler.SurfaceZeroMeanIndex
