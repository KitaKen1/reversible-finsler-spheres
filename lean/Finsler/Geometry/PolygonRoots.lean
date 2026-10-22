module

public import Finsler.Geometry.PolygonNormal
public import Finsler.Algebra.ChainIndexMul
public import Finsler.Algebra.PeriodicMax

/-! The iteration data of a short polygon. For a short polygon q without zero edges, the index
of the k-fold iterate of the d-fold iterate is the value I(d k) of the index function of q, and
the negative index of the normal block of its Hessian along the iterated vectors is
I(d k) - I(d). Together with the earlier results this gives, below a uniform radius, for every
polygon without zero edges: an index function I with |I(m + k) - I(m) - I(k)| ≤ n and a mean
index Δ ≥ 0 with |I(m) - m Δ| ≤ n; nullities of all iterates at most 2 n; and a period L ≥ 1
such that, whenever gcd(d k, L) = gcd(d, L), the k-fold iterate of the d-fold iterate has the
nullity of the d-fold iterate, the normal form along the iterated vectors, and a nondegenerate
normal block of negative index I(d k) - I(d). This is the elementary iteration lemma with the
normal coordinates of the normal shift lemma; no statement on local cohomology is made. -/

@[expose] public section

namespace Finsler.PolygonRoots

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.PolygonSmooth Finsler.PolygonCritical Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.PolygonChart Finsler.PolygonHessian
open Finsler.PolygonNullity Finsler.PolygonIterate Finsler.PolygonIterateReduction
open Finsler.PolygonIndex Finsler.PolygonNormal Finsler.OperatorIndex
open Set Filter Module QuadraticMap
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n N : ℕ} [NeZero N]

section Regular

variable (F : ReversibleMetric n) {δ : ℝ}
  (hδ : ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
  {q : ZMod N → Sphere n} (hq : ShortPolygon δ q) (hne : ∀ i, q (i + 1) ≠ q i)

include hδ hq hne in
/-- The index of the k-fold iterate of the d-fold iterate is the value of the index function of
the polygon at d k. -/
theorem index_iterate_iterate (d k : ℕ) [NeZero d] [NeZero k]
    (hs : (hessian F (iterate k (d * N) (iterate d N q))).toLinearMap.IsSymmetric) :
    index F (iterate k (d * N) (iterate d N q)) hs = iterIndex F q (d * k) := by
  rw [iterIndex_eq F hδ (shortPolygon_iterate d N hq) (iterate_ne d N hne) k hs, iterIndex,
    pairForm_iterate, ChainIndexMul.idx_mul]
  rfl

include hδ hq hne in
/-- **The normal index.** The negative index of the normal block of the Hessian of the k-fold
iterate of the d-fold iterate is I(d k) - I(d). -/
theorem normal_index (d k : ℕ) [NeZero d] [NeZero k] :
    iterIndex F q d + sigNeg ((quad (hessian F (iterate k (d * N) (iterate d N q)))).restrict
      (iterSpace k (d * N))ᗮ) = iterIndex F q (d * k) := by
  have hqd := shortPolygon_iterate d N hq
  have hned := iterate_ne d N hne
  have hs₀ := hessian_isSymmetric F hδ hqd hned
  have hs := hessian_isSymmetric F hδ (shortPolygon_iterate k (d * N) hqd)
    (iterate_ne k (d * N) hned)
  rw [← index_iterate_iterate F hδ hq hne d k hs, ← iterIndex_eq F hδ hq hne d hs₀]
  exact (index_iterate_eq k (d * N) F hδ hqd hned hs₀ hs).symm

include hδ hq hne in
/-- The index function is monotone along divisibility. -/
theorem iterIndex_le_mul (d k : ℕ) [NeZero d] [NeZero k] :
    iterIndex F q d ≤ iterIndex F q (d * k) := by
  rw [← normal_index F hδ hq hne d k]
  exact Nat.le_add_right _ _

include hδ hq hne in
/-- **A period from the nullities alone.** Under the twist condition, every L ≥ 1 at which the
nullity of the L-fold iterate is maximal among the nullities of the iterates is a period: the
nullity of the k-fold iterate of the d-fold iterate equals the nullity of the d-fold iterate
whenever gcd(d k, L) = gcd(d, L). -/
theorem nullity_eq_of_max (htw : Twist F q) (L : ℕ) [NeZero L]
    (hmax : ∀ (m : ℕ) [NeZero m], nullity F (iterate m N q) ≤ nullity F (iterate L N q))
    (d k : ℕ) [NeZero d] [NeZero k] (hg : Nat.gcd (d * k) L = Nat.gcd d L) :
    nullity F (iterate k (d * N) (iterate d N q)) = nullity F (iterate d N q) := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr (NeZero.ne L)
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  have hmax' : ∀ m : ℕ, 1 ≤ m →
      finrank ℝ (PeriodicKernel.fixedPow
        (JacobiChain.mono (PolygonMonodromy.coeff F hδ hq hne htw)) m) ≤
      finrank ℝ (PeriodicKernel.fixedPow
        (JacobiChain.mono (PolygonMonodromy.coeff F hδ hq hne htw)) L) := by
    intro m hm
    have : NeZero m := ⟨by omega⟩
    rw [← PolygonMonodromy.nullity_iterate m F hδ hq hne htw,
      ← PolygonMonodromy.nullity_iterate L F hδ hq hne htw]
    exact hmax m
  rw [PolygonMonodromy.nullity_iterate_iterate F hδ hq hne htw d k,
    PolygonMonodromy.nullity_iterate d F hδ hq hne htw]
  exact PeriodicMax.finrank_eq_of_max _ hL hmax' (Nat.mul_pos hd hk) hd hg

end Regular

/-- **The iteration data of a short polygon.** There is a positive radius below which every
polygon q without zero edges, with any number of vertices, has an index function I, a mean
index Δ ≥ 0 and a period L ≥ 1 with: |I(m + k) - I(m) - I(k)| ≤ n and |I(m) - m Δ| ≤ n; the
nullity of every iterate is at most 2 n; the index of the k-fold iterate of the d-fold iterate
is I(d k); and whenever gcd(d k, L) = gcd(d, L), the k-fold iterate of the d-fold iterate has
the nullity of the d-fold iterate, the normal form along the iterated vectors, and a
nondegenerate normal block of negative index I(d k) - I(d). -/
theorem exists_iteration_data (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n), ShortPolygon δ q →
      (∀ i, q (i + 1) ≠ q i) →
      ∃ (I : ℕ → ℕ) (Δ : ℝ) (L : ℕ), 0 ≤ Δ ∧ 1 ≤ L ∧
        (∀ m k, 1 ≤ m → 1 ≤ k → I (m + k) ≤ I m + I k + n ∧ I m + I k ≤ I (m + k) + n) ∧
        (∀ m, 1 ≤ m → |(I m : ℝ) - m * Δ| ≤ n) ∧
        (∀ (m : ℕ) [NeZero m], nullity F (iterate m N q) ≤ 2 * n) ∧
        ∀ (d k : ℕ) [NeZero d] [NeZero k],
          (∀ hs : (hessian F (iterate k (d * N) (iterate d N q))).toLinearMap.IsSymmetric,
            index F (iterate k (d * N) (iterate d N q)) hs = I (d * k)) ∧
          (Nat.gcd (d * k) L = Nat.gcd d L →
            nullity F (iterate k (d * N) (iterate d N q)) = nullity F (iterate d N q) ∧
            HasNormalForm k (d * N) F (iterate d N q) ∧
            (∀ ν : Model n (k * (d * N)), ν ∈ (iterSpace k (d * N))ᗮ →
              hessian F (iterate k (d * N) (iterate d N q)) ν = 0 → ν = 0) ∧
            I d + sigNeg ((quad (hessian F (iterate k (d * N) (iterate d N q)))).restrict
              (iterSpace k (d * N))ᗮ) = I (d * k)) := by
  obtain ⟨δ₁, hδ₁, hper⟩ := PolygonMonodromy.exists_nullity_period F
  obtain ⟨δ₂, hδ₂, hs⟩ := exists_ambientMinEnergy_contDiffAt F
  obtain ⟨δ₃, hδ₃, hnul⟩ := PolygonTwist.exists_nullity_le F
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), fun N _ q hq hne => ?_⟩
  have hq₁ : ShortPolygon δ₁ q := fun i => (hq i).trans_le (min_le_left _ _)
  have hq₂ : ShortPolygon δ₂ q := fun i =>
    (hq i).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hq₃ : ShortPolygon δ₃ q := fun i =>
    (hq i).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨L, hL, -, hnull⟩ := hper N q hq₁ hne
  obtain ⟨Δ, hΔ, hmean⟩ := PolygonIndex.exists_mean F q
  refine ⟨iterIndex F q, Δ, L, hΔ, hL,
    fun m k hm hk => ⟨iterIndex_add_le F q hm hk, le_iterIndex_add F q hm hk⟩, hmean,
    fun m _ => hnul (m * N) (iterate m N q) (shortPolygon_iterate m N hq₃) (iterate_ne m N hne),
    fun d k _ _ => ⟨fun hsym => index_iterate_iterate F hs hq₂ hne d k hsym, fun hg => ?_⟩⟩
  have hqd := shortPolygon_iterate d N hq₂
  have hned := iterate_ne d N hne
  exact ⟨hnull d k hg, hasNormalForm k (d * N) F hs hqd hned (hnull d k hg).le,
    fun ν hν h => normal_nondegenerate k (d * N) F hs hqd hned (hnull d k hg).le hν h,
    normal_index F hs hq₂ hne d k⟩

/-- **Every maximizer of the nullities is a period, uniformly.** There is a positive radius below
which, for every polygon without zero edges with any number of vertices and every L ≥ 1 at which
the nullity of the iterates is maximal, the k-fold iterate of the d-fold iterate has the nullity
of the d-fold iterate, the normal form along the iterated vectors and a nondegenerate normal
block, whenever gcd(d k, L) = gcd(d, L). -/
theorem exists_normal_forms_of_max (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q : ZMod N → Sphere n), ShortPolygon δ q →
      (∀ i, q (i + 1) ≠ q i) → ∀ (L : ℕ) [NeZero L],
      (∀ (m : ℕ) [NeZero m], nullity F (iterate m N q) ≤ nullity F (iterate L N q)) →
      ∀ (d k : ℕ) [NeZero d] [NeZero k], Nat.gcd (d * k) L = Nat.gcd d L →
        nullity F (iterate k (d * N) (iterate d N q)) = nullity F (iterate d N q) ∧
        HasNormalForm k (d * N) F (iterate d N q) ∧
        (∀ ν : Model n (k * (d * N)), ν ∈ (iterSpace k (d * N))ᗮ →
          hessian F (iterate k (d * N) (iterate d N q)) ν = 0 → ν = 0) ∧
        iterIndex F q d + sigNeg ((quad (hessian F (iterate k (d * N) (iterate d N q)))).restrict
          (iterSpace k (d * N))ᗮ) = iterIndex F q (d * k) := by
  obtain ⟨δ₁, hδ₁, htw⟩ := PolygonTwist.exists_twist F
  obtain ⟨δ₂, hδ₂, hs⟩ := exists_ambientMinEnergy_contDiffAt F
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun N _ q hq hne L _ hmax d k _ _ hg => ?_⟩
  have hq₁ : ShortPolygon δ₁ q := fun i => (hq i).trans_le (min_le_left _ _)
  have hq₂ : ShortPolygon δ₂ q := fun i => (hq i).trans_le (min_le_right _ _)
  have hnull := nullity_eq_of_max F hs hq₂ hne (htw N q hq₁ hne) L hmax d k hg
  have hqd := shortPolygon_iterate d N hq₂
  have hned := iterate_ne d N hne
  exact ⟨hnull, hasNormalForm k (d * N) F hs hqd hned hnull.le,
    fun ν hν h => normal_nondegenerate k (d * N) F hs hqd hned hnull.le hν h,
    normal_index F hs hq₂ hne d k⟩

end

end Finsler.PolygonRoots
