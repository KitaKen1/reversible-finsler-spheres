module

public import Finsler.Geometry.RoundFiltration
public import Finsler.Topology.TrivHq
public import Finsler.Topology.LevelBounds

/-! The tails of the round filtration (G3).

For the cut c_m = 2π(m + 1/2), the ordinary cohomology of the tail pair (Λ, t_{c_m}) vanishes below
the index l_m = (2m + 1)(n − 1) of the next crossing. Finite stages first: the pair
(t_{c_{m+k}}, t_{c_m}) is built from the crossings m, …, m + k − 1, whose cohomology vanishes below
their indices l_{m+i} ≥ l_m (triple sequences). By the universal coefficient isomorphism the
relative homology of the finite stages vanishes below l_m. Singular homology has compact
supports (Tau Ceti): a class of Λ comes from some t_{c_k}, and a class of t_{c_m} which dies in Λ
dies in some t_{c_k}. With the finite stages this makes H_q(t_{c_m}) → H_q(Λ) surjective and
H_{q−1}(t_{c_m}) → H_{q−1}(Λ) injective for q < l_m, so the relative homology of the tail vanishes
below l_m, and so does its cohomology. -/

@[expose] public section

namespace Finsler.RoundTails

open CategoryTheory Limits AlgebraicTopology Finsler.SphereGeometry Finsler.Geometry
open Finsler.RoundCrossPattern Finsler.RoundFiltration Finsler.TrivHq Finsler.TameHomology
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.PairTriple Finsler.BorelComparison Finsler.RelativeCohomology
open Set Module Topology

noncomputable section

variable {n : ℕ}

theorem cut_le_cut {m m' : ℕ} (h : m ≤ m') : cut m ≤ cut m' := by
  unfold cut
  have : (m : ℝ) ≤ m' := by exact_mod_cast h
  have := Real.pi_pos
  nlinarith

theorem cut_pos (m : ℕ) : 0 < cut m := by
  unfold cut
  have := Real.pi_pos
  positivity

theorem exists_cut_gt (x : ℝ) : ∃ k : ℕ, x < cut k := by
  have hπ := Real.pi_pos
  obtain ⟨k, hk⟩ := exists_nat_gt (x / (2 * Real.pi))
  refine ⟨k, ?_⟩
  have h1 : x < 2 * Real.pi * k := by
    rw [div_lt_iff₀ (by positivity)] at hk
    linarith
  unfold cut
  nlinarith

theorem lc_mono (n : ℕ) {m m' : ℕ} (h : m ≤ m') : lc n m ≤ lc n m' := by
  unfold lc
  exact Nat.mul_le_mul_right _ (by omega)

/-! ### Finite stages -/

theorem cross_zero (hn : 3 ≤ n) (j q : ℕ) (hq : q < lc n (j + 1))
    (z : H (triv (pairOf (lev_mono (roundMetric n) (cut_mono j)))) q) : z = 0 := by
  let e := Finsler.LevelBounds.ofPairEquiv (crossPair (roundMetric n) (cut_mono j))
    (Category.comp_id _) (revCross_sq (roundMetric n) (cut_mono j)) q
  apply e.injective
  rw [map_zero]
  exact cross_below (by omega) (Nat.succ_pos j) (cut_lo j) (cut_ac j) (cut_cb j) (cut_hi j)
    (cut_mono j) q hq _

/-- The cohomology of the finite stages vanishes below the index of the first crossing. -/
theorem stage_zero (hn : 3 ≤ n) (m : ℕ) : ∀ k q, q < lc n (m + 1) →
    ∀ z : H (triv (pairOf (lev_mono (roundMetric n) (cut_le_cut (Nat.le_add_right m k))))) q,
      z = 0 := by
  intro k
  induction k with
  | zero =>
    intro q _ z
    exact H_self_eq_zero (lev (roundMetric n) (cut m)) q z
  | succ k ih =>
    intro q hq x
    have hst : lev (roundMetric n) (cut m) ⊆ lev (roundMetric n) (cut (m + k)) :=
      lev_mono (roundMetric n) (cut_le_cut (Nat.le_add_right m k))
    have htu : lev (roundMetric n) (cut (m + k)) ⊆ lev (roundMetric n) (cut (m + k + 1)) :=
      lev_mono (roundMetric n) (cut_mono (m + k))
    have hse := tripleExact hst htu
    obtain ⟨z, hz⟩ := BorelExact.exact_mid_ordinary hse q x (ih q hq _)
    rw [← hz, cross_zero hn (m + k) q (lt_of_lt_of_le hq (lc_mono n (by omega))) z, map_zero]

/-! ### Homology and cohomology -/

/-- The cohomology of a pair is the dual of its relative homology. -/
def dualPair (P : TopPair.{0}) (q : ℕ) :
    H (triv P) q ≃ₗ[ZMod 2] Module.Dual (ZMod 2) (Hrel P q) :=
  (ordinaryEquiv P (𝟙 _) (Category.comp_id _) q).trans (RelativeKronecker.equiv P q)

theorem Hrel_zero_of_H_zero {P : TopPair.{0}} {q : ℕ} (h : ∀ z : H (triv P) q, z = 0)
    (v : Hrel P q) : v = 0 := by
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod 2)]
  intro φ
  have : φ = 0 := by
    have h1 := h ((dualPair P q).symm φ)
    have h2 := congrArg (dualPair P q) h1
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact h2
  rw [this, LinearMap.zero_apply]

theorem stage_Hrel_zero (hn : 3 ≤ n) (m k q : ℕ) (hq : q < lc n (m + 1))
    (v : Hrel (pairOf (lev_mono (roundMetric n) (cut_le_cut (Nat.le_add_right m k)))) q) :
    v = 0 :=
  Hrel_zero_of_H_zero (stage_zero hn m k q hq) v

/-! ### The tails, given compact supports -/

/-- The inclusion of a cut into the whole loop space. -/
def inclU (a : ℝ) : TopCat.of ↥(lev (roundMetric n) a) ⟶ TopCat.of ↥(univ : Set (Loops n)) :=
  TopCat.ofHom (ContinuousMap.inclusion (subset_univ _))

/-- The inclusion of cuts. -/
def inclC {a b : ℝ} (h : a ≤ b) :
    TopCat.of ↥(lev (roundMetric n) a) ⟶ TopCat.of ↥(lev (roundMetric n) b) :=
  TopCat.ofHom (ContinuousMap.inclusion (lev_mono (roundMetric n) h))

theorem inclC_inclU {a b : ℝ} (h : a ≤ b) : inclC (n := n) h ≫ inclU b = inclU a := rfl

/-- **Compact supports** of the homology of the loop space along the cuts c_k: every class comes
from some cut, and a class of a cut which dies in the loop space dies in a larger cut. (Singular
simplices have compact images, which have bounded energy; this is Tau Ceti's
`DirectedUnion` statement, not built in the pinned dependency checkout.) -/
structure Supports (n : ℕ) : Prop where
  rep : ∀ q (y : Hq (TopCat.of ↥(univ : Set (Loops n))) q),
    ∃ k, ∃ x : Hq (TopCat.of ↥(lev (roundMetric n) (cut k))) q, (HqMap (inclU (cut k)) q).hom x = y
  die : ∀ q i (x : Hq (TopCat.of ↥(lev (roundMetric n) (cut i))) q),
    (HqMap (inclU (cut i)) q).hom x = 0 →
      ∃ k, ∃ hik : i ≤ k, (HqMap (inclC (cut_le_cut hik)) q).hom x = 0

theorem HqMap_comp_apply {X Y Z : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ) (x : Hq X q) :
    (HqMap (f ≫ g) q).hom x = (HqMap g q).hom ((HqMap f q).hom x) := by
  rw [HqMap_comp]
  rfl

theorem comp_zero_apply {X Y Z : ModuleCat.{0} (ZMod 2)} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : f ≫ g = 0) (x : X) : g.hom (f.hom x) = 0 := by
  have := congrArg (fun φ : X ⟶ Z => φ.hom x) h
  simpa using this

theorem exact_mem {S : ShortComplex (ModuleCat.{0} (ZMod 2))} (hS : S.Exact) {y : S.X₂}
    (hy : S.g.hom y = 0) : ∃ x, S.f.hom x = y :=
  (ShortComplex.moduleCat_exact_iff_ker_sub_range S).mp hS hy

section Tail

variable (hn : 3 ≤ n) (hS : Supports n) (m : ℕ)
include hn

/-- At finite stages the inclusion is surjective on homology below the index. -/
theorem stage_surj (k q : ℕ) (hq : q < lc n (m + 1)) :
    Function.Surjective (HqMap (inclC (n := n) (cut_le_cut (Nat.le_add_right m k))) q).hom := by
  intro y
  exact exact_mem ((pairOf (lev_mono (roundMetric n)
    (cut_le_cut (Nat.le_add_right m k)))).singularHomology_exact_space coeff q)
    (stage_Hrel_zero hn m k q hq _)

/-- At finite stages the inclusion is injective on homology below the index minus one. -/
theorem stage_inj (k q : ℕ) (hq : q + 1 < lc n (m + 1)) :
    Function.Injective (HqMap (inclC (n := n) (cut_le_cut (Nat.le_add_right m k))) q).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, hz⟩ := exact_mem ((pairOf (lev_mono (roundMetric n)
    (cut_le_cut (Nat.le_add_right m k)))).singularHomology_exact_subspace coeff (q + 1) q rfl) hx
  rw [← hz, stage_Hrel_zero hn m k (q + 1) hq z]
  exact map_zero _

include hS

theorem tail_surj (q : ℕ) (hq : q < lc n (m + 1)) :
    Function.Surjective (HqMap (inclU (n := n) (cut m)) q).hom := by
  intro y
  obtain ⟨k, x, hx⟩ := hS.rep q y
  by_cases hk : m ≤ k
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    obtain ⟨x', hx'⟩ := stage_surj hn m j q hq x
    refine ⟨x', ?_⟩
    rw [← hx, ← hx', ← HqMap_comp_apply, inclC_inclU]
  · refine ⟨(HqMap (inclC (n := n) (cut_le_cut (by omega : k ≤ m))) q).hom x, ?_⟩
    rw [← HqMap_comp_apply, inclC_inclU, hx]

theorem tail_inj (q : ℕ) (hq : q + 1 < lc n (m + 1)) :
    Function.Injective (HqMap (inclU (n := n) (cut m)) q).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨k, hmk, hk⟩ := hS.die q m x hx
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
  exact stage_inj hn m j q hq (hk.trans (map_zero _).symm)

/-- **The relative homology of the tail vanishes below the index.** -/
theorem tail_Hrel_zero (q : ℕ) (hq : q < lc n (m + 1))
    (v : Hrel (tailPair (roundMetric n) (cut m)) q) : v = 0 := by
  cases q with
  | zero =>
    have hepi : Function.Surjective
        ((tailPair (roundMetric n) (cut m)).singularHomologyπ coeff 0).hom :=
      (ModuleCat.epi_iff_surjective _).mp inferInstance
    obtain ⟨y, rfl⟩ := hepi v
    obtain ⟨x, rfl⟩ := tail_surj hn hS m 0 hq y
    exact comp_zero_apply _ _
      ((tailPair (roundMetric n) (cut m)).homologyMap_comp_singularHomologyπ coeff 0) x
  | succ q =>
    have h0 := comp_zero_apply _ _
      ((tailPair (roundMetric n) (cut m)).singularHomologyδ_comp coeff (q + 1) q rfl) v
    have h1 : ((tailPair (roundMetric n) (cut m)).singularHomologyδ coeff (q + 1) q rfl).hom v =
        0 :=
      (injective_iff_map_eq_zero (HqMap (inclU (n := n) (cut m)) q).hom).mp
        (tail_inj hn hS m q (by omega)) _ h0
    obtain ⟨y, hy⟩ := exact_mem ((tailPair (roundMetric n) (cut m)).singularHomology_exact_relative
      coeff (q + 1) q rfl) h1
    obtain ⟨x, rfl⟩ := tail_surj hn hS m (q + 1) hq y
    rw [← hy]
    exact comp_zero_apply _ _
      ((tailPair (roundMetric n) (cut m)).homologyMap_comp_singularHomologyπ coeff (q + 1)) x

/-- **The ordinary cohomology of the tail vanishes below the index** (given compact supports). -/
theorem tail_zero (q : ℕ) (hq : q < lc n (m + 1))
    (z : H (tailComplex (roundMetric n) (cut m)) q) : z = 0 := by
  let e := (Finsler.LevelBounds.ofPairEquiv (tailPair (roundMetric n) (cut m))
    (revTail_sq (roundMetric n) (cut m)) (Category.comp_id _) q).trans
      (dualPair (tailPair (roundMetric n) (cut m)) q)
  apply e.injective
  rw [map_zero]
  ext v
  rw [tail_Hrel_zero hn hS m q hq v, map_zero, LinearMap.zero_apply]

end Tail

end

end Finsler.RoundTails
