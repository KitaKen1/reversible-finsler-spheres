module

public import Finsler.Geometry.RoundV2Chart
public import Finsler.Topology.TrivHq

/-! The cohomology of V₂.

Let F₊ be the fibre of V₂ over e₀ and A = V₂ ∖ F₊. By excision of the fibre over −e₀ and the chart
of V₂ over the sphere minus −e₀, the pair (V₂, A) is (S(K) × ℝⁿ, S(K) × (ℝⁿ ∖ 0)), whose cohomology
is that of the fibre sphere S(K) shifted by n (`PairSuspensionProduct`). The flip x ↦ −x takes A
to the domain of the chart, so A is S(K) × ℝⁿ, which has the cohomology of S(K). The long exact
sequence of the triple (V₂, A, ∅) bounds the cohomology of V₂: for n ≥ 2 it has dimension at most
one in every degree, it vanishes outside the degrees 0, n − 1, n and 2n − 1, and it is nonzero in
degree 0. -/

@[expose] public section

namespace Finsler.RoundV2Dims

open CategoryTheory Finsler.SphereGeometry Finsler.RoundChart Finsler.RoundThom
open Finsler.RoundV2Chart Finsler.RoundV2Finite Finsler.TrivHq Finsler.PairSuspensionProduct
open Finsler.BorelCochain Finsler.BorelPair Finsler.PairTriple Finsler.BorelLoop
open Finsler.TameHomology Finsler.BorelDeformation Finsler.BorelCrossing
open Set Topology Module Metric
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-! ### The fibre sphere -/

theorem finrank_Kq (hn : 2 ≤ n) : finrank ℝ (Kq n) = (n - 1) + 1 := by
  rw [Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := n) e₀_ne_zero]
  omega

theorem Zs_Hq_finite (hn : 2 ≤ n) (k : ℕ) : Module.Finite (ZMod 2) (Hq (Zs n) k) := by
  by_cases h0 : k = 0
  · subst h0
    exact (sphere_Hq_zero_deg (finrank_Kq hn) (by omega)).1
  by_cases h1 : k = n - 1
  · subst h1
    exact (sphere_Hq_top (finrank_Kq hn) (by omega)).1
  exact finite_of_isZero (sphere_Hq_zero (finrank_Kq hn) (by omega) h0 h1)

theorem Zs_finrank (hn : 2 ≤ n) (k : ℕ) :
    finrank (ZMod 2) (Hq (Zs n) k) = if k = 0 ∨ k = n - 1 then 1 else 0 := by
  by_cases h0 : k = 0
  · subst h0
    rw [if_pos (Or.inl rfl)]
    exact (sphere_Hq_zero_deg (finrank_Kq hn) (by omega)).2
  by_cases h1 : k = n - 1
  · subst h1
    rw [if_pos (Or.inr rfl)]
    exact (sphere_Hq_top (finrank_Kq hn) (by omega)).2
  rw [if_neg (by tauto)]
  have := ModuleCat.subsingleton_of_isZero (sphere_Hq_zero (finrank_Kq hn) (by omega) h0 h1)
  exact Module.finrank_zero_of_subsingleton

theorem Zs_H_finite (hn : 2 ≤ n) (k : ℕ) :
    Module.Finite (ZMod 2) (H (triv (emptyPair (Zs n))) k) :=
  (finite_finrank (Zs n) k (Zs_Hq_finite hn k)).1

theorem Zs_H_finrank (hn : 2 ≤ n) (k : ℕ) :
    finrank (ZMod 2) (H (triv (emptyPair (Zs n))) k) = if k = 0 ∨ k = n - 1 then 1 else 0 :=
  (finite_finrank (Zs n) k (Zs_Hq_finite hn k)).2.trans (Zs_finrank hn k)

/-! ### The pair (V₂, A) -/

theorem cover : (univ : Set (V2T n)) ⊆ AP ∪ NP := by
  intro p _
  by_cases h : p.1.1 = e₀
  · right
    change p.1.1 ≠ -e₀
    rw [h]
    intro h'
    have h2 : (2 : ℝ) • (e₀ : Ambient n) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h']
      exact add_neg_cancel _
    exact e₀_ne_zero ((smul_eq_zero.mp h2).resolve_left two_ne_zero)
  · left
    exact h

/-- Excision of the fibre over −e₀. -/
theorem exc_bijective (q : ℕ) :
    Function.Bijective (Hmap (trivHom (inclPair (inter_subset_left : NP ∩ AP ⊆ NP)
      (subset_univ (AP (n := n))) inter_subset_right (subset_univ _))) q) :=
  bijective_Hmap_excision (inter_subset_left : NP ∩ AP ⊆ NP) (subset_univ (AP (n := n)))
    inter_subset_right (subset_univ _) (fun _ h1 h2 => ⟨h1, h2⟩) AP NP AP_isOpen NP_isOpen cover
    (fun _ h => h.1) (fun _ h => h.1) q

/-- The chart as a map of pairs. -/
def chartP : C(NP (n := n), prodCyl (univ : Set (Zs n)) n) :=
  ⟨fun x => ⟨chartHomeo x, trivial⟩, chartHomeo.continuous.subtype_mk _⟩

def chartPInv : C(prodCyl (univ : Set (Zs n)) n, NP (n := n)) :=
  ⟨fun y => chartHomeo.symm (y : Prd (Zs n) n), chartHomeo.symm.continuous.comp continuous_subtype_val⟩

theorem chartP_mem (x : NP (n := n)) (hx : (x : V2T n) ∈ NP ∩ AP) :
    ((chartP x : prodCyl (univ : Set (Zs n)) n) : Prd (Zs n) n) ∈
      prodCyl (univ : Set (Zs n)) n ∩ prodOpen (∅ : Set (Zs n)) n := by
  refine ⟨trivial, Or.inl ?_⟩
  intro h
  exact hx.2 ((chartFun_snd_eq_zero_iff x).mp h)

theorem chartPInv_mem (y : prodCyl (univ : Set (Zs n)) n)
    (hy : (y : Prd (Zs n) n) ∈ prodCyl (univ : Set (Zs n)) n ∩ prodOpen (∅ : Set (Zs n)) n) :
    ((chartPInv y : NP (n := n)) : V2T n) ∈ NP ∩ AP := by
  refine ⟨(chartPInv y).2, fun h => ?_⟩
  have h1 : (chartFun (chartPInv y)).2 = 0 := (chartFun_snd_eq_zero_iff _).mpr h
  have h2 : chartFun (chartPInv y) = (y : Prd (Zs n) n) := chartHomeo.apply_symm_apply _
  rw [h2] at h1
  rcases hy.2 with h3 | h3
  · exact h3 h1
  · exact h3

/-- The chart is bijective on the cohomology of the pairs. -/
theorem chart_bijective (q : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX (inter_subset_left : NP ∩ AP ⊆ NP)
      (inter_subset_left : prodCyl (univ : Set (Zs n)) n ∩ prodOpen (∅ : Set (Zs n)) n ⊆
        prodCyl univ n) chartP chartP_mem)) q) := by
  let F : (chartPInv.comp chartP).Homotopy (ContinuousMap.id (NP (n := n))) :=
    { toFun := fun q => q.2
      continuous_toFun := continuous_snd
      map_zero_left := fun x => (chartHomeo.symm_apply_apply x).symm
      map_one_left := fun _ => rfl }
  have hpi : chartP.comp chartPInv = ContinuousMap.id (prodCyl (univ : Set (Zs n)) n) :=
    ContinuousMap.ext fun y => Subtype.ext (chartHomeo.apply_symm_apply (y : Prd (Zs n) n))
  exact bijective_Hmap_of_section _ _ chartP chartPInv chartP_mem chartPInv_mem hpi F
    (fun _ _ hx => hx) q

/-- **The pair (V₂, A) has the cohomology of the fibre sphere shifted by n.** -/
def pairEquiv (k : ℕ) :
    H (triv (emptyPair (Zs n))) k ≃ₗ[ZMod 2] H (triv (pairOf (subset_univ (AP (n := n))))) (k + n) :=
  ((prodEquiv (univ : Set (Zs n)) isOpen_empty n k).trans
    (LinearEquiv.ofBijective _ (chart_bijective (k + n)))).trans
      (LinearEquiv.ofBijective _ (exc_bijective (k + n))).symm

theorem pair_eq_zero (q : ℕ) (hq : q < n) (x : H (triv (pairOf (subset_univ (AP (n := n))))) q) :
    x = 0 := by
  have h1 := (exc_bijective (n := n) q).1
  have h2 := (chart_bijective (n := n) q).2
  obtain ⟨y, hy⟩ := h2 (Hmap (trivHom (inclPair (inter_subset_left : NP ∩ AP ⊆ NP)
    (subset_univ (AP (n := n))) inter_subset_right (subset_univ _))) q x)
  have hy0 : y = 0 := prod_eq_zero (univ : Set (Zs n)) isOpen_empty n q hq y
  rw [hy0, map_zero] at hy
  exact h1 (hy.symm.trans (map_zero _).symm)

/-! ### The complement A of the fibre over e₀ -/

/-- The flip of the first vector. -/
def flipAN (x : AP (n := n)) : NP (n := n) :=
  ⟨⟨(-x.1.1.1, x.1.1.2), by rw [norm_neg]; exact x.1.2.1, x.1.2.2.1, by
      rw [inner_neg_left, x.1.2.2.2, neg_zero]⟩, fun h => x.2 (neg_inj.mp h)⟩

def flipNA (y : NP (n := n)) : AP (n := n) :=
  ⟨⟨(-y.1.1.1, y.1.1.2), by rw [norm_neg]; exact y.1.2.1, y.1.2.2.1, by
      rw [inner_neg_left, y.1.2.2.2, neg_zero]⟩, fun h => y.2 (by rw [← h, neg_neg])⟩

theorem flipNA_flipAN (x : AP (n := n)) : flipNA (flipAN x) = x :=
  Subtype.ext (Subtype.ext (Prod.ext (neg_neg _) rfl))

theorem flipAN_continuous : Continuous (flipAN (n := n)) := by
  refine (Continuous.subtype_mk ?_ _).subtype_mk _
  exact ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).neg).prodMk
    (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))

theorem flipNA_continuous : Continuous (flipNA (n := n)) := by
  refine (Continuous.subtype_mk ?_ _).subtype_mk _
  exact ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).neg).prodMk
    (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))

/-- The projection of A to the fibre sphere. -/
def projA : C(AP (n := n), (univ : Set (Zs n))) :=
  ⟨fun x => ⟨(chartHomeo (flipAN x)).1, trivial⟩,
    ((continuous_fst.comp (chartHomeo.continuous.comp flipAN_continuous)).subtype_mk _)⟩

/-- The section of the projection. -/
def secA : C((univ : Set (Zs n)), AP (n := n)) :=
  ⟨fun z => flipNA (chartHomeo.symm ((z : Zs n), 0)),
    flipNA_continuous.comp (chartHomeo.symm.continuous.comp
      ((continuous_subtype_val).prodMk continuous_const))⟩

theorem A_bijective (q : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX (fun _ h => h.2.elim :
      (univ : Set (V2T n)) ∩ ∅ ⊆ AP) (inter_subset_left : (univ : Set (Zs n)) ∩ ∅ ⊆ univ) projA
        (fun _ h => h.2.elim))) q) := by
  have hpi : projA.comp secA = ContinuousMap.id (univ : Set (Zs n)) := by
    refine ContinuousMap.ext fun z => Subtype.ext ?_
    change (chartHomeo (flipAN (flipNA (chartHomeo.symm ((z : Zs n), 0))))).1 = (z : Zs n)
    have h1 : flipAN (flipNA (chartHomeo.symm ((z : Zs n), (0 : Fin n → ℝ)))) =
        chartHomeo.symm ((z : Zs n), 0) := Subtype.ext (Subtype.ext (Prod.ext (neg_neg _) rfl))
    rw [h1, chartHomeo.apply_symm_apply]
  let F : (secA.comp projA).Homotopy (ContinuousMap.id (AP (n := n))) :=
    { toFun := fun p => flipNA (chartHomeo.symm ((chartHomeo (flipAN p.2)).1,
        (p.1 : ℝ) • (chartHomeo (flipAN p.2)).2))
      continuous_toFun := by
        have h1 : Continuous fun p : unitInterval × AP (n := n) => chartHomeo (flipAN p.2) :=
          chartHomeo.continuous.comp (flipAN_continuous.comp continuous_snd)
        exact flipNA_continuous.comp (chartHomeo.symm.continuous.comp
          ((continuous_fst.comp h1).prodMk
            ((continuous_subtype_val.comp continuous_fst).smul (continuous_snd.comp h1))))
      map_zero_left := fun x => by
        change flipNA (chartHomeo.symm ((chartHomeo (flipAN x)).1,
          ((0 : unitInterval) : ℝ) • (chartHomeo (flipAN x)).2)) =
            flipNA (chartHomeo.symm ((chartHomeo (flipAN x)).1, 0))
        rw [Set.Icc.coe_zero, zero_smul]
      map_one_left := fun x => by
        change flipNA (chartHomeo.symm ((chartHomeo (flipAN x)).1,
          ((1 : unitInterval) : ℝ) • (chartHomeo (flipAN x)).2)) = x
        rw [Set.Icc.coe_one, one_smul, Prod.mk.eta, chartHomeo.symm_apply_apply, flipNA_flipAN] }
  exact bijective_Hmap_of_section _ _ projA secA (fun _ h => h.2.elim) (fun _ h => h.2.elim)
    hpi F (fun _ _ h => h.2.elim) q

/-! ### The long exact sequence -/

theorem finrank_mid_le {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''}
    (h : BorelExact.ShortExact ι π) (k : ℕ) [Module.Finite (ZMod 2) (H K k)]
    [Module.Finite (ZMod 2) (H K' k)] [Module.Finite (ZMod 2) (H K'' k)] :
    finrank (ZMod 2) (H K k) ≤ finrank (ZMod 2) (H K' k) + finrank (ZMod 2) (H K'' k) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Hmap π k)
  have h2 : LinearMap.ker (Hmap π k) ≤ LinearMap.range (Hmap ι k) := fun x hx => by
    obtain ⟨z, hz⟩ := BorelExact.exact_mid_ordinary h k x (LinearMap.mem_ker.mp hx)
    exact ⟨z, hz⟩
  have h3 := Submodule.finrank_mono h2
  have h4 := LinearMap.finrank_range_le (Hmap ι k)
  have h5 := Submodule.finrank_le (LinearMap.range (Hmap π k))
  calc finrank (ZMod 2) (H K k) = finrank (ZMod 2) (LinearMap.range (Hmap π k)) +
        finrank (ZMod 2) (LinearMap.ker (Hmap π k)) := h1.symm
    _ ≤ finrank (ZMod 2) (H K'' k) + finrank (ZMod 2) (H K' k) := add_le_add h5 (h3.trans h4)
    _ = _ := add_comm _ _

/-- The cohomology of V₂. -/
abbrev HV (n k : ℕ) := H (triv (emptyPair (V2T n))) k

theorem hst : (univ : Set (V2T n)) ∩ ∅ ⊆ AP := fun _ h => h.2.elim

theorem A_finite (hn : 2 ≤ n) (k : ℕ) :
    Module.Finite (ZMod 2) (H (triv (pairOf (hst (n := n)))) k) := by
  haveI := Zs_H_finite hn k
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ (A_bijective k))

theorem A_finrank (hn : 2 ≤ n) (k : ℕ) :
    finrank (ZMod 2) (H (triv (pairOf (hst (n := n)))) k) = if k = 0 ∨ k = n - 1 then 1 else 0 :=
  ((LinearEquiv.ofBijective _ (A_bijective k)).finrank_eq.symm).trans (Zs_H_finrank hn k)

theorem P_finite (hn : 2 ≤ n) (k : ℕ) :
    Module.Finite (ZMod 2) (H (triv (pairOf (subset_univ (AP (n := n))))) k) := by
  by_cases hk : n ≤ k
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    haveI := Zs_H_finite hn j
    exact Module.Finite.equiv (pairEquiv j)
  · have : Subsingleton (H (triv (pairOf (subset_univ (AP (n := n))))) k) :=
      ⟨fun x y => (pair_eq_zero k (by omega) x).trans (pair_eq_zero k (by omega) y).symm⟩
    exact inferInstance

theorem P_finrank (hn : 2 ≤ n) (k : ℕ) :
    finrank (ZMod 2) (H (triv (pairOf (subset_univ (AP (n := n))))) k) =
      if n ≤ k ∧ (k - n = 0 ∨ k - n = n - 1) then 1 else 0 := by
  by_cases hk : n ≤ k
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hk
    rw [← (pairEquiv j).finrank_eq, Zs_H_finrank hn j, Nat.add_sub_cancel]
    by_cases h : j = 0 ∨ j = n - 1
    · rw [if_pos h, if_pos ⟨hk, h⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.2)]
  · rw [if_neg (fun h => hk h.1)]
    have : Subsingleton (H (triv (pairOf (subset_univ (AP (n := n))))) k) :=
      ⟨fun x y => (pair_eq_zero k (by omega) x).trans (pair_eq_zero k (by omega) y).symm⟩
    exact Module.finrank_zero_of_subsingleton

/-- **The dimensions of the cohomology of V₂** are bounded by the sum of those of the pair
(V₂, A) and of A. -/
theorem V2_finrank_le (hn : 2 ≤ n) (k : ℕ) :
    finrank (ZMod 2) (HV n k) ≤ (if n ≤ k ∧ (k - n = 0 ∨ k - n = n - 1) then 1 else 0) +
      (if k = 0 ∨ k = n - 1 then 1 else 0) := by
  have hse := tripleExact (hst (n := n)) (subset_univ (AP (n := n)))
  haveI := V2_finite (n := n) k
  haveI := P_finite hn k
  haveI := A_finite hn k
  have h := finrank_mid_le hse k
  rw [P_finrank hn k, A_finrank hn k] at h
  exact h

theorem V2_finrank_le_one (hn : 2 ≤ n) (k : ℕ) : finrank (ZMod 2) (HV n k) ≤ 1 := by
  have h := V2_finrank_le hn k
  split_ifs at h with h1 h2
  · exfalso
    omega
  · exact h
  · exact h
  · omega

theorem V2_eq_zero (hn : 2 ≤ n) (k : ℕ) (h0 : k ≠ 0) (h1 : k ≠ n - 1) (h2 : k ≠ n)
    (h3 : k ≠ n + (n - 1)) (x : HV n k) : x = 0 := by
  have h := V2_finrank_le hn k
  rw [if_neg (by omega), if_neg (by omega)] at h
  haveI := V2_finite (n := n) k
  have : finrank (ZMod 2) (HV n k) = 0 := by omega
  have hs := Module.finrank_zero_iff.mp this
  exact Subsingleton.elim _ _

/-- **V₂ has cohomology in degree zero.** -/
theorem V2_H0_pos (hn : 2 ≤ n) : 0 < finrank (ZMod 2) (HV n 0) := by
  have hse := tripleExact (hst (n := n)) (subset_univ (AP (n := n)))
  haveI := V2_finite (n := n) 0
  haveI := A_finite hn 0
  have hsurj : Function.Surjective (Hmap (trivHom (incPair (hst (n := n))
      (subset_univ (AP (n := n))))) 0) := fun y => OrdinaryDelta.exact_delta hse 0 y
    (pair_eq_zero 1 (by omega) _)
  have h1 := LinearMap.finrank_range_le (Hmap (trivHom (incPair (hst (n := n))
    (subset_univ (AP (n := n))))) 0)
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, A_finrank hn 0, if_pos (Or.inl rfl)] at h1
  exact h1

end

end Finsler.RoundV2Dims
