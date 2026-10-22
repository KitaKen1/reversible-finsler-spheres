module

public import Finsler.Topology.OrdinaryDelta
public import Finsler.Topology.OrdinaryRestriction
public import Finsler.Topology.FiniteCut

/-! Ordinary ranks of a cut from filling (source (9.9)). With finitely many prime closed geodesic
images, let the ordinary crossing groups of single crossings above a regular cut a have dimension
at most C in degree j + 1. Then for every regular cut b ≥ a the dimension of the ordinary
cohomology of (t_a, M) in degree j is at most the dimension of the image of the restriction
from t_b plus C times the number of critical levels between a and b (induction over the
critical levels, with the connecting map of ordinary cohomology). If moreover the image of the
restriction from t_b lies in the image of the restriction from the loop space, which has
dimension at most G, the dimension is at most G + C K, where K bounds the number of critical
levels between a and b. The local rank bound and the filling statement are hypotheses. -/

@[expose] public section

namespace Finsler.OrdinaryRank

open Set Module Finsler.BorelCochain Finsler.BorelLoop Finsler.BorelCrossing Finsler.Geometry
open Finsler.Geodesics Finsler.CriticalLevels

/-- The image of a linear map has dimension at most the dimension of the image of a subspace
plus the codimension of the subspace. -/
theorem finrank_range_le_map_add {V U : Type*} [AddCommGroup V] [AddCommGroup U]
    [Module (ZMod 2) V] [Module (ZMod 2) U] [Module.Finite (ZMod 2) V] [Module.Finite (ZMod 2) U]
    (f : V →ₗ[ZMod 2] U) (W : Submodule (ZMod 2) V) :
    finrank (ZMod 2) (LinearMap.range f) ≤
      finrank (ZMod 2) (W.map f) + finrank (ZMod 2) (V ⧸ W) := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl W
  have h1 : LinearMap.range f = W.map f ⊔ C.map f := by
    rw [← Submodule.map_sup, hC.sup_eq_top, Submodule.map_top]
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (W.map f) (C.map f)
  have h3 : finrank (ZMod 2) (C.map f) ≤ finrank (ZMod 2) C := Submodule.finrank_map_le f C
  have h4 : finrank (ZMod 2) (V ⧸ W) = finrank (ZMod 2) C :=
    (Submodule.quotientEquivOfIsCompl W C hC).finrank_eq
  rw [h1]
  omega

variable {n : ℕ} (F : ReversibleMetric n)

/-- The image of the restriction from t_c in t_a is the image under the restriction from t_b
of the image of the restriction from t_c in t_b. -/
theorem range_cut_trans {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (j : ℕ) :
    LinearMap.range (Hmap (cutHom F (hab.trans hbc)) j) =
      (LinearMap.range (Hmap (cutHom F hbc) j)).map (Hmap (cutHom F hab) j) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨Hmap (cutHom F hbc) j z, ⟨z, rfl⟩,
      (OrdinaryRestriction.Hmap_cut_cut F hab hbc j z).symm⟩
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨z, OrdinaryRestriction.Hmap_cut_cut F hab hbc j z⟩

/-- Across two regular cuts, the codimension of the image of the ordinary restriction is at
most the dimension of the ordinary crossing group in the next degree. -/
theorem finrank_quot_cut_le (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hac : a ∉ crit F) (hbc : b ∉ crit F) (j : ℕ) :
    finrank (ZMod 2) (H (levComplex F a) j ⧸ LinearMap.range (Hmap (cutHom F hab) j)) ≤
      finrank (ZMod 2) (H (crossComplex F hab) (j + 1)) := by
  obtain ⟨-, hfa, -⟩ := FiniteCut.exists_finite_H F hn hfin ha hac
  obtain ⟨-, hfb, -⟩ := FiniteCut.exists_finite_H F hn hfin (ha.trans_le hab) hbc
  have := hfa j
  have := hfb (j + 1)
  have : Module.Finite (ZMod 2) (H (crossComplex F hab) (j + 1)) :=
    OrdinaryDelta.finite_sub (shortExact F hab) j
  have h1 := OrdinaryDelta.finrank_le_range_add (shortExact F hab) j
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.range (Hmap (cutHom F hab) j))
  omega

/-- With finitely many prime closed geodesic images: if the ordinary crossing groups of single
crossings above the regular cut a have dimension at most C in degree j + 1, then for every
regular cut b ≥ a the dimension of the ordinary cohomology of (t_a, M) in degree j is at most
the dimension of the image of the restriction from t_b plus C times the number of critical
levels in [a, b]. -/
theorem finrank_le_cut_range (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ crit F) (j C : ℕ)
    (hC : ∀ (a' b' : ℝ) (hab' : a' ≤ b'), a ≤ a' → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton →
      finrank (ZMod 2) (H (crossComplex F hab') (j + 1)) ≤ C)
    {b : ℝ} (hab : a ≤ b) (hbc : b ∉ crit F) :
    finrank (ZMod 2) (H (levComplex F a) j) ≤
      finrank (ZMod 2) (LinearMap.range (Hmap (cutHom F hab) j)) +
        C * (crit F ∩ Icc a b).ncard := by
  have hfinH : ∀ x : ℝ, 0 < x → x ∉ crit F → ∀ q, Module.Finite (ZMod 2) (H (levComplex F x) q) :=
    fun x hx hxc => (FiniteCut.exists_finite_H F hn hfin hx hxc).choose_spec.1
  have hcfin : ∀ x : ℝ, (crit F ∩ Icc a x).Finite := fun x => crit_finite F hfin a x
  have hmono : ∀ {x y : ℝ}, x ≤ y → (crit F ∩ Icc a x).ncard ≤ (crit F ∩ Icc a y).ncard :=
    fun {x y} h => ncard_le_ncard (fun l hl => ⟨hl.1, hl.2.1, hl.2.2.trans h⟩) (hcfin y)
  have := hfinH a ha hac j
  -- an interval without critical levels
  have hstep_reg : ∀ {a' b' : ℝ}, 0 < a' → ∀ ha'b' : a' ≤ b', (∀ x ∈ Icc a' b', x ∉ crit F) →
      (∀ haa' : a ≤ a', finrank (ZMod 2) (H (levComplex F a) j) ≤
        finrank (ZMod 2) (LinearMap.range (Hmap (cutHom F haa') j)) +
          C * (crit F ∩ Icc a a').ncard) →
      ∀ hax : a ≤ b', finrank (ZMod 2) (H (levComplex F a) j) ≤
        finrank (ZMod 2) (LinearMap.range (Hmap (cutHom F hax) j)) +
          C * (crit F ∩ Icc a b').ncard := by
    intro a' b' ha' ha'b' hreg ih hax
    by_cases haa' : a ≤ a'
    · have hbij := OrdinaryRestriction.cut_bijective_of_regular F hn ha' ha'b' hreg j
      have hr : LinearMap.range (Hmap (cutHom F hax) j) =
          LinearMap.range (Hmap (cutHom F haa') j) := by
        rw [range_cut_trans F haa' ha'b' j, LinearMap.range_eq_top.mpr hbij.2, Submodule.map_top]
      rw [hr]
      exact (ih haa').trans (Nat.add_le_add_left (Nat.mul_le_mul_left C (hmono ha'b')) _)
    · have hbij := OrdinaryRestriction.cut_bijective_of_regular F hn ha hax
        (fun x hx => hreg x ⟨(not_le.mp haa').le.trans hx.1, hx.2⟩) j
      rw [LinearMap.range_eq_top.mpr hbij.2, finrank_top]
      exact Nat.le_add_right _ _
  have key := LevelCount.forall_levelCount F hfin
    (fun x _ => ∀ hax : a ≤ x, finrank (ZMod 2) (H (levComplex F a) j) ≤
      finrank (ZMod 2) (LinearMap.range (Hmap (cutHom F hax) j)) +
        C * (crit F ∩ Icc a x).ncard)
    ⟨a / 2, by linarith, fun x _ hx hax => by linarith⟩
    (fun a' b' ha' ha'b' hreg _ ih => hstep_reg ha' ha'b' hreg ih)
    (fun a' b' ha' ha'b' ha'c hb'c hsub _ ih hax => by
      by_cases haa' : a ≤ a'
      · by_cases hemp : ∀ x ∈ Icc a' b', x ∉ crit F
        · exact hstep_reg ha' ha'b' hemp ih hax
        obtain ⟨l, hlI, hlc⟩ : ∃ l ∈ Icc a' b', l ∈ crit F := by
          by_contra hcon
          exact hemp fun x hx hxc => hcon ⟨x, hx, hxc⟩
        have hla' : a' < l := lt_of_le_of_ne hlI.1 fun h => ha'c (h ▸ hlc)
        have := hfinH a' ha' ha'c j
        have h1 := finrank_range_le_map_add (Hmap (cutHom F haa') j)
          (LinearMap.range (Hmap (cutHom F ha'b') j))
        rw [← range_cut_trans F haa' ha'b' j] at h1
        have h2 := finrank_quot_cut_le F hn hfin ha' ha'b' ha'c hb'c j
        have h3 := hC a' b' ha'b' haa' ha'c hb'c hsub
        have h4 := ih haa'
        have hnot : l ∉ crit F ∩ Icc a a' := fun h => not_le.mpr hla' h.2.2
        have hins : insert l (crit F ∩ Icc a a') ⊆ crit F ∩ Icc a b' := by
          intro x hx
          rcases hx with rfl | hx
          · exact ⟨hlc, haa'.trans hla'.le, hlI.2⟩
          · exact ⟨hx.1, hx.2.1, hx.2.2.trans ha'b'⟩
        have hcount : (crit F ∩ Icc a a').ncard + 1 ≤ (crit F ∩ Icc a b').ncard := by
          rw [← ncard_insert_of_notMem hnot (hcfin a')]
          exact ncard_le_ncard hins (hcfin b')
        have h5 : C * ((crit F ∩ Icc a a').ncard + 1) ≤ C * (crit F ∩ Icc a b').ncard :=
          Nat.mul_le_mul_left C hcount
        have h6 : C * ((crit F ∩ Icc a a').ncard + 1) = C * (crit F ∩ Icc a a').ncard + C := by
          ring
        have h1' : finrank (ZMod 2) (LinearMap.range (Hmap (cutHom F haa') j)) ≤
            finrank (ZMod 2) (LinearMap.range (Hmap (cutHom F hax) j)) +
              finrank (ZMod 2) (H (levComplex F a') j ⧸
                LinearMap.range (Hmap (cutHom F ha'b') j)) := h1
        omega
      · by_cases hemp : ∀ x ∈ Icc a b', x ∉ crit F
        · have hbij := OrdinaryRestriction.cut_bijective_of_regular F hn ha hax hemp j
          rw [LinearMap.range_eq_top.mpr hbij.2, finrank_top]
          exact Nat.le_add_right _ _
        obtain ⟨l, hlI, hlc⟩ : ∃ l ∈ Icc a b', l ∈ crit F := by
          by_contra hcon
          exact hemp fun x hx hxc => hcon ⟨x, hx, hxc⟩
        have h2 := finrank_quot_cut_le F hn hfin ha hax hac hb'c j
        have h3 := hC a b' hax le_rfl hac hb'c
          (hsub.anti (inter_subset_inter_right _ (Icc_subset_Icc (not_le.mp haa').le le_rfl)))
        have h4 := Submodule.finrank_quotient_add_finrank
          (LinearMap.range (Hmap (cutHom F hax) j))
        have hpos : 1 ≤ (crit F ∩ Icc a b').ncard :=
          (ncard_pos (hcfin b')).mpr ⟨l, hlc, hlI⟩
        have h5 : C ≤ C * (crit F ∩ Icc a b').ncard := Nat.le_mul_of_pos_right C hpos
        omega)
    b (ha.trans_le hab) hbc
  exact key hab

/-- With finitely many prime closed geodesic images: under the hypothesis of
`finrank_le_cut_range`, if the image of the restriction from t_b lies in the image of the
restriction from the loop space, whose dimension is at most G, and at most K critical levels lie
in [a, b], the ordinary cohomology of (t_a, M) in degree j has dimension at most G + C K. -/
theorem finrank_lev_le_of_fill (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hac : a ∉ crit F) (hbc : b ∉ crit F) (j C G K : ℕ)
    (hC : ∀ (a' b' : ℝ) (hab' : a' ≤ b'), a ≤ a' → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton →
      finrank (ZMod 2) (H (crossComplex F hab') (j + 1)) ≤ C)
    (hfill : ∀ y : H (levComplex F b) j,
      ∃ x : H (fullComplex n) j, Hmap (resHom F a) j x = Hmap (cutHom F hab) j y)
    (hG : finrank (ZMod 2) (LinearMap.range (Hmap (resHom F a) j)) ≤ G)
    (hK : (crit F ∩ Icc a b).ncard ≤ K) :
    finrank (ZMod 2) (H (levComplex F a) j) ≤ G + C * K := by
  have := (FiniteCut.exists_finite_H F hn hfin ha hac).choose_spec.1 j
  have h1 := finrank_le_cut_range F hn hfin ha hac j C hC hab hbc
  have h2 : LinearMap.range (Hmap (cutHom F hab) j) ≤ LinearMap.range (Hmap (resHom F a) j) := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hfill y
    exact ⟨x, hx⟩
  have h3 := Submodule.finrank_mono h2
  have h4 := Nat.mul_le_mul_left C hK
  omega

end Finsler.OrdinaryRank
