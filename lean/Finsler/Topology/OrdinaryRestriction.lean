module

public import Finsler.Topology.OrdinaryExact
public import Finsler.Topology.BorelCrossing
public import Finsler.Topology.CrossingW
public import Finsler.Topology.LevelCount

/-! Bijectivity of the ordinary restriction from the vanishing of the ordinary cohomology of the
subcomplex. For a degreewise short exact sequence 0 → K' → K → K'' → 0 of F₂-cochain complexes,
the map H K n → H K'' n is injective if H K' n = 0 and surjective if H K' (n + 1) = 0 (the
converse statements are in `OrdinaryExact`). For the loop space: if the ordinary cohomology of
the crossing pair (t_b, t_a) vanishes in the degrees j and j + 1, the restriction from t_b to
t_a relative to the constant loops is bijective in degree j. With finitely many prime closed
geodesic images the same holds across any number of critical levels: if the ordinary crossing
groups of all single crossings between two regular cuts vanish in the degrees j and j + 1, the
restriction between the two cuts is bijective in degree j (induction over the critical levels,
with the level deformations on intervals without critical levels). -/

@[expose] public section

namespace Finsler.OrdinaryRestriction

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelExact Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels

section Abstract

variable {K' K K'' : InvComplex} {ι : InvHom K' K} {π : InvHom K K''} (h : ShortExact ι π)

include h

/-- If the ordinary cohomology of the subcomplex vanishes in degree n, the restriction is
injective in degree n. -/
theorem restriction_injective (n : ℕ) (hsub : ∀ z : H K' n, z = 0) :
    Function.Injective (Hmap π n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := exact_mid_ordinary h n x hx
  rw [hsub z, map_zero]

/-- If the ordinary cohomology of the subcomplex vanishes in degree n + 1, the restriction is
surjective in degree n. -/
theorem restriction_surjective (n : ℕ) (hsub : ∀ z : H K' (n + 1), z = 0) :
    Function.Surjective (Hmap π n) := by
  intro y
  obtain ⟨c'', rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have hc'' : K''.d n (c'' : K''.C n) = 0 := c''.2
  obtain ⟨c, hc⟩ := h.surj n (c'' : K''.C n)
  have hπ : π.f (n + 1) (K.d n c) = 0 := by rw [π.comm_d, hc, hc'']
  obtain ⟨z', hz'⟩ := h.exact (n + 1) _ hπ
  have hz'd : K'.d (n + 1) z' = 0 := by
    apply h.inj (n + 1 + 1)
    rw [ι.comm_d, hz', K.dd, map_zero]
  have h0 := hsub (Submodule.Quotient.mk ⟨z', hz'd⟩)
  rw [Submodule.Quotient.mk_eq_zero] at h0
  have h0' : z' ∈ coboundaries K' (n + 1) := h0
  obtain ⟨u', hu'⟩ := h0'
  have hcoc : K.d n (c - ι.f n u') = 0 := by
    rw [map_sub, ← ι.comm_d, hu', hz', sub_self]
  refine ⟨Submodule.Quotient.mk ⟨c - ι.f n u', hcoc⟩, ?_⟩
  rw [Hmap, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  change π.f n (c - ι.f n u') = (c'' : K''.C n)
  rw [map_sub, h.zero, sub_zero, hc]

/-- If the ordinary cohomology of the subcomplex vanishes in the degrees n and n + 1, the
restriction is bijective in degree n. -/
theorem restriction_bijective (n : ℕ) (hsub : ∀ z : H K' n, z = 0)
    (hsub' : ∀ z : H K' (n + 1), z = 0) : Function.Bijective (Hmap π n) :=
  ⟨restriction_injective h n hsub, restriction_surjective h n hsub'⟩

end Abstract

variable {n : ℕ} (F : ReversibleMetric n) {a b : ℝ} (hab : a ≤ b)

/-- If the ordinary cohomology of the crossing pair (t_b, t_a) vanishes in the degrees j and
j + 1, the ordinary restriction from t_b to t_a, relative to the constant loops, is bijective in
degree j. -/
theorem cut_bijective (j : ℕ) (h0 : ∀ z : H (crossComplex F hab) j, z = 0)
    (h1 : ∀ z : H (crossComplex F hab) (j + 1), z = 0) :
    Function.Bijective (Hmap (cutHom F hab) j) :=
  restriction_bijective (shortExact F hab) j h0 h1

/-- If the ordinary cohomology of the tail pair (Λ, t_a) vanishes in the degrees j and j + 1,
the ordinary restriction from the loop space to t_a, relative to the constant loops, is
bijective in degree j. -/
theorem res_bijective (a : ℝ) (j : ℕ) (h0 : ∀ z : H (tailComplex F a) j, z = 0)
    (h1 : ∀ z : H (tailComplex F a) (j + 1), z = 0) :
    Function.Bijective (Hmap (resHom F a) j) :=
  restriction_bijective (shortExactTail F a) j h0 h1

/-- The inclusions of the pairs (t_a, M) → (t_b, M) → (t_c, M) compose. -/
theorem cutPair_cutPair {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    cutPair F hab ≫ cutPair F hbc = cutPair F (hab.trans hbc) := by
  have h : (inclLev F hbc).comp (inclLev F hab) = inclLev F (hab.trans hbc) := by
    ext u
    rfl
  exact (pairMap_comp _ _ _ (inclLev F hab) (inclLev F hbc) (fun _ hx => hx)
    (fun _ hx => hx)).symm.trans (pairMap_congr _ _ h _ (fun _ hx => hx))

/-- Restriction from t_c to t_a is the composite of the restrictions through t_b. -/
theorem cut_cut_f {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (j : ℕ) (x : (levComplex F c).C j) :
    (invHomComp (cutHom F hbc) (cutHom F hab)).f j x = (cutHom F (hab.trans hbc)).f j x := by
  have h := pullHom_comp (revPair_sq F a) (revPair_sq F b) (revPair_sq F c) (cutPair F hab)
    (cutPair F hbc) (cutPair_equivariant F hab) (cutPair_equivariant F hbc)
    (by rw [cutPair_cutPair]; exact cutPair_equivariant F (hab.trans hbc)) j x
  rw [← h]
  change ((pull (cutPair F hab ≫ cutPair F hbc)).f j).hom x =
    ((pull (cutPair F (hab.trans hbc))).f j).hom x
  rw [cutPair_cutPair]

/-- On ordinary cohomology, restriction from t_c to t_a is the composite of the restrictions
through t_b. -/
theorem Hmap_cut_cut {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (j : ℕ) (z : H (levComplex F c) j) :
    Hmap (cutHom F (hab.trans hbc)) j z = Hmap (cutHom F hab) j (Hmap (cutHom F hbc) j z) := by
  rw [← Hmap_comp]
  exact (Hmap_congr (cut_cut_f F hab hbc) j z).symm

/-- If the restrictions from t_c to t_b and from t_b to t_a are bijective on ordinary
cohomology of degree j, so is the restriction from t_c to t_a. -/
theorem cut_bijective_trans {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (j : ℕ)
    (h1 : Function.Bijective (Hmap (cutHom F hab) j))
    (h2 : Function.Bijective (Hmap (cutHom F hbc) j)) :
    Function.Bijective (Hmap (cutHom F (hab.trans hbc)) j) := by
  have h : ⇑(Hmap (cutHom F (hab.trans hbc)) j) =
      ⇑(Hmap (cutHom F hab) j) ∘ ⇑(Hmap (cutHom F hbc) j) :=
    funext fun z => Hmap_cut_cut F hab hbc j z
  rw [h]
  exact h1.comp h2

/-- The ordinary restriction is bijective along an interval without critical levels. -/
theorem cut_bijective_of_regular (hn : 1 ≤ n) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hreg : ∀ x ∈ Icc a b, x ∉ crit F) (j : ℕ) : Function.Bijective (Hmap (cutHom F hab) j) := by
  obtain ⟨D⟩ := CrossingW.levelDeformation_of_regular F hn a b b ha hab le_rfl hreg
  exact BorelDeformation.cut_bijective_ordinary F hab (RegularInterval.toDeformationConsts D) j

/-- With finitely many prime closed geodesic images: if the ordinary crossing groups of all
single crossings between the regular cuts a ≤ b vanish in the degrees j and j + 1, the ordinary
restriction from t_b to t_a is bijective in degree j. -/
theorem cut_bijective_of_crossings (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hac : a ∉ crit F) (hbc : b ∉ crit F) (j : ℕ)
    (hcr : ∀ (a' b' : ℝ) (hab' : a' ≤ b'), a ≤ a' → b' ≤ b → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton →
      (∀ z : H (crossComplex F hab') j, z = 0) ∧
        ∀ z : H (crossComplex F hab') (j + 1), z = 0) :
    Function.Bijective (Hmap (cutHom F hab) j) := by
  have key := LevelCount.forall_levelCount F hfin
    (fun x _ => ∀ hax : a ≤ x, x ≤ b → Function.Bijective (Hmap (cutHom F hax) j))
    ⟨a / 2, by linarith, fun x _ hx hax _ => by linarith⟩
    (fun a' b' ha' ha'b' hreg _ ih hax hb'b => by
      by_cases haa' : a ≤ a'
      · exact cut_bijective_trans F haa' ha'b' j (ih haa' (ha'b'.trans hb'b))
          (cut_bijective_of_regular F hn ha' ha'b' hreg j)
      · exact cut_bijective_of_regular F hn ha hax
          (fun x hx => hreg x ⟨(not_le.mp haa').le.trans hx.1, hx.2⟩) j)
    (fun a' b' ha' ha'b' ha'c hb'c hsub _ ih hax hb'b => by
      by_cases haa' : a ≤ a'
      · obtain ⟨h0, h1⟩ := hcr a' b' ha'b' haa' hb'b ha'c hb'c hsub
        exact cut_bijective_trans F haa' ha'b' j (ih haa' (ha'b'.trans hb'b))
          (cut_bijective F ha'b' j h0 h1)
      · obtain ⟨h0, h1⟩ := hcr a b' hax le_rfl hb'b hac hb'c
          (hsub.anti (inter_subset_inter_right _
            (Icc_subset_Icc (not_le.mp haa').le le_rfl)))
        exact cut_bijective F hax j h0 h1)
    b (ha.trans_le hab) hbc
  exact key hab le_rfl

end Finsler.OrdinaryRestriction
