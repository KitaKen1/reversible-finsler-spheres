module

public import Finsler.Topology.OrdinaryRestriction
public import Finsler.Topology.SmallLevel
public import Finsler.Topology.RegularInterval

/-! Consequences of the vanishing of crossing groups in a fixed degree, with finitely many prime
closed geodesic images. If the reflection Borel crossing groups of all single crossings below a
regular cut a vanish in degree j, the reflection Borel cohomology of (t_a, M) vanishes in degree
j (induction over the critical levels, starting from the vanishing at small levels). If the
ordinary restriction from t_b to t_a is surjective in degree j and its image lies in the image
of the restriction from the loop space, the restriction from the loop space to t_a is surjective
in degree j. The vanishing statements for single crossings are hypotheses. -/

@[expose] public section

namespace Finsler.CrossingSupport

open Set Finsler.BorelCochain Finsler.BorelLoop Finsler.BorelCrossing Finsler.Geometry
open Finsler.Geodesics Finsler.CriticalLevels

variable {n : ℕ} (F : ReversibleMetric n)

/-- With finitely many prime closed geodesic images: if the reflection Borel crossing groups of
all single crossings below the regular cut a vanish in degree j, the reflection Borel cohomology
of (t_a, M) vanishes in degree j. -/
theorem lev_eq_zero_of_crossings (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ}
    (ha : 0 < a) (hac : a ∉ crit F) (j : ℕ)
    (hcr : ∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → b' ≤ a → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton → ∀ z : HR (crossComplex F hab') j, z = 0)
    (x : HR (levComplex F a) j) : x = 0 := by
  have key := LevelCount.forall_levelCount F hfin
    (fun b _ => b ≤ a → ∀ y : HR (levComplex F b) j, y = 0)
    (by
      obtain ⟨b₀, hb₀, hzero⟩ := SmallLevel.exists_HR_lev_eq_zero F
      exact ⟨b₀, hb₀, fun b hb hbb _ y => hzero b hb hbb j y⟩)
    (fun a' b' ha' ha'b' hreg _ ih hb'a y => by
      obtain ⟨D⟩ := CrossingW.levelDeformation_of_regular F hn a' b' b' ha' ha'b' le_rfl hreg
      apply (RegularInterval.cut_bijective_of_levelDeformation F ha'b' D j).1
      have h := ih (ha'b'.trans hb'a) (HRmap (cutHom F ha'b') j y)
      rw [h, map_zero])
    (fun a' b' ha' ha'b' ha'c hb'c hsub _ ih hb'a y => by
      obtain ⟨z, rfl⟩ := exact_crossing F ha'b' j y (ih (ha'b'.trans hb'a) _)
      rw [hcr a' b' ha'b' ha' hb'a ha'c hb'c hsub z, map_zero])
    a ha hac
  exact key le_rfl x

/-- If the ordinary restriction from t_b to t_a is surjective in degree j and its image lies in
the image of the restriction from the loop space, the restriction from the loop space to t_a is
surjective in degree j. -/
theorem res_surjective_of_cut {a b : ℝ} (hab : a ≤ b) (j : ℕ)
    (hcut : Function.Surjective (Hmap (cutHom F hab) j))
    (hfill : ∀ y : H (levComplex F b) j,
      ∃ x : H (fullComplex n) j, Hmap (resHom F a) j x = Hmap (cutHom F hab) j y) :
    Function.Surjective (Hmap (resHom F a) j) := fun y => by
  obtain ⟨y', rfl⟩ := hcut y
  exact hfill y'

/-- With finitely many prime closed geodesic images: if the ordinary crossing groups of all
single crossings between the regular cuts a ≤ b vanish in the degrees j and j + 1 and the image
of the restriction from t_b lies in the image of the restriction from the loop space, the
ordinary restriction from the loop space to t_a is surjective in degree j. -/
theorem res_surjective_of_crossings (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hac : a ∉ crit F) (hbc : b ∉ crit F) (j : ℕ)
    (hcr : ∀ (a' b' : ℝ) (hab' : a' ≤ b'), a ≤ a' → b' ≤ b → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton →
      (∀ z : H (crossComplex F hab') j, z = 0) ∧
        ∀ z : H (crossComplex F hab') (j + 1), z = 0)
    (hfill : ∀ y : H (levComplex F b) j,
      ∃ x : H (fullComplex n) j, Hmap (resHom F a) j x = Hmap (cutHom F hab) j y) :
    Function.Surjective (Hmap (resHom F a) j) :=
  res_surjective_of_cut F hab j
    (OrdinaryRestriction.cut_bijective_of_crossings F hn hfin ha hab hac hbc j hcr).2 hfill

end Finsler.CrossingSupport
