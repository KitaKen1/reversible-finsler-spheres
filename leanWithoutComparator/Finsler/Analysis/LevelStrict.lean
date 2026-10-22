module

public import Finsler.Analysis.LevelAssembly

/-! Strict decrease of the deformed function along the glued field. With the assembly of a level
(cutoffs χ_i with pairwise disjoint closed supports, fields W_i, a background field V,
deformations β_i supported where χ_i = 1), the derivative of f + Σ β_i in the direction of the
glued field is negative at a point of O in each of the following cases: the point lies in the
closed support of β_i and f + β_i decreases strictly along W_i there; or it lies in no closed
support of a β_j and either it lies in no closed support of a cutoff and f decreases strictly
along V, or it lies in the closed support of χ_i and f decreases strictly along V with χ_i < 1,
or along W_i with χ_i > 0. -/

@[expose] public section

namespace Finsler.LevelStrict

open Set Filter
open Finsler.GlueField Finsler.LevelGlue Finsler.LevelAssembly
open scoped Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
  {s : Finset ι} {U : ι → Set E} {χ : ι → E → ℝ} {W : ι → E → E} {V : E → E}
  {β : ι → E → ℝ} {f : E → ℝ}

/-- **Strict decrease at a point of the closed support of a deformation.** -/
theorem lt_zero_at_label
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hβ : ∀ i ∈ s, ∀ y ∈ tsupport (β i), χ i y = 1) (hsupp : ∀ i ∈ s, tsupport (χ i) ⊆ U i)
    {i : ι} (hi : i ∈ s) {y : E} (hy : y ∈ tsupport (β i))
    (hlt : fderiv ℝ (fun y => f y + β i y) y (W i y) < 0) :
    fderiv ℝ (fun y => f y + ∑ j ∈ s, β j y) y (sumGlue s U χ W V y) < 0 := by
  rw [fderiv_at_label hdis hβ hsupp hi hy]
  exact hlt

/-- **Strict decrease off the deformations.** -/
theorem lt_zero_off_labels {O : Set E}
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hχ0 : ∀ i ∈ s, ∀ y, 0 ≤ χ i y) (hχ1 : ∀ i ∈ s, ∀ y, χ i y ≤ 1)
    (hsupp : ∀ i ∈ s, tsupport (χ i) ⊆ U i)
    (hW : ∀ i ∈ s, ∀ y ∈ tsupport (χ i), fderiv ℝ f y (W i y) ≤ 0)
    (hV : ∀ y ∈ O, fderiv ℝ f y (V y) ≤ 0) {y : E} (hy : y ∈ O)
    (hno : ∀ j ∈ s, y ∉ tsupport (β j))
    (hcase : ((∀ i ∈ s, y ∉ tsupport (χ i)) ∧ fderiv ℝ f y (V y) < 0) ∨
      (∃ i ∈ s, y ∈ tsupport (χ i) ∧ ((fderiv ℝ f y (V y) < 0 ∧ χ i y < 1) ∨
        (fderiv ℝ f y (W i y) < 0 ∧ 0 < χ i y ∧ y ∈ U i)))) :
    fderiv ℝ (fun y => f y + ∑ j ∈ s, β j y) y (sumGlue s U χ W V y) < 0 := by
  rw [fderiv_off_labels hno]
  exact (sumGlue_descent f hdis hχ0 hχ1 hsupp hW hV hy).2 hcase

/-- Where all cutoffs vanish, the glued field is the background field. -/
theorem sumGlue_of_cutoffs_zero {y : E} (hy : ∀ i ∈ s, y ∉ tsupport (χ i)) :
    sumGlue s U χ W V y = V y :=
  sumGlue_eq_of_not_mem hy

end

end Finsler.LevelStrict
