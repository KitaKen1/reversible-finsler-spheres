module

public import Finsler.Analysis.LevelGlue

/-! The assembly of a level: one field and one deformed function. Let f be differentiable on an
open set O of a finite dimensional real normed space, V a smooth field with D f(V) ≤ 0 on O, and
for finitely many labels i let χ_i be cutoffs with values in [0, 1] and pairwise disjoint closed
supports inside open sets U_i ⊆ O, W_i fields smooth on U_i with D f(W_i) ≤ 0 on the closed
support of χ_i, and β_i differentiable functions whose closed supports lie where χ_i = 1. Put

  V_glob = Σ_i χ_i W_i + (1 - Σ_i χ_i) V,   g' = f + Σ_i β_i.

At a point of the closed support of β_i the field is W_i and the derivative of g' is the
derivative of f + β_i; outside the closed supports of all β_i the derivative of g' is that of
f. Hence g' does not increase along V_glob on O if f + β_i does not increase along W_i on the
closed support of β_i, with strict decrease where the pieces are strict. -/

@[expose] public section

namespace Finsler.LevelAssembly

open Set Filter
open Finsler.GlueField Finsler.LevelGlue
open scoped Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

omit [NormedSpace ℝ E] in
/-- The closed supports of functions supported where pairwise disjoint cutoffs are 1 are
pairwise disjoint. -/
theorem disjoint_of_eq_one {s : Finset ι} {χ : ι → E → ℝ} {β : ι → E → ℝ}
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hβ : ∀ i ∈ s, ∀ y ∈ tsupport (β i), χ i y = 1) :
    ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (β i)) (tsupport (β j)) := by
  intro i hi j hj hij
  rw [Set.disjoint_left]
  intro y hyi hyj
  have h1 : y ∈ tsupport (χ i) :=
    subset_tsupport _ (by rw [Function.mem_support, hβ i hi y hyi]; exact one_ne_zero)
  have h2 : y ∈ tsupport (χ j) :=
    subset_tsupport _ (by rw [Function.mem_support, hβ j hj y hyj]; exact one_ne_zero)
  exact Set.disjoint_left.mp (hdis i hi j hj hij) h1 h2

omit [NormedSpace ℝ E] in
/-- Near a point of the closed support of β_i the sum of the β_j is β_i. -/
theorem sum_eventuallyEq_of_mem {s : Finset ι} {β : ι → E → ℝ}
    (hdisβ : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (β i)) (tsupport (β j)))
    {i : ι} (hi : i ∈ s) {y : E} (hy : y ∈ tsupport (β i)) :
    (fun y => ∑ j ∈ s, β j y) =ᶠ[𝓝 y] β i := by
  classical
  have hev : ∀ j ∈ s.erase i, ∀ᶠ y' in 𝓝 y, β j y' = 0 := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hy' : y ∉ tsupport (β j) := fun h =>
      Set.disjoint_left.mp (hdisβ i hi j (Finset.mem_of_mem_erase hj) (Ne.symm hji)) hy h
    filter_upwards [(isClosed_tsupport (β j)).isOpen_compl.mem_nhds hy'] with y' hy''
    exact image_eq_zero_of_notMem_tsupport hy''
  have hall : ∀ᶠ y' in 𝓝 y, ∀ j ∈ s.erase i, β j y' = 0 :=
    (Filter.eventually_all_finset (s.erase i)).mpr hev
  filter_upwards [hall] with y' hy'
  rw [← Finset.add_sum_erase s _ hi, Finset.sum_eq_zero hy', add_zero]

omit [NormedSpace ℝ E] in
/-- Outside the closed supports of all β_j their sum vanishes nearby. -/
theorem sum_eventuallyEq_zero {s : Finset ι} {β : ι → E → ℝ} {y : E}
    (hy : ∀ j ∈ s, y ∉ tsupport (β j)) : (fun y => ∑ j ∈ s, β j y) =ᶠ[𝓝 y] fun _ => 0 := by
  have hev : ∀ j ∈ s, ∀ᶠ y' in 𝓝 y, β j y' = 0 := by
    intro j hj
    filter_upwards [(isClosed_tsupport (β j)).isOpen_compl.mem_nhds (hy j hj)] with y' hy'
    exact image_eq_zero_of_notMem_tsupport hy'
  filter_upwards [(Filter.eventually_all_finset s).mpr hev] with y' hy'
  exact Finset.sum_eq_zero hy'

variable {s : Finset ι} {U : ι → Set E} {χ : ι → E → ℝ} {W : ι → E → E} {V : E → E}
  {β : ι → E → ℝ} {f : E → ℝ}

/-- **The derivative of the deformed function along the glued field at a point of the closed
support of β_i.** -/
theorem fderiv_at_label
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hβ : ∀ i ∈ s, ∀ y ∈ tsupport (β i), χ i y = 1) (hsupp : ∀ i ∈ s, tsupport (χ i) ⊆ U i)
    {i : ι} (hi : i ∈ s) {y : E} (hy : y ∈ tsupport (β i)) :
    fderiv ℝ (fun y => f y + ∑ j ∈ s, β j y) y (sumGlue s U χ W V y) =
      fderiv ℝ (fun y => f y + β i y) y (W i y) := by
  have hdisβ := disjoint_of_eq_one hdis hβ
  have he : (fun y => f y + ∑ j ∈ s, β j y) =ᶠ[𝓝 y] fun y => f y + β i y := by
    filter_upwards [sum_eventuallyEq_of_mem hdisβ hi hy] with y' hy'
    rw [hy']
  have hχy : χ i y = 1 := hβ i hi y hy
  have hyχ : y ∈ tsupport (χ i) :=
    subset_tsupport _ (by rw [Function.mem_support, hχy]; exact one_ne_zero)
  rw [he.fderiv_eq, sumGlue_eq_glue hdis hi hyχ, glue_of_eq_one (hsupp i hi) hχy]

/-- **The derivative of the deformed function along the glued field outside the closed
supports of the β_j.** -/
theorem fderiv_off_labels {y : E} (hy : ∀ j ∈ s, y ∉ tsupport (β j)) :
    fderiv ℝ (fun y => f y + ∑ j ∈ s, β j y) y (sumGlue s U χ W V y) =
      fderiv ℝ f y (sumGlue s U χ W V y) := by
  have he : (fun y => f y + ∑ j ∈ s, β j y) =ᶠ[𝓝 y] f := by
    filter_upwards [sum_eventuallyEq_zero hy] with y' hy'
    rw [hy', add_zero]
  rw [he.fderiv_eq]

/-- **Descent of the deformed function along the glued field.** If f + β_i does not increase
along W_i on the closed support of β_i, f does not increase along W_i on the closed support of
χ_i and along V on O, then f + Σ β_i does not increase along the glued field on O. -/
theorem deform_descent {O : Set E}
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hχ0 : ∀ i ∈ s, ∀ y, 0 ≤ χ i y) (hχ1 : ∀ i ∈ s, ∀ y, χ i y ≤ 1)
    (hsupp : ∀ i ∈ s, tsupport (χ i) ⊆ U i)
    (hβ : ∀ i ∈ s, ∀ y ∈ tsupport (β i), χ i y = 1)
    (hWβ : ∀ i ∈ s, ∀ y ∈ tsupport (β i), fderiv ℝ (fun y => f y + β i y) y (W i y) ≤ 0)
    (hW : ∀ i ∈ s, ∀ y ∈ tsupport (χ i), fderiv ℝ f y (W i y) ≤ 0)
    (hV : ∀ y ∈ O, fderiv ℝ f y (V y) ≤ 0) {y : E} (hy : y ∈ O) :
    fderiv ℝ (fun y => f y + ∑ j ∈ s, β j y) y (sumGlue s U χ W V y) ≤ 0 := by
  by_cases hin : ∃ i ∈ s, y ∈ tsupport (β i)
  · obtain ⟨i, hi, hyi⟩ := hin
    rw [fderiv_at_label hdis hβ hsupp hi hyi]
    exact hWβ i hi y hyi
  · have hno : ∀ j ∈ s, y ∉ tsupport (β j) := fun j hj hyj => hin ⟨j, hj, hyj⟩
    rw [fderiv_off_labels hno]
    exact (sumGlue_descent f hdis hχ0 hχ1 hsupp hW hV hy).1

end

end Finsler.LevelAssembly
