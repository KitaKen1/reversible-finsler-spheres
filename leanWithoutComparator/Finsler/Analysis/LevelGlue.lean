module

public import Finsler.Analysis.GlueField
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Cutoffs and the gluing of finitely many local fields. In a finite dimensional real normed
space, a compact set T inside an open set U has a smooth cutoff with values in [0, 1] which is 1
on an open neighbourhood of T and whose closed support is compact and contained in U (smooth
Urysohn lemma applied to a thickening). Given finitely many open sets U_i with cutoffs χ_i whose
closed supports are pairwise disjoint, fields W_i smooth on U_i, and a smooth field V, the field

  Σ_i χ_i W_i + (1 - Σ_i χ_i) V

(each χ_i W_i extended by zero outside U_i) is smooth, has compact support if V has, agrees at
each point of the closed support of χ_i with the single gluing of W_i and V, and agrees with V
outside all these supports. -/

@[expose] public section

namespace Finsler.LevelGlue

open Set Filter Metric
open Finsler.GlueField
open scoped Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A smooth cutoff.** A compact set inside an open set has a smooth cutoff with values in
[0, 1], equal to 1 on an open neighbourhood of the compact set, with compact closed support
inside the open set. -/
theorem exists_cutoff {T U : Set E} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U) :
    ∃ (χ : E → ℝ) (W : Set E), ContDiff ℝ ∞ χ ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ IsOpen W ∧ T ⊆ W ∧ ∀ y ∈ W, χ y = 1 := by
  obtain ⟨δ, hδ, hsub⟩ := hT.exists_cthickening_subset_open hU hTU
  have hs : IsOpen (thickening δ T) := isOpen_thickening
  have ht : IsClosed (cthickening (δ / 2) T) := isClosed_cthickening
  have hts : cthickening (δ / 2) T ⊆ thickening δ T :=
    cthickening_subset_thickening' hδ (half_lt_self hδ) T
  obtain ⟨χ, hχ, hrange, hsupp, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := ⊤) hs ht hts
  have htsupp : tsupport χ ⊆ cthickening δ T := by
    unfold tsupport
    rw [hsupp]
    exact closure_thickening_subset_cthickening δ T
  refine ⟨χ, thickening (δ / 2) T, hχ, fun y => hrange (mem_range_self y), ?_, htsupp.trans hsub,
    isOpen_thickening, self_subset_thickening (half_pos hδ) T, fun y hy => ?_⟩
  · exact (hT.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport χ) htsupp
  · exact (hone y).mp (thickening_subset_cthickening _ _ hy)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A finite sum of compactly supported functions has compact support. -/
theorem hasCompactSupport_finsetSum {ι : Type*} (t : Finset ι) {f : ι → E → E}
    (hf : ∀ i ∈ t, HasCompactSupport (f i)) : HasCompactSupport (fun y => ∑ i ∈ t, f i y) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert a t ha ih =>
    have e : (fun y => ∑ i ∈ insert a t, f i y) = fun y => f a y + ∑ i ∈ t, f i y := by
      funext y
      rw [Finset.sum_insert ha]
    rw [e]
    exact (hf a (Finset.mem_insert_self a t)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

variable {ι : Type*} (s : Finset ι) (U : ι → Set E) (χ : ι → E → ℝ) (W : ι → E → E) (V : E → E)

/-- The field glued from finitely many local fields and a background field. -/
def sumGlue (y : E) : E :=
  ∑ i ∈ s, cutField (U i) (χ i) (W i) y + (1 - ∑ i ∈ s, χ i y) • V y

variable {s U χ W V}

omit [FiniteDimensional ℝ E] in
/-- At a point of the closed support of χ_i the glued field is the single gluing of W_i and V. -/
theorem sumGlue_eq_glue (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {i : ι} (hi : i ∈ s) {y : E} (hy : y ∈ tsupport (χ i)) :
    sumGlue s U χ W V y = glue (U i) (χ i) (W i) V y := by
  have hother : ∀ j ∈ s, j ≠ i → y ∉ tsupport (χ j) := fun j hj hji hyj =>
    Set.disjoint_left.mp (hdis i hi j hj (Ne.symm hji)) hy hyj
  have h1 : ∑ j ∈ s, cutField (U j) (χ j) (W j) y = cutField (U i) (χ i) (W i) y :=
    Finset.sum_eq_single_of_mem i hi fun j hj hji =>
      cutField_of_not_mem_tsupport (hother j hj hji)
  have h2 : ∑ j ∈ s, χ j y = χ i y :=
    Finset.sum_eq_single_of_mem i hi fun j hj hji =>
      image_eq_zero_of_notMem_tsupport (hother j hj hji)
  unfold sumGlue glue
  rw [h1, h2]

omit [FiniteDimensional ℝ E] in
/-- Outside all closed supports of the cutoffs the glued field is the background field. -/
theorem sumGlue_eq_of_not_mem {y : E} (hy : ∀ i ∈ s, y ∉ tsupport (χ i)) :
    sumGlue s U χ W V y = V y := by
  have h1 : ∑ j ∈ s, cutField (U j) (χ j) (W j) y = 0 :=
    Finset.sum_eq_zero fun j hj => cutField_of_not_mem_tsupport (hy j hj)
  have h2 : ∑ j ∈ s, χ j y = 0 :=
    Finset.sum_eq_zero fun j hj => image_eq_zero_of_notMem_tsupport (hy j hj)
  unfold sumGlue
  rw [h1, h2, sub_zero, one_smul, zero_add]

omit [FiniteDimensional ℝ E] in
/-- The glued field is smooth. -/
theorem sumGlue_contDiff (hU : ∀ i ∈ s, IsOpen (U i)) (hχ : ∀ i ∈ s, ContDiff ℝ ∞ (χ i))
    (hsupp : ∀ i ∈ s, tsupport (χ i) ⊆ U i) (hW : ∀ i ∈ s, ContDiffOn ℝ ∞ (W i) (U i))
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (sumGlue s U χ W V) :=
  (ContDiff.sum fun i hi => cutField_contDiff (hU i hi) (hχ i hi) (hsupp i hi) (hW i hi)).add
    ((contDiff_const.sub (ContDiff.sum fun i hi => hχ i hi)).smul hV)

omit [FiniteDimensional ℝ E] in
/-- The glued field has compact support if the cutoffs and the background field have. -/
theorem sumGlue_hasCompactSupport (hχc : ∀ i ∈ s, HasCompactSupport (χ i))
    (hVc : HasCompactSupport V) : HasCompactSupport (sumGlue s U χ W V) := by
  classical
  have h1 : ∀ i ∈ s, HasCompactSupport (cutField (U i) (χ i) (W i)) := fun i hi =>
    (hχc i hi).mono' fun y hy => by
      by_contra h
      exact hy (cutField_of_not_mem_tsupport h)
  have h2 : HasCompactSupport (fun y => (1 - ∑ i ∈ s, χ i y) • V y) :=
    hVc.smul_left (f := fun y => 1 - ∑ i ∈ s, χ i y)
  have h3 : HasCompactSupport (fun y => ∑ i ∈ s, cutField (U i) (χ i) (W i) y) :=
    hasCompactSupport_finsetSum s h1
  exact h3.add h2

omit [FiniteDimensional ℝ E] in
/-- **Descent of the glued field.** If the cutoffs take values in [0, 1] and have pairwise
disjoint closed supports inside the U_i, the derivative of f is nonpositive in the direction of
W_i on the closed support of χ_i and in the direction of V on O, then it is nonpositive in the
direction of the glued field on O, and negative at a point of O outside all closed supports
where it is negative in the direction of V, or at a point of the closed support of χ_i where it
is negative in the direction of V and χ_i < 1, or negative in the direction of W_i and χ_i > 0. -/
theorem sumGlue_descent {O : Set E} (f : E → ℝ)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hχ0 : ∀ i ∈ s, ∀ y, 0 ≤ χ i y) (hχ1 : ∀ i ∈ s, ∀ y, χ i y ≤ 1)
    (hsupp : ∀ i ∈ s, tsupport (χ i) ⊆ U i)
    (hW : ∀ i ∈ s, ∀ y ∈ tsupport (χ i), fderiv ℝ f y (W i y) ≤ 0)
    (hV : ∀ y ∈ O, fderiv ℝ f y (V y) ≤ 0) {y : E} (hy : y ∈ O) :
    fderiv ℝ f y (sumGlue s U χ W V y) ≤ 0 ∧
      (((∀ i ∈ s, y ∉ tsupport (χ i)) ∧ fderiv ℝ f y (V y) < 0) ∨
        (∃ i ∈ s, y ∈ tsupport (χ i) ∧ ((fderiv ℝ f y (V y) < 0 ∧ χ i y < 1) ∨
          (fderiv ℝ f y (W i y) < 0 ∧ 0 < χ i y ∧ y ∈ U i))) →
        fderiv ℝ f y (sumGlue s U χ W V y) < 0) := by
  by_cases hin : ∃ i ∈ s, y ∈ tsupport (χ i)
  · obtain ⟨i, hi, hyi⟩ := hin
    rw [sumGlue_eq_glue hdis hi hyi]
    obtain ⟨h1, h2⟩ := fderiv_glue_le (hχ0 i hi) (hχ1 i hi) (hsupp i hi) f (hW i hi) hV hy
    refine ⟨h1, ?_⟩
    rintro (⟨hno, -⟩ | ⟨j, hj, hyj, hcase⟩)
    · exact absurd hyi (hno i hi)
    · have hji : j = i := by
        by_contra hne
        exact Set.disjoint_left.mp (hdis j hj i hi hne) hyj hyi
      subst hji
      exact h2 hcase
  · have hno : ∀ i ∈ s, y ∉ tsupport (χ i) := fun i hi hyi => hin ⟨i, hi, hyi⟩
    rw [sumGlue_eq_of_not_mem hno]
    refine ⟨hV y hy, ?_⟩
    rintro (⟨-, hlt⟩ | ⟨i, hi, hyi, -⟩)
    · exact hlt
    · exact absurd hyi (hno i hi)

end

end Finsler.LevelGlue
