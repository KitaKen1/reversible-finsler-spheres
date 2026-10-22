module

public import Finsler.Analysis.PseudoGradient

/-! Gluing descent fields with a cutoff. Let f be a function on a finite dimensional real
normed space which is differentiable on an open set O, let χ be a smooth function with values
in [0, 1] whose closed support lies in an open set U ⊆ O, let W be a field which is smooth on U,
and let V be a smooth field supported in O. The field χ W, extended by zero outside U, is
smooth, and so is the glued field χ W + (1 - χ) V. Where χ = 1 it is W, where χ = 0 it is V,
and the derivative of f in its direction is the convex combination of the derivatives in the
directions of W and of V; in particular it is nonpositive where both are, and negative where
one of them is negative with positive weight and the other is nonpositive. -/

@[expose] public section

namespace Finsler.GlueField

open Set Filter
open scoped Topology ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
/-- The field χ W extended by zero outside U. -/
def cutField (U : Set E) (χ : E → ℝ) (W : E → E) (y : E) : E :=
  if y ∈ U then χ y • W y else 0

theorem cutField_of_mem {U : Set E} {χ : E → ℝ} {W : E → E} {y : E} (hy : y ∈ U) :
    cutField U χ W y = χ y • W y := by
  classical
  exact ite_eq_left hy

theorem cutField_of_not_mem_tsupport {U : Set E} {χ : E → ℝ} {W : E → E} {y : E}
    (hy : y ∉ tsupport χ) : cutField U χ W y = 0 := by
  classical
  unfold cutField
  split_ifs
  · rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  · rfl

/-- The cut field is smooth if the closed support of χ lies in the open set U on which W is
smooth. -/
theorem cutField_contDiff {U : Set E} (hU : IsOpen U) {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ U) {W : E → E} (hW : ContDiffOn ℝ ∞ W U) :
    ContDiff ℝ ∞ (cutField U χ W) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ U
  · have h1 : ContDiffAt ℝ ∞ (fun x => χ x • W x) y :=
      hχ.contDiffAt.smul (hW.contDiffAt (hU.mem_nhds hy))
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hy] with x hx
    exact cutField_of_mem hx
  · have hy' : y ∉ tsupport χ := fun h => hy (hsupp h)
    have h0 : ∀ᶠ x in 𝓝 y, x ∉ tsupport χ :=
      (isClosed_tsupport χ).isOpen_compl.mem_nhds hy'
    refine (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with x hx
    exact cutField_of_not_mem_tsupport hx

/-- The glued field. -/
def glue (U : Set E) (χ : E → ℝ) (W V : E → E) (y : E) : E :=
  cutField U χ W y + (1 - χ y) • V y

theorem glue_contDiff {U : Set E} (hU : IsOpen U) {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ U) {W : E → E} (hW : ContDiffOn ℝ ∞ W U) {V : E → E}
    (hV : ContDiff ℝ ∞ V) : ContDiff ℝ ∞ (glue U χ W V) :=
  (cutField_contDiff hU hχ hsupp hW).add ((contDiff_const.sub hχ).smul hV)

theorem glue_of_eq_one {U : Set E} {χ : E → ℝ} (hsupp : tsupport χ ⊆ U) {W V : E → E} {y : E}
    (hy : χ y = 1) : glue U χ W V y = W y := by
  have hyU : y ∈ U := hsupp (subset_tsupport χ (by rw [Function.mem_support, hy]; exact one_ne_zero))
  unfold glue
  rw [cutField_of_mem hyU, hy, one_smul, sub_self, zero_smul, add_zero]

theorem glue_of_not_mem_tsupport {U : Set E} {χ : E → ℝ} {W V : E → E} {y : E}
    (hy : y ∉ tsupport χ) : glue U χ W V y = V y := by
  unfold glue
  rw [cutField_of_not_mem_tsupport hy, image_eq_zero_of_notMem_tsupport hy, sub_zero, one_smul,
    zero_add]

/-- The derivative of a function in the direction of the glued field is the convex combination
of the derivatives in the directions of the two fields (inside U) or the derivative in the
direction of the second field (outside the support of χ). -/
theorem fderiv_glue {U : Set E} {χ : E → ℝ} {W V : E → E} (f : E → ℝ) {y : E} (hy : y ∈ U) :
    fderiv ℝ f y (glue U χ W V y) =
      χ y * fderiv ℝ f y (W y) + (1 - χ y) * fderiv ℝ f y (V y) := by
  unfold glue
  rw [cutField_of_mem hy, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **Descent of the glued field.** If χ takes values in [0, 1], the derivative of f in the
direction of W is nonpositive on U ∩ tsupport χ and in the direction of V on O, then the
derivative in the direction of the glued field is nonpositive on O; it is negative at a point
where, in addition, the derivative in the direction of V is negative and χ < 1, or the
derivative in the direction of W is negative and χ > 0. -/
theorem fderiv_glue_le {U O : Set E} {χ : E → ℝ} (hχ0 : ∀ y, 0 ≤ χ y)
    (hχ1 : ∀ y, χ y ≤ 1) (hsupp : tsupport χ ⊆ U) {W V : E → E} (f : E → ℝ)
    (hW : ∀ y ∈ tsupport χ, fderiv ℝ f y (W y) ≤ 0) (hV : ∀ y ∈ O, fderiv ℝ f y (V y) ≤ 0)
    {y : E} (hy : y ∈ O) :
    fderiv ℝ f y (glue U χ W V y) ≤ 0 ∧
      ((fderiv ℝ f y (V y) < 0 ∧ χ y < 1) ∨ (fderiv ℝ f y (W y) < 0 ∧ 0 < χ y ∧ y ∈ U) →
        fderiv ℝ f y (glue U χ W V y) < 0) := by
  by_cases hyt : y ∈ tsupport χ
  · have hyU := hsupp hyt
    rw [fderiv_glue f hyU]
    have h1 := hW y hyt
    have h2 := hV y hy
    have h3 := hχ0 y
    have h4 := hχ1 y
    refine ⟨by nlinarith, ?_⟩
    rintro (⟨h5, h6⟩ | ⟨h5, h6, -⟩)
    · nlinarith
    · nlinarith
  · rw [glue_of_not_mem_tsupport hyt]
    have hχy : χ y = 0 := image_eq_zero_of_notMem_tsupport hyt
    refine ⟨hV y hy, ?_⟩
    rintro (⟨h5, -⟩ | ⟨-, h6, -⟩)
    · exact h5
    · rw [hχy] at h6
      exact absurd h6 (lt_irrefl 0)

/-- The glued field vanishes outside O if V does and the support of χ lies in U ⊆ O. -/
theorem glue_eq_zero {U O : Set E} (hUO : U ⊆ O) {χ : E → ℝ} (hsupp : tsupport χ ⊆ U)
    {W V : E → E} (hVO : ∀ y, V y ≠ 0 → y ∈ O) {y : E} (hy : glue U χ W V y ≠ 0) : y ∈ O := by
  by_cases hyt : y ∈ tsupport χ
  · exact hUO (hsupp hyt)
  · rw [glue_of_not_mem_tsupport hyt] at hy
    exact hVO y hy

/-- The glued field has compact support if χ and V do. -/
theorem glue_hasCompactSupport {U : Set E} {χ : E → ℝ} (hχc : HasCompactSupport χ)
    {W V : E → E} (hVc : HasCompactSupport V) : HasCompactSupport (glue U χ W V) := by
  have h1 : HasCompactSupport (cutField U χ W) := by
    refine hχc.mono' ?_
    intro y hy
    by_contra h
    exact hy (cutField_of_not_mem_tsupport h)
  have h2 : HasCompactSupport (fun y => (1 - χ y) • V y) :=
    hVc.smul_left (f := fun y => 1 - χ y)
  exact h1.add h2

end

end Finsler.GlueField
