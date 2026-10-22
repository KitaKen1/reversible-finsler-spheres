module

public import Finsler.Geometry.LabelData
public import Finsler.Analysis.InvariantThickening

/-! Invariant smooth root cutoffs satisfying the actual quantitative label estimates. -/

@[expose] public section
namespace Finsler.InvariantLabelChoice
open Set Metric Finsler.InvariantThickening Finsler.LevelGlue Finsler.LogCutoff
open scoped ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_invariant_label_choice (τ : E →L[ℝ] E) (hτ : ∀ x, τ (τ x) = x)
    (hiso : Isometry τ) {Γ : Set E} (hΓτ : ∀ x ∈ Γ, τ x ∈ Γ) (hΓ : IsCompact Γ) {δ R c C₁ : ℝ} (hδ : 0 < δ)
    (hR : 0 < R) (hc : 0 < c) (hC₁ : 0 ≤ C₁) (b p : ℕ) :
    ∃ (χ₀ : E → ℝ) (W₀ : Set E) (B M lam r κ' : ℝ),
      ContDiff ℝ ∞ χ₀ ∧ (∀ z, 0 ≤ χ₀ z ∧ χ₀ z ≤ 1) ∧ HasCompactSupport χ₀ ∧
      tsupport χ₀ ⊆ thickening δ Γ ∧ (∀ z, χ₀ (τ z) = χ₀ z) ∧
      (∀ z, τ z ∈ W₀ ↔ z ∈ W₀) ∧ IsOpen W₀ ∧ cthickening (δ / 2) Γ ⊆ W₀ ∧
      (∀ z ∈ W₀, χ₀ z = 1) ∧ 0 ≤ B ∧ (∀ z, ‖fderiv ℝ χ₀ z‖ ≤ B) ∧
      (∀ x, |deriv Real.smoothTransition x| ≤ M) ∧ 0 < lam ∧ 0 < r ∧
      r ^ 2 * Real.exp lam ≤ (R / 2) ^ 2 ∧ 0 < κ' ∧
      (C₁ + 1) * (B * κ' + 2 * M / lam) ≤ min (c / (b + p + 1)) 2 / 2 := by
  -- the cutoff
  have hT : IsCompact (cthickening (δ / 2) Γ) := hΓ.cthickening
  have hTU : cthickening (δ / 2) Γ ⊆ thickening δ Γ :=
    cthickening_subset_thickening' hδ (half_lt_self hδ) Γ
  obtain ⟨χ₀, W₀, hχ, hχ01, hχc, hχs, hχτ, hW₀, hTW, hWτ, hχ1⟩ :=
    Finsler.InvariantCutoff.exists_invariant_cutoff τ hτ hT isOpen_thickening hTU
      (fun x hx => (cthickening_invariant τ hτ hΓτ hiso (δ / 2) x).mpr hx)
      (fun x hx => (thickening_invariant τ hτ hΓτ hiso δ x).mpr hx)
  -- the bound of the derivative
  have hdc : HasCompactSupport (fderiv ℝ χ₀) := hχc.fderiv (𝕜 := ℝ)
  have hdcont : Continuous (fderiv ℝ χ₀) := hχ.continuous_fderiv (by simp)
  obtain ⟨B₀, hB₀⟩ := hdc.exists_bound_of_continuous hdcont
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ z, ‖fderiv ℝ χ₀ z‖ ≤ B := fun z => (hB₀ z).trans (le_max_left _ _)
  obtain ⟨M, hM0, hM⟩ := exists_deriv_bound
  -- the constant c*
  set cs : ℝ := min (c / (b + p + 1)) 2 with hcs
  have hcs0 : 0 < cs := lt_min (by positivity) two_pos
  -- λ with (C₁ + 1) 2M/λ ≤ c*/4
  set lam : ℝ := (C₁ + 1) * (8 * M + 1) / cs with hlamdef
  have hlam : 0 < lam := by positivity
  have hlam' : (C₁ + 1) * (2 * M / lam) ≤ cs / 4 := by
    have hC : 0 < C₁ + 1 := by linarith
    rw [hlamdef]
    have e : (C₁ + 1) * (2 * M / ((C₁ + 1) * (8 * M + 1) / cs)) = 2 * M * cs / (8 * M + 1) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    nlinarith
  -- r with r² e^λ = (R/2)² e^0 ... we take r = (R/2) e^{-λ/2}
  set r : ℝ := R / 2 * Real.exp (-(lam / 2)) with hrdef
  have hr : 0 < r := by positivity
  have hrR : r ^ 2 * Real.exp lam ≤ (R / 2) ^ 2 := by
    have e : r ^ 2 * Real.exp lam = (R / 2) ^ 2 := by
      rw [hrdef, mul_pow, ← Real.exp_nat_mul]
      rw [mul_assoc, ← Real.exp_add]
      norm_num
      rw [show -(2 * (lam / 2)) + lam = 0 by ring, Real.exp_zero, mul_one]
    rw [e]
  -- κ' with (C₁ + 1) B κ' ≤ c*/4
  set κ' : ℝ := cs / (4 * (C₁ + 1) * (B + 1)) with hκdef
  have hκ' : 0 < κ' := by positivity
  have hκB : (C₁ + 1) * (B * κ') ≤ cs / 4 := by
    have hC : 0 < C₁ + 1 := by linarith
    rw [hκdef]
    have e : (C₁ + 1) * (B * (cs / (4 * (C₁ + 1) * (B + 1)))) = cs / 4 * (B / (B + 1)) := by
      field_simp
    rw [e]
    have h1 : B / (B + 1) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have h2 : 0 ≤ cs / 4 := by positivity
    nlinarith
  refine ⟨χ₀, W₀, B, M, lam, r, κ', hχ, hχ01, hχc, hχs, hχτ, hWτ, hW₀, hTW, hχ1, hB0, hB, hM, hlam, hr, hrR,
    hκ', ?_⟩
  have e : (C₁ + 1) * (B * κ' + 2 * M / lam) = (C₁ + 1) * (B * κ') + (C₁ + 1) * (2 * M / lam) := by
    ring
  rw [e]
  linarith

end
end Finsler.InvariantLabelChoice
