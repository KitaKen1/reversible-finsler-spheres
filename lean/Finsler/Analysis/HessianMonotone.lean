module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Strict monotonicity of a derivative along a segment from a positive second
derivative, and injectivity of the derivative of a nonnegative two-homogeneous
function whose Hessian is positive away from zero. The mean value theorem
replaces a convexity theory; segments through zero are handled by Euler's
identity instead of a second derivative at zero. -/

@[expose] public section

namespace Finsler.HessianMonotone

open Set

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Along a segment avoiding the singular point, a positive Hessian forces a
strictly positive increment of the derivative in the segment direction. -/
theorem derivative_increment_pos {e : V → ℝ} {v w : V} (hvw : v ≠ w)
    (hsmooth : ∀ s ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 e (w + s • (v - w)))
    (hseg : ∀ s ∈ Icc (0 : ℝ) 1, w + s • (v - w) ≠ 0)
    (hpos : ∀ z : V, z ≠ 0 → ∀ d : V, d ≠ 0 → 0 < fderiv ℝ (fderiv ℝ e) z d d) :
    0 < (fderiv ℝ e v - fderiv ℝ e w) (v - w) := by
  have hd0 : v - w ≠ 0 := sub_ne_zero.mpr hvw
  let γ : ℝ → V := fun s => w + s • (v - w)
  let g : ℝ → ℝ := fun s => fderiv ℝ e (γ s) (v - w)
  let g' : ℝ → ℝ := fun s => fderiv ℝ (fderiv ℝ e) (γ s) (v - w) (v - w)
  have hγ (s : ℝ) : HasDerivAt γ (v - w) s := by
    have h := ((hasDerivAt_id' s).smul_const (v - w)).const_add w
    rw [one_smul] at h
    exact h
  have hg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt g (g' s) s := by
    have hdiff : DifferentiableAt ℝ (fderiv ℝ e) (γ s) :=
      ((hsmooth s hs).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h1 : HasDerivAt (fun r => fderiv ℝ e (γ r)) (fderiv ℝ (fderiv ℝ e) (γ s) (v - w)) s :=
      hdiff.hasFDerivAt.comp_hasDerivAt s (hγ s)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ (v - w)).hasFDerivAt.comp_hasDerivAt s h1
    simpa only [Function.comp_def, ContinuousLinearMap.apply_apply] using h2
  have hcont : ContinuousOn g (Icc 0 1) := fun s hs =>
    (hg s hs).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope g g' zero_lt_one hcont
    (fun s hs => hg s (Ioo_subset_Icc_self hs))
  have hpos' : 0 < g' c := hpos (γ c) (hseg c (Ioo_subset_Icc_self hc)) (v - w) hd0
  have hg1 : g 1 = fderiv ℝ e v (v - w) := by
    simp only [g, γ, one_smul, add_sub_cancel]
  have hg0 : g 0 = fderiv ℝ e w (v - w) := by
    simp only [g, γ, zero_smul, add_zero]
  rw [hslope, hg1, hg0, sub_zero, div_one] at hpos'
  simpa only [sub_apply] using hpos'

/-- The derivative of a nonnegative two-homogeneous function with positive
Hessian away from zero is injective, including at the zero vector. -/
theorem eq_of_fderiv_eq {e : V → ℝ}
    (hsmooth : ∀ z : V, z ≠ 0 → ContDiffAt ℝ 2 e z)
    (hpos : ∀ z : V, z ≠ 0 → ∀ d : V, d ≠ 0 → 0 < fderiv ℝ (fderiv ℝ e) z d d)
    (heuler : ∀ z : V, fderiv ℝ e z z = 2 * e z)
    (hnonneg : ∀ z : V, 0 ≤ e z) (hzero : ∀ z : V, e z = 0 → z = 0)
    (hd0 : fderiv ℝ e 0 = 0) {v w : V} (h : fderiv ℝ e v = fderiv ℝ e w) : v = w := by
  by_contra hvw
  by_cases hseg : ∀ s ∈ Icc (0 : ℝ) 1, w + s • (v - w) ≠ 0
  · have hp := derivative_increment_pos hvw (fun s hs => hsmooth _ (hseg s hs)) hseg hpos
    rw [h, sub_self, zero_apply] at hp
    exact lt_irrefl _ hp
  · push Not at hseg
    obtain ⟨s, hs, hz⟩ := hseg
    have hv : fderiv ℝ e v v = 2 * e v := heuler v
    have hw : fderiv ℝ e v w = 2 * e w := by rw [h]; exact heuler w
    have hlin : (1 - s) * (2 * e w) + s * (2 * e v) = 0 := by
      have h0 := congrArg (fderiv ℝ e v) hz
      rw [map_add, map_smul, map_sub, map_zero, hv, hw, smul_eq_mul] at h0
      linarith
    have hew := hnonneg w
    have hev := hnonneg v
    have hs1 : (0 : ℝ) ≤ 1 - s := sub_nonneg.mpr hs.2
    have h1 : (1 - s) * e w = 0 := by nlinarith [mul_nonneg hs1 hew, mul_nonneg hs.1 hev]
    have h2 : s * e v = 0 := by nlinarith [mul_nonneg hs1 hew, mul_nonneg hs.1 hev]
    have hboth : v = 0 ∧ w = 0 := by
      rcases eq_or_lt_of_le hs.2 with hs_eq | hs_lt
      · -- the zero lies at v
        have hv0 : v = 0 := by
          rw [hs_eq, one_smul, add_sub_cancel] at hz
          exact hz
        have hp0 : fderiv ℝ e v = 0 := by rw [hv0]; exact hd0
        have hw0 : e w = 0 := by
          have := hw
          rw [hp0, zero_apply] at this
          linarith
        exact ⟨hv0, hzero w hw0⟩
      · have hw0 : w = 0 := hzero w (by
          rcases mul_eq_zero.mp h1 with h | h
          · linarith
          · exact h)
        have hp0 : fderiv ℝ e v = 0 := by rw [h, hw0]; exact hd0
        have hv0 : e v = 0 := by
          have := hv
          rw [hp0, zero_apply] at this
          linarith
        exact ⟨hzero v hv0, hw0⟩
    exact hvw (hboth.1.trans hboth.2.symm)

end Finsler.HessianMonotone
