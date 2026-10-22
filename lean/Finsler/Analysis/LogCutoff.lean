module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! A logarithmic cutoff and the deformation of a descent function. For r, λ > 0 the function

  Φ(q) = 1 - smoothTransition (log (q / r²) / λ)

is 1 for 0 ≤ q ≤ r², 0 for q ≥ r² e^λ, takes values in [0, 1], is smooth at every q > 0, and
q Φ'(q) is bounded by M / λ, where M bounds the derivative of the smooth transition. So for a
smooth nonnegative function q with |Dq(ξ)(v)| ≤ C q(ξ) the cutoff Φ ∘ q is smooth and its
derivative in the direction v is at most C M / λ, however far apart the radii r and r e^{λ/2}
are; this is what makes a cutoff in the normal directions compatible with a descent whose
decrease is only quadratic in the normal coordinates. If two functions Ψ and M decrease along a
field with derivatives at most A - c q, differ by at most C₁ q, and the derivative of a cutoff χ
with values in [0, 1] along the field is at most ε with C₁ ε ≤ c / 2, then Ψ + χ (M - Ψ)
decreases along the field with derivative at most A - (c / 2) q. -/

@[expose] public section

namespace Finsler.LogCutoff

open Set Filter
open scoped Topology ContDiff

noncomputable section

/-- The derivative of the smooth transition is bounded. -/
theorem exists_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |deriv Real.smoothTransition x| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact (hM x hx).trans (le_max_left _ _)
  · have h0 : deriv Real.smoothTransition x = 0 := by
      rcases not_and_or.mp hx with h | h
      · rw [not_le] at h
        have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds h] with y hy
          exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
        rw [he.deriv_eq, deriv_const]
      · rw [not_le] at h
        have he : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
          filter_upwards [Ioi_mem_nhds h] with y hy
          exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
        rw [he.deriv_eq, deriv_const]
    rw [h0, abs_zero]
    exact le_max_right _ _

/-- The logarithmic cutoff. -/
def logCut (r lam q : ℝ) : ℝ := 1 - Real.smoothTransition (Real.log (q / r ^ 2) / lam)

theorem logCut_nonneg (r lam q : ℝ) : 0 ≤ logCut r lam q :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

theorem logCut_le_one (r lam q : ℝ) : logCut r lam q ≤ 1 :=
  sub_le_self _ (Real.smoothTransition.nonneg _)

theorem logCut_of_le {r lam q : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) (hq : 0 ≤ q) (hqr : q ≤ r ^ 2) :
    logCut r lam q = 1 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have h1 : Real.log (q / r ^ 2) ≤ 0 :=
    Real.log_nonpos (div_nonneg hq hr2.le) ((div_le_one hr2).mpr hqr)
  unfold logCut
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg h1 hlam.le), sub_zero]

theorem logCut_of_ge {r lam q : ℝ} (hr : r ≠ 0) (hlam : 0 < lam)
    (hq : r ^ 2 * Real.exp lam ≤ q) : logCut r lam q = 0 := by
  have hr2 : 0 < r ^ 2 := by positivity
  have hq' : Real.exp lam ≤ q / r ^ 2 := by
    rw [le_div_iff₀ hr2]
    linarith [mul_comm (r ^ 2) (Real.exp lam)]
  have hqpos : 0 < q / r ^ 2 := lt_of_lt_of_le (Real.exp_pos _) hq'
  have h1 : lam ≤ Real.log (q / r ^ 2) := (Real.le_log_iff_exp_le hqpos).mpr hq'
  have h2 : 1 ≤ Real.log (q / r ^ 2) / lam := (one_le_div hlam).mpr h1
  unfold logCut
  rw [Real.smoothTransition.one_of_one_le h2, sub_self]

theorem logCut_contDiffAt {r lam q : ℝ} (hr : r ≠ 0) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (logCut r lam) q := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have h1 : ContDiffAt ℝ ∞ (fun q : ℝ => q / r ^ 2) q := contDiffAt_id.div_const _
  have h2 : ContDiffAt ℝ ∞ (fun q : ℝ => Real.log (q / r ^ 2)) q :=
    h1.log (div_ne_zero hq.ne' hr2)
  have h3 : ContDiffAt ℝ ∞ (fun q : ℝ => Real.log (q / r ^ 2) / lam) q := h2.div_const _
  exact contDiffAt_const.sub ((Real.smoothTransition.contDiff (n := ⊤)).contDiffAt.comp q h3)

theorem hasDerivAt_logCut {r lam q : ℝ} (hr : r ≠ 0) (hq : 0 < q) :
    HasDerivAt (logCut r lam)
      (-(deriv Real.smoothTransition (Real.log (q / r ^ 2) / lam) * (q⁻¹ / lam))) q := by
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  have h1 : HasDerivAt (fun q : ℝ => q / r ^ 2) (1 / r ^ 2) q := (hasDerivAt_id q).div_const _
  have h2 : HasDerivAt (fun q : ℝ => Real.log (q / r ^ 2)) (1 / r ^ 2 / (q / r ^ 2)) q :=
    h1.log (div_ne_zero hq.ne' hr2)
  have e : 1 / r ^ 2 / (q / r ^ 2) = q⁻¹ := by
    field_simp
  rw [e] at h2
  have h3 : HasDerivAt (fun q : ℝ => Real.log (q / r ^ 2) / lam) (q⁻¹ / lam) q := h2.div_const _
  have h4 := ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero
    (Real.log (q / r ^ 2) / lam)).hasDerivAt.comp q h3
  exact (hasDerivAt_const q (1 : ℝ)).sub h4 |>.congr_deriv (by ring)

/-- **The logarithmic bound.** q Φ'(q) is bounded by M / λ. -/
theorem abs_mul_deriv_le {r lam q M : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) (hq : 0 < q)
    (hM : ∀ x, |deriv Real.smoothTransition x| ≤ M) :
    |q * deriv (logCut r lam) q| ≤ M / lam := by
  rw [(hasDerivAt_logCut (lam := lam) hr hq).deriv]
  have e : q * -(deriv Real.smoothTransition (Real.log (q / r ^ 2) / lam) * (q⁻¹ / lam)) =
      -(deriv Real.smoothTransition (Real.log (q / r ^ 2) / lam) / lam) := by
    field_simp
  rw [e, abs_neg, abs_div, abs_of_pos hlam]
  exact div_le_div_of_nonneg_right (hM _) hlam.le

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The cutoff along a nonnegative smooth function is smooth. -/
theorem logCut_comp_contDiff {r lam : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) {q : X → ℝ}
    (hq : ContDiff ℝ ∞ q) (hq0 : ∀ ξ, 0 ≤ q ξ) : ContDiff ℝ ∞ fun ξ => logCut r lam (q ξ) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : q ξ < r ^ 2
  · have hU : IsOpen {ξ : X | q ξ < r ^ 2} := isOpen_lt hq.continuous continuous_const
    refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hU.mem_nhds hξ] with η hη
    exact logCut_of_le hr hlam (hq0 η) (le_of_lt hη)
  · have hpos : 0 < q ξ := lt_of_lt_of_le (by positivity) (not_lt.mp hξ)
    exact (logCut_contDiffAt hr hpos).comp ξ hq.contDiffAt

/-- **The derivative of the cutoff.** If |Dq(ξ)(v)| ≤ C q(ξ), the derivative of Φ ∘ q at ξ in
the direction v is at most C M / λ. -/
theorem abs_fderiv_logCut_comp_le {r lam C M : ℝ} (hr : r ≠ 0) (hlam : 0 < lam) (hC : 0 ≤ C)
    (hM : ∀ x, |deriv Real.smoothTransition x| ≤ M) {q : X → ℝ} (hq : ContDiff ℝ ∞ q)
    (hq0 : ∀ ξ, 0 ≤ q ξ) (ξ v : X) (hv : |fderiv ℝ q ξ v| ≤ C * q ξ) :
    |fderiv ℝ (fun ξ => logCut r lam (q ξ)) ξ v| ≤ C * M / lam := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  by_cases hξ : q ξ < r ^ 2
  · have hU : IsOpen {ξ : X | q ξ < r ^ 2} := isOpen_lt hq.continuous continuous_const
    have he : (fun ξ => logCut r lam (q ξ)) =ᶠ[𝓝 ξ] fun _ => (1 : ℝ) := by
      filter_upwards [hU.mem_nhds hξ] with η hη
      exact logCut_of_le hr hlam (hq0 η) (le_of_lt hη)
    have h0 : fderiv ℝ (fun _ : X => (1 : ℝ)) ξ = 0 := by simp
    rw [he.fderiv_eq, h0, zero_apply, abs_zero]
    positivity
  · have hpos : 0 < q ξ := lt_of_lt_of_le (by positivity) (not_lt.mp hξ)
    have hd : HasFDerivAt (fun ξ => logCut r lam (q ξ))
        ((deriv (logCut r lam) (q ξ)) • fderiv ℝ q ξ) ξ := by
      have h1 := (hasDerivAt_logCut (lam := lam) hr hpos)
      have h2 : HasFDerivAt q (fderiv ℝ q ξ) ξ :=
        (hq.differentiable (by simp) ξ).hasFDerivAt
      rw [h1.deriv]
      exact h1.comp_hasFDerivAt ξ h2
    rw [hd.fderiv, smul_apply, smul_eq_mul, abs_mul]
    have hb := abs_mul_deriv_le hr hlam hpos hM
    rw [abs_mul, abs_of_pos hpos] at hb
    have h3 : |deriv (logCut r lam) (q ξ)| ≤ M / lam / q ξ := by
      rw [le_div_iff₀ hpos]
      linarith [mul_comm (q ξ) |deriv (logCut r lam) (q ξ)|]
    calc |deriv (logCut r lam) (q ξ)| * |fderiv ℝ q ξ v|
        ≤ (M / lam / q ξ) * (C * q ξ) :=
          mul_le_mul h3 hv (abs_nonneg _) (by positivity)
      _ = C * M / lam := by field_simp

/-- **The deformation inequality.** -/
theorem deform_le {A c C₁ ε q χ dΨ dM dχ δ : ℝ} (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hΨ : dΨ ≤ A - c * q) (hM : dM ≤ A - c * q) (hδ : |δ| ≤ C₁ * q) (hdχ : |dχ| ≤ ε)
    (hCε : C₁ * ε ≤ c / 2) (hq : 0 ≤ q) :
    (1 - χ) * dΨ + χ * dM + δ * dχ ≤ A - c / 2 * q := by
  have h1 : (1 - χ) * dΨ + χ * dM ≤ A - c * q := by
    have e1 := mul_le_mul_of_nonneg_left hΨ (sub_nonneg.mpr hχ1)
    have e2 := mul_le_mul_of_nonneg_left hM hχ0
    nlinarith
  have h2 : δ * dχ ≤ c / 2 * q := by
    have e1 : δ * dχ ≤ |δ| * |dχ| := by
      rw [← abs_mul]
      exact le_abs_self _
    have e2 : |δ| * |dχ| ≤ C₁ * q * ε :=
      mul_le_mul hδ hdχ (abs_nonneg _) ((abs_nonneg _).trans hδ)
    have e3 : C₁ * q * ε ≤ c / 2 * q := by
      rw [mul_right_comm]
      exact mul_le_mul_of_nonneg_right hCε hq
    linarith
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of the deformed function Ψ + χ (M - Ψ). -/
theorem fderiv_deform {Ψ M χ : E → ℝ} {y : E} (hΨ : DifferentiableAt ℝ Ψ y)
    (hM : DifferentiableAt ℝ M y) (hχ : DifferentiableAt ℝ χ y) (v : E) :
    fderiv ℝ (fun y => Ψ y + χ y * (M y - Ψ y)) y v =
      (1 - χ y) * fderiv ℝ Ψ y v + χ y * fderiv ℝ M y v + (M y - Ψ y) * fderiv ℝ χ y v := by
  have h1 : HasFDerivAt (fun y => Ψ y + χ y * (M y - Ψ y))
      (fderiv ℝ Ψ y + (χ y • (fderiv ℝ M y - fderiv ℝ Ψ y) + (M y - Ψ y) • fderiv ℝ χ y)) y :=
    hΨ.hasFDerivAt.add (hχ.hasFDerivAt.mul (hM.hasFDerivAt.sub hΨ.hasFDerivAt))
  rw [h1.fderiv]
  simp only [add_apply, smul_apply, sub_apply, smul_eq_mul]
  ring

end

end Finsler.LogCutoff
