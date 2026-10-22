module

public import TauCeti.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Taylor's formula with integral remainder, smoothly in a parameter. For a curve f with
continuous second derivative, f(s) − f(0) − s f'(0) = s² ∫₀¹ (1 − θ) f''(θs) dθ. For a C^(m+2)
map P(v,s) the remainder R(v,s) = ∫₀¹ (1 − θ) ∂²ₛP(v,θs) dθ is C^m (Tau Ceti's parametric
integral), so P(v,s) = P(v,0) + s ∂ₛP(v,0) + s² R(v,s). This is the device that makes the Finsler
exponential map C¹ at the zero section. -/

@[expose] public section

namespace Finsler.ParamTaylor

open Set MeasureTheory

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Taylor's formula with integral remainder for a curve. -/
theorem taylor_integral {f f' f'' : ℝ → W} (s : ℝ)
    (hf : ∀ σ, HasDerivAt f (f' σ) σ) (hf' : ∀ σ, HasDerivAt f' (f'' σ) σ)
    (hc : Continuous f'') :
    f s - f 0 - s • f' 0 = s ^ 2 • ∫ θ in (0 : ℝ)..1, (1 - θ) • f'' (θ * s) := by
  let φ : ℝ → W := fun θ => f (θ * s) + ((1 - θ) * s) • f' (θ * s)
  have hφ : ∀ θ, HasDerivAt φ (s ^ 2 • ((1 - θ) • f'' (θ * s))) θ := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => θ * s) s θ := by
      simpa using (hasDerivAt_id θ).mul_const s
    have hA := (hf (θ * s)).scomp θ h1
    have hB := (hf' (θ * s)).scomp θ h1
    have hc1 : HasDerivAt (fun θ : ℝ => (1 - θ) * s) (-s) θ := by
      simpa using ((hasDerivAt_id θ).const_sub 1).mul_const s
    have hC := hc1.smul hB
    have h := hA.add hC
    have h' : HasDerivAt φ (s • f' (θ * s) + (((1 - θ) * s) • s • f'' (θ * s) +
        -s • f' (θ * s))) θ := h
    convert h' using 1
    module
  have hcont : Continuous fun θ : ℝ => s ^ 2 • ((1 - θ) • f'' (θ * s)) :=
    continuous_const.smul ((continuous_const.sub continuous_id).smul
      (hc.comp (continuous_id.mul continuous_const)))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hφ θ)
    (hcont.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_smul] at hftc
  have h1 : φ 1 = f s := by simp [φ]
  have h0 : φ 0 = f 0 + s • f' 0 := by simp [φ]
  rw [hftc, h1, h0]
  abel

section Param

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The time derivative of a map on V × ℝ. -/
def timeDeriv (P : V × ℝ → W) (q : V × ℝ) : W := fderiv ℝ P q (0, 1)

omit [CompleteSpace W] in
theorem hasDerivAt_time {P : V × ℝ → W} (v : V) {σ : ℝ} (hP : DifferentiableAt ℝ P (v, σ)) :
    HasDerivAt (fun s => P (v, s)) (timeDeriv P (v, σ)) σ := by
  have h1 : HasDerivAt (fun s : ℝ => (v, s)) ((0 : V), (1 : ℝ)) σ :=
    (hasDerivAt_const σ v).prodMk (hasDerivAt_id σ)
  exact hP.hasFDerivAt.comp_hasDerivAt σ h1

/-- Taylor's formula with a C^m integral remainder, smoothly in the parameter. -/
theorem exists_smooth_remainder {P : V × ℝ → W} {m : ℕ} (hP : ContDiff ℝ (m + 2) P) :
    ∃ R : V × ℝ → W, ContDiff ℝ m R ∧ ∀ v s,
      P (v, s) = P (v, 0) + s • timeDeriv P (v, 0) + s ^ 2 • R (v, s) := by
  have hD1 : ContDiff ℝ (m + 1) (timeDeriv P) := by
    have h := hP.fderiv_right (m := m + 1) (by norm_cast)
    exact h.clm_apply contDiff_const
  have hD2 : ContDiff ℝ m (timeDeriv (timeDeriv P)) := by
    have h := hD1.fderiv_right (m := m) (by norm_cast)
    exact h.clm_apply contDiff_const
  let h : V × ℝ → ℝ → W := fun q θ => (1 - θ) • timeDeriv (timeDeriv P) (q.1, θ * q.2)
  have hh : ContDiff ℝ (m : ℕ∞) h.uncurry := by
    have h1 : ContDiff ℝ m (fun x : (V × ℝ) × ℝ => (x.1.1, x.2 * x.1.2)) :=
      (contDiff_fst.comp contDiff_fst).prodMk (contDiff_snd.mul (contDiff_snd.comp contDiff_fst))
    exact (contDiff_const.sub contDiff_snd).smul (hD2.comp h1)
  refine ⟨fun q => ∫ θ in Icc (0 : ℝ) 1, h q θ,
    contDiff_integral_Icc_of_contDiff (m : ℕ∞) h hh, fun v s => ?_⟩
  have hdiffP : ∀ σ, DifferentiableAt ℝ P (v, σ) :=
    fun σ => (hP.differentiable (by norm_cast)) _
  have hdiffD : ∀ σ, DifferentiableAt ℝ (timeDeriv P) (v, σ) :=
    fun σ => (hD1.differentiable (by norm_cast)) _
  have ht := taylor_integral (f := fun σ => P (v, σ)) (f' := fun σ => timeDeriv P (v, σ))
    (f'' := fun σ => timeDeriv (timeDeriv P) (v, σ)) s
    (fun σ => hasDerivAt_time v (hdiffP σ)) (fun σ => hasDerivAt_time v (hdiffD σ))
    (hD2.continuous.comp (continuous_const.prodMk continuous_id))
  have hint : (∫ θ in (0 : ℝ)..1, (1 - θ) • timeDeriv (timeDeriv P) (v, θ * s)) =
      ∫ θ in Icc (0 : ℝ) 1, h (v, s) θ := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rw [hint] at ht
  rw [← ht]
  abel

end Param

end

end Finsler.ParamTaylor
