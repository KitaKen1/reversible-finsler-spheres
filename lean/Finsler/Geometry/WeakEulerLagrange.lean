module

public import Finsler.Geometry.AmbientLagrangian
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Periodic integration by parts for the actual ambient Lagrangian.
Stationarity implies that its Euler residual annihilates every smooth periodic
tangent test field in the integral sense. The pointwise implication is proved
in PointwiseEuler; identification with ordinary geodesics remains open. -/

@[expose] public section

namespace Finsler.WeakEulerLagrange

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.SphereVariation Finsler.AmbientLagrangian Function
open scoped Interval ContDiff RealInnerProductSpace

noncomputable section

/-- The genuine derivative of a periodic covector--vector pairing integrates
 to zero. Smoothness and periodicity are actual properties of both maps. -/
theorem periodic_covector_derivative_integral_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E →L[ℝ] ℝ} {v : ℝ → E}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hup : Periodic u 1) (hvp : Periodic v 1) :
    (∫ t in 0..1, deriv u t (v t) + u t (deriv v t)) = 0 := by
  have hi := (((hu.continuous_deriv (by simp)).clm_apply hv.continuous).add
    (hu.continuous.clm_apply (hv.continuous_deriv (by simp)))).intervalIntegrable
      (μ := MeasureTheory.volume) 0 1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => ((hu.differentiable (by simp) t).hasDerivAt).clm_apply
      ((hv.differentiable (by simp) t).hasDerivAt)) hi
  have hu1 : u 1 = u 0 := by simpa only [zero_add] using hup 0
  have hv1 : v 1 = v 0 := by simpa only [zero_add] using hvp 0
  simpa only [hu1, hv1, sub_self] using h

variable {n : ℕ} {γ : SmoothLoop n}

def momentum (F : ReversibleMetric n) (γ : SmoothLoop n) (t : ℝ) : Ambient n →L[ℝ] ℝ :=
  velocityDifferential F (loopJet γ t)

def positionTerm (F : ReversibleMetric n) (γ : SmoothLoop n) (t : ℝ) : Ambient n →L[ℝ] ℝ :=
  positionDifferential F (loopJet γ t)

/-- Sign convention: D_q L - d/dt D_v L. -/
def residual (F : ReversibleMetric n) (γ : SmoothLoop n) (t : ℝ) : Ambient n →L[ℝ] ℝ :=
  positionTerm F γ t - deriv (momentum F γ) t

theorem momentum_smooth (F : ReversibleMetric n) (hreg : Regular γ) :
    ContDiff ℝ ∞ (momentum F γ) := velocityDifferential_loopJet_smooth F hreg

theorem positionTerm_smooth (F : ReversibleMetric n) (hreg : Regular γ) :
    ContDiff ℝ ∞ (positionTerm F γ) := positionDifferential_loopJet_smooth F hreg

theorem momentum_periodic (F : ReversibleMetric n) (γ : SmoothLoop n) :
    Periodic (momentum F γ) 1 := fun t => congrArg (velocityDifferential F) (loopJet_periodic γ t)

theorem periodic_deriv_of_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℝ → E} (hu : ContDiff ℝ ∞ u) (hp : Periodic u 1) : Periodic (deriv u) 1 := by
  have he : (fun t => u (t + 1)) = u := funext hp
  intro t
  have h := ((hu.differentiable (by simp) (t + 1)).hasDerivAt).scomp t
    ((hasDerivAt_id t).add_const 1)
  simpa only [Function.comp_def, id_eq, he, mul_one, one_smul] using h.deriv.symm

theorem residual_smooth (F : ReversibleMetric n) (hreg : Regular γ) :
    ContDiff ℝ ∞ (residual F γ) :=
  (positionTerm_smooth F hreg).sub (contDiff_infty_iff_deriv.mp (momentum_smooth F hreg)).2

theorem residual_periodic (F : ReversibleMetric n) (hreg : Regular γ) :
    Periodic (residual F γ) 1 := by
  have hQ := periodic_deriv_of_smooth (momentum_smooth F hreg) (momentum_periodic F γ)
  intro t
  simp only [residual, positionTerm, loopJet_periodic γ t, hQ t]

theorem firstVariation_residual (F : ReversibleMetric n) (hreg : Regular γ)
    (η : SmoothTangentField γ) :
    Finsler.FirstVariation.firstVariation F (variation η) 0 =
      ∫ t in 0..1, residual F γ t (η.value t) := by
  have hP := positionTerm_smooth F hreg
  have hQ := momentum_smooth F hreg
  have hQ' := hQ.continuous_deriv (by simp)
  have hη' := η.smooth.continuous_deriv (by simp)
  have hiR := ((hP.continuous.sub hQ').clm_apply η.smooth.continuous).intervalIntegrable
    (μ := MeasureTheory.volume) 0 1
  have hiD := ((hQ'.clm_apply η.smooth.continuous).add
    (hQ.continuous.clm_apply hη')).intervalIntegrable (μ := MeasureTheory.volume) 0 1
  have hz := periodic_covector_derivative_integral_zero hQ η.smooth
    (momentum_periodic F γ) η.periodic
  calc
    Finsler.FirstVariation.firstVariation F (variation η) 0 =
        ∫ t in 0..1, positionTerm F γ t (η.value t) + momentum F γ t (deriv η.value t) :=
      firstVariation_loopJet F hreg η
    _ = (∫ t in 0..1, residual F γ t (η.value t)) +
        (∫ t in 0..1, deriv (momentum F γ) t (η.value t) +
          momentum F γ t (deriv η.value t)) := by
      rw [← intervalIntegral.integral_add
        (f := fun t => residual F γ t (η.value t))
        (g := fun t => deriv (momentum F γ) t (η.value t) +
          momentum F γ t (deriv η.value t)) hiR hiD]
      apply intervalIntegral.integral_congr
      intro t _
      simp only [residual, sub_apply]
      ring
    _ = ∫ t in 0..1, residual F γ t (η.value t) := by rw [hz, add_zero]

theorem stationary_residual_integral_zero (F : ReversibleMetric n) (hreg : Regular γ)
    (hstat : Stationary F γ) (η : SmoothTangentField γ) :
    (∫ t in 0..1, residual F γ t (η.value t)) = 0 := by
  rw [← firstVariation_residual F hreg η]
  exact stationary_explicit_firstVariation_zero F hreg hstat η

theorem stationary_projected_residual_integral_zero (F : ReversibleMetric n)
    (hreg : Regular γ) (hstat : Stationary F γ) (h : ℝ → Ambient n)
    (hs : ContDiff ℝ ∞ h) (hp : Periodic h 1) :
    (∫ t in 0..1, residual F γ t
      (h t - ⟪(γ t : Ambient n), h t⟫ • (γ t : Ambient n))) = 0 :=
  stationary_residual_integral_zero F hreg hstat (projectedField h hs hp)

end

end Finsler.WeakEulerLagrange
