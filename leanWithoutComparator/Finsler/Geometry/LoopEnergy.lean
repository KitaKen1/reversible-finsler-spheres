module

public import Finsler.Definitions.Loop
public import Finsler.Definitions.Metric
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual velocity and integral energy of smooth loops. The energy is
integral F², matching the paper's normalization, rather than half that integral.
These statements do not yet address Sobolev loops or the H¹ topology. -/

@[expose] public section

namespace Finsler.LoopEnergy

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops TauCeti.Manifold Function
open scoped Manifold ContDiff Interval

noncomputable section

variable {n : ℕ}

def velocityLift (γ : ℝ → Sphere n) (t : ℝ) : Total n :=
  curveVelocityLift (𝓡 n) γ t

def density (F : ReversibleMetric n) (γ : ℝ → Sphere n) (t : ℝ) : ℝ :=
  F.value (velocityLift γ t) ^ 2

def energy (F : ReversibleMetric n) (γ : SmoothLoop n) : ℝ := ∫ t in 0..1, density F γ t

theorem energy_nonneg (F : ReversibleMetric n) (γ : SmoothLoop n) : 0 ≤ energy F γ :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ => sq_nonneg _)

theorem velocityLift_continuous (γ : SmoothLoop n) : Continuous (velocityLift γ) :=
  TauCeti.Manifold.ContMDiff.continuous_curveVelocityLift (γ.smooth.of_le (by simp))

theorem density_continuous (F : ReversibleMetric n) (γ : SmoothLoop n) :
    Continuous (density F γ) :=
  (F.continuous.comp (velocityLift_continuous γ)).pow 2

theorem density_intervalIntegrable (F : ReversibleMetric n) (γ : SmoothLoop n) (a b : ℝ) :
    IntervalIntegrable (density F γ) MeasureTheory.volume a b :=
  (density_continuous F γ).intervalIntegrable a b

theorem velocityLift_comp (γ : ℝ → Sphere n) {φ : ℝ → ℝ} {c t : ℝ}
    (hφ : HasDerivAt φ c t) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ (φ t)) :
    velocityLift (γ ∘ φ) t = ⟨γ (φ t), c • curveVelocity (𝓡 n) γ (φ t)⟩ := by
  simp only [velocityLift, curveVelocityLift_apply, curveVelocity_comp hφ hγ, comp_apply]

theorem density_comp (F : ReversibleMetric n) (γ : ℝ → Sphere n) {φ : ℝ → ℝ} {c t : ℝ}
    (hφ : HasDerivAt φ c t) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) γ (φ t)) :
    density F (γ ∘ φ) t = c ^ 2 * density F γ (φ t) := by
  rw [density, velocityLift_comp γ hφ hγ, value_smul]
  simp [density, velocityLift, curveVelocityLift_apply, mul_pow]

theorem density_periodic (F : ReversibleMetric n) (γ : SmoothLoop n) :
    Periodic (density F γ) 1 := by
  have he : (γ ∘ fun t : ℝ => t + 1) = (γ : ℝ → Sphere n) := funext γ.periodic
  intro t
  have h := density_comp F γ ((hasDerivAt_id t).add_const 1)
    (γ.smooth.mdifferentiableAt (by simp))
  simpa only [id_eq, he, one_pow, one_mul] using h.symm

theorem density_shift (F : ReversibleMetric n) (γ : SmoothLoop n) (a t : ℝ) :
    density F (shift γ a) t = density F γ (t + a) := by
  have h := density_comp F γ ((hasDerivAt_id t).add_const a)
    (γ.smooth.mdifferentiableAt (by simp))
  simpa only [id_eq, one_pow, one_mul, shift, comp_def] using h

theorem density_reverse (F : ReversibleMetric n) (γ : SmoothLoop n) (t : ℝ) :
    density F (reverse γ) t = density F γ (-t) := by
  have h := density_comp F γ (hasDerivAt_id t).neg
    (γ.smooth.mdifferentiableAt (by simp))
  simpa only [id_eq, Pi.neg_apply, neg_one_sq, one_mul, reverse, comp_def] using h

theorem density_iterate (F : ReversibleMetric n) (γ : SmoothLoop n) (k : ℕ) (t : ℝ) :
    density F (iterate γ k) t = (k : ℝ) ^ 2 * density F γ ((k : ℝ) * t) := by
  have h := density_comp F γ ((hasDerivAt_id t).const_mul (k : ℝ))
    (γ.smooth.mdifferentiableAt (by simp))
  simpa only [id_eq, mul_one, iterate, comp_def] using h

theorem density_constant (F : ReversibleMetric n) (x : Sphere n) (t : ℝ) :
    density F (constant x) t = 0 := by
  simp [density, velocityLift, constant, curveVelocityLift_apply, F.zero]

theorem energy_constant (F : ReversibleMetric n) (x : Sphere n) : energy F (constant x) = 0 := by
  simp [energy, density_constant]

theorem energy_shift (F : ReversibleMetric n) (γ : SmoothLoop n) (a : ℝ) :
    energy F (shift γ a) = energy F γ := by
  simp only [energy, density_shift]
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_zero, add_comm] using
    (density_periodic F γ).intervalIntegral_add_eq a 0

theorem energy_reverse (F : ReversibleMetric n) (γ : SmoothLoop n) :
    energy F (reverse γ) = energy F γ := by
  simp only [energy, density_reverse]
  rw [intervalIntegral.integral_comp_neg]
  simpa using (density_periodic F γ).intervalIntegral_add_eq (-1) 0

theorem energy_iterate (F : ReversibleMetric n) (γ : SmoothLoop n) (k : ℕ) :
    energy F (iterate γ k) = (k : ℝ) ^ 2 * energy F γ := by
  by_cases hk : k = 0
  · subst k
    simp [Loops.iterate_zero, energy_constant]
  have hI : (∫ t in (0 : ℝ)..(k : ℝ), density F γ t) = (k : ℝ) * energy F γ := by
    simpa [energy, smul_eq_mul] using
      (density_periodic F γ).intervalIntegral_add_zsmul_eq (k : ℤ) 0
        (density_intervalIntegrable F γ)
  simp only [energy, density_iterate]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ (Nat.cast_ne_zero.mpr hk)]
  simp only [mul_zero, mul_one, smul_eq_mul]
  rw [hI]
  field_simp
  rfl

theorem energy_double (F : ReversibleMetric n) (γ : SmoothLoop n) :
    energy F (iterate γ 2) = 4 * energy F γ := by
  have h := energy_iterate F γ 2
  norm_num at h
  exact h

end

end Finsler.LoopEnergy
