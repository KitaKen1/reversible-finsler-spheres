module

public import Finsler.Geometry.WeakEulerLagrange
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Algebra.Order.Floor.Ring

/-! An explicit residual test field converts the weak Euler equation into a
pointwise constrained ambient equation. This avoids periodizing local bump
functions and applying a distributional fundamental lemma. GeneralVariation
proves the reverse implication; comparison with coordinate geodesic equations
remains a separate open obligation. -/

@[expose] public section

namespace Finsler.PointwiseEuler

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops Finsler.Geodesics
open Finsler.SphereVariation Finsler.AmbientLagrangian Finsler.WeakEulerLagrange Function
open scoped Interval ContDiff RealInnerProductSpace

noncomputable section

/-- A continuous periodic field with zero squared-norm integral vanishes
at every real time, including times outside the integration interval. -/
theorem periodic_field_zero_of_integral_norm_sq_zero
    {E : Type*} [NormedAddCommGroup E] {w : ℝ → E}
    (hc : Continuous w) (hp : Periodic w 1)
    (hz : (∫ t in 0..1, ‖w t‖ ^ 2) = 0) : ∀ t, w t = 0 := by
  intro t
  by_contra ht
  let s : ℝ := t - (Int.floor t : ℝ)
  have hs0 : 0 ≤ s := sub_nonneg.mpr (Int.floor_le t)
  have hs1 : s ≤ 1 := by
    have h := Int.lt_floor_add_one t
    change t - (Int.floor t : ℝ) ≤ 1
    linarith
  have he : w s = w t := by
    simpa only [mul_one] using hp.sub_int_mul_eq (x := t) (Int.floor t)
  have hs : w s ≠ 0 := he ▸ ht
  have hi := intervalIntegral.integral_pos (by norm_num : (0 : ℝ) < 1)
    (hc.norm.pow 2).continuousOn (fun _ _ => sq_nonneg _)
    ⟨s, ⟨hs0, hs1⟩, sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hs)⟩
  change 0 < ∫ t in 0..1, ‖w t‖ ^ 2 at hi
  rw [hz] at hi
  exact lt_irrefl 0 hi

variable {n : ℕ} {γ : SmoothLoop n}

def representative (F : ReversibleMetric n) (γ : SmoothLoop n) (t : ℝ) : Ambient n :=
  (InnerProductSpace.toDual ℝ (Ambient n)).symm (residual F γ t)

theorem representative_smooth (F : ReversibleMetric n) (hreg : Regular γ) :
    ContDiff ℝ ∞ (representative F γ) :=
  (InnerProductSpace.toDual ℝ (Ambient n)).symm.toContinuousLinearEquiv.contDiff.comp
    (residual_smooth F hreg)

theorem representative_periodic (F : ReversibleMetric n) (hreg : Regular γ) :
    Periodic (representative F γ) 1 := fun t =>
  congrArg (InnerProductSpace.toDual ℝ (Ambient n)).symm (residual_periodic F hreg t)

/-- Choose the answer itself: the tangent projection of the Riesz residual. -/
def residualField (F : ReversibleMetric n) (hreg : Regular γ) : SmoothTangentField γ :=
  projectedField (representative F γ) (representative_smooth F hreg)
    (representative_periodic F hreg)

theorem residualField_decomposition (F : ReversibleMetric n) (hreg : Regular γ) (t : ℝ) :
    representative F γ t = (residualField F hreg).value t +
      ⟪(γ t : Ambient n), representative F γ t⟫ • (γ t : Ambient n) := by
  simp only [residualField, projectedField]
  abel

theorem residual_on_residualField (F : ReversibleMetric n) (hreg : Regular γ) (t : ℝ) :
    residual F γ t ((residualField F hreg).value t) = ‖(residualField F hreg).value t‖ ^ 2 := by
  rw [← InnerProductSpace.toDual_symm_apply]
  change ⟪representative F γ t, (residualField F hreg).value t⟫ = _
  rw [residualField_decomposition F hreg t, inner_add_left]
  simp only [inner_smul_left, conj_trivial,
    (residualField F hreg).tangent t, mul_zero, add_zero, real_inner_self_eq_norm_sq]

theorem stationary_residualField_zero (F : ReversibleMetric n) (hreg : Regular γ)
    (hstat : Stationary F γ) : ∀ t, (residualField F hreg).value t = 0 := by
  apply periodic_field_zero_of_integral_norm_sq_zero (residualField F hreg).smooth.continuous
    (residualField F hreg).periodic
  have h := stationary_residual_integral_zero F hreg hstat (residualField F hreg)
  simpa only [residual_on_residualField] using h

/-- The ambient Euler residual annihilates the actual sphere tangent directions. -/
def ConstrainedEuler (F : ReversibleMetric n) (γ : SmoothLoop n) : Prop :=
  ∀ t (v : Ambient n), ⟪(γ t : Ambient n), v⟫ = 0 → residual F γ t v = 0

theorem stationary_constrainedEuler (F : ReversibleMetric n) (hreg : Regular γ)
    (hstat : Stationary F γ) : ConstrainedEuler F γ := by
  intro t v hv
  have he := residualField_decomposition F hreg t
  rw [stationary_residualField_zero F hreg hstat t, zero_add] at he
  rw [← InnerProductSpace.toDual_symm_apply]
  change ⟪representative F γ t, v⟫ = 0
  rw [he, inner_smul_left, hv, mul_zero]

end

end Finsler.PointwiseEuler
