module

public import Finsler.Geometry.SmallRotation

/-! Extend small orthogonal distortion to every tangent velocity, including zero. -/

@[expose] public section

namespace Finsler.SmallRotationGeneral

open Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientLagrangian
open Finsler.MetricComparison Finsler.SmallRotation
open scoped RealInnerProductSpace

noncomputable section
variable {n : ℕ}

theorem pointSpeed_zero (F : ReversibleMetric n) (x : Ambient n) :
    pointSpeed F (x, 0) = 0 := by
  simpa only [zero_smul, abs_zero, zero_mul] using
    pointSpeed_smul F x (0 : Ambient n) 0

theorem normalized_pair_unit {x v : Ambient n} (hx : ‖x‖ = 1)
    (hv : v ≠ 0) (hi : ⟪x, v⟫ = 0) :
    (x, ‖v‖⁻¹ • v) ∈ unitTangentPairs n := by
  refine ⟨hx, ?_, ?_⟩
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  · simp only [inner_smul_right, hi, mul_zero]

/-- The radius is uniform in both position and velocity, not selected per loop. -/
theorem exists_rotation_speed_control (F : ReversibleMetric n) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Ambient n ≃ₗᵢ[ℝ] Ambient n,
      ‖A.toContinuousLinearMap - ContinuousLinearMap.id ℝ (Ambient n)‖ < δ →
      ∀ x v : Ambient n, ‖x‖ = 1 → ⟪x, v⟫ = 0 →
        |pointSpeed F (A x, A v) - pointSpeed F (x, v)| ≤ ε * pointSpeed F (x, v) := by
  obtain ⟨δ, hδ, hd⟩ := exists_unit_rotation_control F hε
  refine ⟨δ, hδ, fun A hA x v hx hi => ?_⟩
  by_cases hv : v = 0
  · subst v
    simp only [map_zero, pointSpeed_zero, sub_self, abs_zero, mul_zero, le_refl]
  · have he := hd A hA (x, ‖v‖⁻¹ • v) (normalized_pair_unit hx hv hi)
    change |pointSpeed F (A x, A (‖v‖⁻¹ • v)) -
      pointSpeed F (x, ‖v‖⁻¹ • v)| ≤ ε * pointSpeed F (x, ‖v‖⁻¹ • v) at he
    rw [A.map_smul, pointSpeed_smul, pointSpeed_smul, ← mul_sub, abs_mul, abs_abs] at he
    have hp : 0 < |‖v‖⁻¹| := abs_pos.mpr (inv_ne_zero (norm_ne_zero_iff.mpr hv))
    apply (mul_le_mul_iff_left₀ hp).mp
    simpa only [mul_comm, mul_assoc, mul_left_comm] using he


end
end Finsler.SmallRotationGeneral
