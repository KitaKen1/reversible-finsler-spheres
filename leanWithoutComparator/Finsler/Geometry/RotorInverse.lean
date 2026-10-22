module

public import Finsler.Geometry.NearbyRotor

/-! Exact inverse of the concrete equal-norm basepoint rotor. -/

@[expose] public section

namespace Finsler.RotorInverse

open Finsler.SphereGeometry Finsler.NearbyRotor
open scoped RealInnerProductSpace

noncomputable section
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem axis_natural_apply (A : Ambient n ≃ₗᵢ[ℝ] Ambient n) (u v : Ambient n) :
    axisReflection (A u) v = A (axisReflection u (A.symm v)) := by
  have hs : (ℝ ∙ u).map (A.toLinearEquiv : Ambient n →ₗ[ℝ] Ambient n) = ℝ ∙ A u := by
    rw [Submodule.map_span]
    simp
  have he := Submodule.reflection_map_apply A (ℝ ∙ u) v
  simpa only [axisReflection, hs] using he

theorem rotor_symm {x y : Ambient n} (h : ‖x‖ = ‖y‖) :
    (rotor x y).symm = rotor y x := by
  apply LinearIsometryEquiv.ext
  intro v
  have he := axis_natural_apply (axisReflection (x + y)) x v
  have hm : axisReflection (x + y) x = y := axis_sum_map h
  have hs : (axisReflection (x + y)).symm = axisReflection (x + y) :=
    Submodule.reflection_symm
  rw [hm, hs] at he
  change (axisReflection x).symm ((axisReflection (x + y)).symm v) =
    axisReflection (y + x) (axisReflection y v)
  rw [show (axisReflection x).symm = axisReflection x from Submodule.reflection_symm,
    hs, add_comm y x, he]
  exact (Submodule.reflection_reflection (ℝ ∙ (x + y)) _).symm

theorem rotor_cancel {x y : Ambient n} (h : ‖x‖ = ‖y‖) (v : Ambient n) :
    rotor y x (rotor x y v) = v := by
  rw [← rotor_symm h]
  exact (rotor x y).symm_apply_apply v


end
end Finsler.RotorInverse
