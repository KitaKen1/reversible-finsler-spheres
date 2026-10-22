module

public import Finsler.Loop.MeridianLoopFamily

/-! Exact four-quarter formulas for the ORIGINAL based meridian loop.
Use path extension so that both sides of each seam are covered by
the same inclusive path-concatenation lemmas. -/

@[expose] public section
namespace Finsler.MeridianLoopQuarterPaths
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.RationalSphereArc
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem first {n : ℕ} (P : Sphere n) (v₀ v : equator P) (t : _root_.unitInterval) :
    (loop P v₀ v).extend ((t : ℝ) / 4) = arc (outgoing P v) t := by
  rw [loop, Path.extend_trans_of_le_half _ _ (by linarith [t.property.2])]
  rw [meridian, Path.extend_trans_of_le_half _ _ (by linarith [t.property.2])]
  rw [show 2 * (2 * ((t : ℝ) / 4)) = (t : ℝ) by ring]
  exact Path.extend_apply _ t.property

theorem second {n : ℕ} (P : Sphere n) (v₀ v : equator P) (t : _root_.unitInterval) :
    (loop P v₀ v).extend ((1 + (t : ℝ)) / 4) = arc (incoming P v) t := by
  rw [loop, Path.extend_trans_of_le_half _ _ (by linarith [t.property.2])]
  rw [meridian, Path.extend_trans_of_half_le _ _ (by linarith [t.property.1])]
  rw [show 2 * (2 * ((1 + (t : ℝ)) / 4)) - 1 = (t : ℝ) by ring]
  exact Path.extend_apply _ t.property

theorem third {n : ℕ} (P : Sphere n) (v₀ v : equator P) (t : _root_.unitInterval) :
    (loop P v₀ v).extend ((2 + (t : ℝ)) / 4) = (arc (incoming P v₀)).symm t := by
  rw [loop, Path.extend_trans_of_half_le _ _ (by linarith [t.property.1])]
  rw [meridian, Path.trans_symm,
    Path.extend_trans_of_le_half _ _ (by linarith [t.property.2])]
  rw [show 2 * (2 * ((2 + (t : ℝ)) / 4) - 1) = (t : ℝ) by ring]
  exact Path.extend_apply _ t.property

theorem fourth {n : ℕ} (P : Sphere n) (v₀ v : equator P) (t : _root_.unitInterval) :
    (loop P v₀ v).extend ((3 + (t : ℝ)) / 4) = (arc (outgoing P v₀)).symm t := by
  rw [loop, Path.extend_trans_of_half_le _ _ (by linarith [t.property.1])]
  rw [meridian, Path.trans_symm,
    Path.extend_trans_of_half_le _ _ (by linarith [t.property.1])]
  rw [show 2 * (2 * ((3 + (t : ℝ)) / 4) - 1) - 1 = (t : ℝ) by ring]
  exact Path.extend_apply _ t.property

end
end Finsler.MeridianLoopQuarterPaths
