module

public import Finsler.Loop.RationalSphereArcCarrier

/-! Exact positive coordinates and time recovery on the ACTUAL
rational quarter arc. These identify self-coincidence loci before
the original Thom cap is evaluated. -/
@[expose] public section
namespace Finsler.RationalSphereArcCoordinates
open Finsler.SphereGeometry Finsler.RationalSphereCurve Finsler.RationalSphereArc
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def alpha (t : _root_.unitInterval) : ℝ := (1 - (t : ℝ)^2) / (1 + (t : ℝ)^2)
def beta (t : _root_.unitInterval) : ℝ := (2 * (t : ℝ)) / (1 + (t : ℝ)^2)

theorem coordinates {n : ℕ} (z : orthogonalPairs n) (t : _root_.unitInterval) :
    (point z t : Ambient n) = alpha t • (z.val.1 : Ambient n) + beta t • (z.val.2 : Ambient n) := by
  have hy := mem_sphere_zero_iff_norm.mp z.val.2.property
  change (1 + aFun (2 * (t : ℝ)) (z.val.2 : Ambient n))⁻¹ •
    ((1 - aFun (2 * (t : ℝ)) (z.val.2 : Ambient n)) • (z.val.1 : Ambient n) +
      (2 * (t : ℝ)) • (z.val.2 : Ambient n)) = _
  have ha : aFun (2 * (t : ℝ)) (z.val.2 : Ambient n) = (t : ℝ)^2 := by
    rw [aFun, hy, one_pow, mul_one]; ring
  rw [ha]
  simp only [alpha, beta, div_eq_mul_inv, smul_add, smul_smul]
  module

theorem alpha_nonneg (t : _root_.unitInterval) : 0 ≤ alpha t := by
  apply div_nonneg
  · nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)]
  · positivity

theorem alpha_pos (t : _root_.unitInterval) (ht : (t : ℝ) < 1) : 0 < alpha t := by
  apply div_pos
  · nlinarith [mul_pos (sub_pos.mpr ht) (show 0 < 1 + (t : ℝ) by linarith [t.property.1])]
  · positivity

theorem beta_nonneg (t : _root_.unitInterval) : 0 ≤ beta t :=
  div_nonneg (by linarith [t.property.1]) (by positivity)

theorem beta_pos (t : _root_.unitInterval) (ht : 0 < (t : ℝ)) : 0 < beta t :=
  div_pos (by linarith) (by positivity)

theorem alpha_zero_iff (t : _root_.unitInterval) : alpha t = 0 ↔ t = 1 := by
  rw [alpha, div_eq_zero_iff]
  have hd : 1 + (t : ℝ)^2 ≠ 0 := by positivity
  simp only [hd, or_false]
  constructor
  · intro h
    apply Subtype.ext
    change (t : ℝ) = 1
    nlinarith [t.property.1]
  · rintro rfl
    norm_num

theorem beta_zero_iff (t : _root_.unitInterval) : beta t = 0 ↔ t = 0 := by
  rw [beta, div_eq_zero_iff]
  have hd : 1 + (t : ℝ)^2 ≠ 0 := by positivity
  simp only [hd, or_false]
  constructor
  · intro h
    apply Subtype.ext
    change (t : ℝ) = 0
    linarith
  · rintro rfl
    norm_num

theorem time_relation (t : _root_.unitInterval) : beta t = (t : ℝ) * (1 + alpha t) := by
  unfold alpha beta
  have hd : 1 + (t : ℝ)^2 ≠ 0 := by positivity
  field_simp
  ring

theorem point_injective {n : ℕ} (z : orthogonalPairs n) : Function.Injective (point z) := by
  intro s t h
  have ha := congrArg (fun x : Sphere n => ⟪(z.val.1 : Ambient n), (x : Ambient n)⟫) h
  have hb := congrArg (fun x : Sphere n => ⟪(z.val.2 : Ambient n), (x : Ambient n)⟫) h
  rw [RationalSphereArcCarrier.inner_left, RationalSphereArcCarrier.inner_left] at ha
  rw [RationalSphereArcCarrier.inner_right, RationalSphereArcCarrier.inner_right] at hb
  change alpha s = alpha t at ha
  change beta s = beta t at hb
  have hc : (s : ℝ) * (1 + alpha t) = (t : ℝ) * (1 + alpha t) := by
    rw [← ha, ← time_relation, hb, time_relation, ha]
  apply Subtype.ext
  exact mul_right_cancel₀ (by linarith [alpha_nonneg t] : 1 + alpha t ≠ 0) hc

end
end Finsler.RationalSphereArcCoordinates
