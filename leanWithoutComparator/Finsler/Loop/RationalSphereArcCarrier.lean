module

public import Finsler.Loop.RationalSphereArc

/-! Actual hemisphere/pole-avoidance control for the rational
quarter-meridians. These are the concrete carrier estimates needed
to compute their sphere sweep by the antipodal Mayer-Vietoris cover. -/

@[expose] public section
namespace Finsler.RationalSphereArcCarrier
open Finsler.SphereGeometry Finsler.RationalSphereCurve Finsler.RationalSphereArc
open scoped RealInnerProductSpace
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem inner_left {n : ℕ} (z : orthogonalPairs n) (t : _root_.unitInterval) :
    ⟪(z.val.1 : Ambient n), (point z t : Ambient n)⟫ =
      (1 - (t : ℝ) ^ 2) / (1 + (t : ℝ) ^ 2) := by
  have hx := mem_sphere_zero_iff_norm.mp z.val.1.property
  have hy := mem_sphere_zero_iff_norm.mp z.val.2.property
  change ⟪(z.val.1 : Ambient n), ratMap (2 * (t : ℝ)) ((z.val.1 : Ambient n), (z.val.2 : Ambient n))⟫ = _
  simp only [ratMap, real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq,
    hx, one_pow, z.property, mul_zero, add_zero, mul_one]
  simp only [aFun, hy, one_pow, mul_one]
  rw [show (2 * (t : ℝ)) ^ 2 / 4 = (t : ℝ) ^ 2 by ring]
  simp only [div_eq_mul_inv]
  ring

theorem inner_right {n : ℕ} (z : orthogonalPairs n) (t : _root_.unitInterval) :
    ⟪(z.val.2 : Ambient n), (point z t : Ambient n)⟫ =
      (2 * (t : ℝ)) / (1 + (t : ℝ) ^ 2) := by
  have hy := mem_sphere_zero_iff_norm.mp z.val.2.property
  have hz : ⟪(z.val.2 : Ambient n), (z.val.1 : Ambient n)⟫ = 0 :=
    (real_inner_comm _ _).trans z.property
  change ⟪(z.val.2 : Ambient n), ratMap (2 * (t : ℝ)) ((z.val.1 : Ambient n), (z.val.2 : Ambient n))⟫ = _
  simp only [ratMap, real_inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq,
    hy, one_pow, hz, mul_zero, zero_add, mul_one]
  simp only [aFun, hy, one_pow, mul_one]
  rw [show (2 * (t : ℝ)) ^ 2 / 4 = (t : ℝ) ^ 2 by ring]
  simp only [div_eq_mul_inv]
  ring

theorem inner_left_nonneg {n : ℕ} (z : orthogonalPairs n) (t : _root_.unitInterval) :
    0 ≤ ⟪(z.val.1 : Ambient n), (point z t : Ambient n)⟫ := by
  rw [inner_left]
  apply div_nonneg
  · nlinarith [mul_nonneg t.property.1 (sub_nonneg.mpr t.property.2)]
  · positivity

theorem inner_right_nonneg {n : ℕ} (z : orthogonalPairs n) (t : _root_.unitInterval) :
    0 ≤ ⟪(z.val.2 : Ambient n), (point z t : Ambient n)⟫ := by
  rw [inner_right]
  exact div_nonneg (mul_nonneg (by norm_num) t.property.1) (by positivity)

theorem point_ne_neg_left {n : ℕ} (z : orthogonalPairs n) (t : _root_.unitInterval) :
    (point z t : Ambient n) ≠ -(z.val.1 : Ambient n) := by
  intro h
  have he := inner_left_nonneg z t
  rw [h, inner_neg_right, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp z.val.1.property] at he
  norm_num at he

theorem point_ne_neg_right {n : ℕ} (z : orthogonalPairs n) (t : _root_.unitInterval) :
    (point z t : Ambient n) ≠ -(z.val.2 : Ambient n) := by
  intro h
  have he := inner_right_nonneg z t
  rw [h, inner_neg_right, real_inner_self_eq_norm_sq,
    mem_sphere_zero_iff_norm.mp z.val.2.property] at he
  norm_num at he

end
end Finsler.RationalSphereArcCarrier
