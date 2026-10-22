module

public import Finsler.Definitions.Sphere
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic.Module

/-! The rational sphere curve ((1 - a) x + r y) / (1 + a) with a = r² ‖y‖² / 4,
the inverse stereographic projection from -x of the tangent vector r y. It has unit
length exactly when x is a unit vector orthogonal to y, equals x at r = 0, and its
explicit derivative in the pair (x, y) differs from (α, β) ↦ α + r β by O(r²)
uniformly for bounded y. No normalization theory is used. -/

@[expose] public section

namespace Finsler.RationalSphereCurve

open Finsler.SphereGeometry
open scoped RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- The quadratic coefficient a = r² ‖y‖² / 4. -/
def aFun (r : ℝ) (y : Ambient n) : ℝ := r ^ 2 * ‖y‖ ^ 2 / 4

theorem aFun_nonneg (r : ℝ) (y : Ambient n) : 0 ≤ aFun r y := by
  unfold aFun
  positivity

/-- The rational sphere curve in the pair (base point, tangent direction). -/
def ratMap (r : ℝ) (z : Ambient n × Ambient n) : Ambient n :=
  (1 + aFun r z.2)⁻¹ • ((1 - aFun r z.2) • z.1 + r • z.2)

theorem ratMap_zero (z : Ambient n × Ambient n) : ratMap 0 z = z.1 := by
  simp [ratMap, aFun]

theorem norm_ratMap {r : ℝ} {x y : Ambient n} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫ = 0) :
    ‖ratMap r (x, y)‖ = 1 := by
  have ha := aFun_nonneg r y
  have hsq : ‖(1 - aFun r y) • x + r • y‖ ^ 2 = (1 + aFun r y) ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      hxy, hx, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    unfold aFun
    ring
  have hnorm : ‖(1 - aFun r y) • x + r • y‖ = 1 + aFun r y := by
    have h1 : 0 ≤ ‖(1 - aFun r y) • x + r • y‖ := norm_nonneg _
    nlinarith [hsq, sq_nonneg (‖(1 - aFun r y) • x + r • y‖ - (1 + aFun r y)),
      sq_nonneg (‖(1 - aFun r y) • x + r • y‖ + (1 + aFun r y))]
  unfold ratMap
  rw [norm_smul, hnorm, Real.norm_eq_abs, abs_of_pos (by positivity)]
  field_simp

theorem aFun_eq (r : ℝ) (y : Ambient n) : aFun r y = r ^ 2 / 4 * ‖y‖ ^ 2 := by
  unfold aFun
  ring

/-- Derivative of the quadratic coefficient in the pair variable. -/
def aDeriv (r : ℝ) (z : Ambient n × Ambient n) : Ambient n × Ambient n →L[ℝ] ℝ :=
  (r ^ 2 / 4) • (2 • (innerSL ℝ z.2).comp (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)))

theorem aDeriv_apply (r : ℝ) (z w : Ambient n × Ambient n) :
    aDeriv r z w = r ^ 2 / 2 * ⟪z.2, w.2⟫ := by
  simp only [aDeriv, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  ring

theorem aFun_hasFDerivAt (r : ℝ) (z : Ambient n × Ambient n) :
    HasFDerivAt (fun w : Ambient n × Ambient n => aFun r w.2) (aDeriv r z) z := by
  have h := ((hasFDerivAt_snd (p := z)).norm_sq).const_mul (r ^ 2 / 4)
  have hfun : (fun w : Ambient n × Ambient n => aFun r w.2) =
      fun w => r ^ 2 / 4 * ‖w.2‖ ^ 2 := funext fun w => aFun_eq r w.2
  rw [hfun]
  exact h

/-- The explicit derivative of the rational curve in the pair variable. -/
def ratDeriv (r : ℝ) (z : Ambient n × Ambient n) : Ambient n × Ambient n →L[ℝ] Ambient n :=
  (1 + aFun r z.2)⁻¹ •
      ((1 - aFun r z.2) • ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n) +
        (-aDeriv r z).smulRight z.1 + r • ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)) +
    ((-((1 + aFun r z.2) ^ 2)⁻¹) • aDeriv r z).smulRight
      ((1 - aFun r z.2) • z.1 + r • z.2)

theorem ratMap_hasFDerivAt (r : ℝ) (z : Ambient n × Ambient n) :
    HasFDerivAt (ratMap r) (ratDeriv r z) z := by
  have hA := aFun_hasFDerivAt r z
  have hs : (1 + aFun r z.2) ≠ 0 := by have := aFun_nonneg r z.2; positivity
  have hc : HasFDerivAt (fun w : Ambient n × Ambient n => (1 + aFun r w.2)⁻¹)
      ((-((1 + aFun r z.2) ^ 2)⁻¹) • aDeriv r z) z := by
    have h1 : HasFDerivAt (fun w : Ambient n × Ambient n => 1 + aFun r w.2) (aDeriv r z) z := by
      simpa using hA.const_add 1
    exact (hasDerivAt_inv hs).comp_hasFDerivAt z h1
  have hV : HasFDerivAt (fun w : Ambient n × Ambient n => (1 - aFun r w.2) • w.1 + r • w.2)
      ((1 - aFun r z.2) • ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n) +
        (-aDeriv r z).smulRight z.1 + r • ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)) z := by
    have h1 : HasFDerivAt (fun w : Ambient n × Ambient n => 1 - aFun r w.2) (-aDeriv r z) z := by
      simpa using hA.const_sub 1
    have h2 := h1.smul (hasFDerivAt_fst (p := z))
    have h3 : HasFDerivAt (fun w : Ambient n × Ambient n => r • w.2)
        (r • ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)) z :=
      (r • ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)).hasFDerivAt
    exact h2.add h3
  exact hc.smul hV

theorem ratMap_fderiv (r : ℝ) (z : Ambient n × Ambient n) :
    fderiv ℝ (ratMap r) z = ratDeriv r z :=
  (ratMap_hasFDerivAt r z).fderiv

theorem ratDeriv_apply (r : ℝ) (z w : Ambient n × Ambient n) :
    ratDeriv r z w = (1 + aFun r z.2)⁻¹ •
        ((1 - aFun r z.2) • w.1 - (r ^ 2 / 2 * ⟪z.2, w.2⟫) • z.1 + r • w.2) -
      (((1 + aFun r z.2) ^ 2)⁻¹ * (r ^ 2 / 2 * ⟪z.2, w.2⟫)) •
        ((1 - aFun r z.2) • z.1 + r • z.2) := by
  simp only [ratDeriv, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', neg_apply, aDeriv_apply, neg_smul,
    smul_eq_mul, neg_mul]
  abel_nf

theorem ratMap_contDiff (r : ℝ) : ContDiff ℝ 1 (ratMap (n := n) r) := by
  have hq : ContDiff ℝ 1 (fun w : Ambient n × Ambient n => aFun r w.2) := by
    have h : ContDiff ℝ 1 (fun w : Ambient n × Ambient n => r ^ 2 / 4 * ‖w.2‖ ^ 2) :=
      contDiff_const.mul (contDiff_snd.norm_sq ℝ)
    have hfun : (fun w : Ambient n × Ambient n => aFun r w.2) =
        fun w => r ^ 2 / 4 * ‖w.2‖ ^ 2 := funext fun w => aFun_eq r w.2
    rw [hfun]
    exact h
  have hc : ContDiff ℝ 1 (fun w : Ambient n × Ambient n => (1 + aFun r w.2)⁻¹) :=
    (contDiff_const.add hq).inv fun w => by have := aFun_nonneg r w.2; positivity
  have hV : ContDiff ℝ 1 (fun w : Ambient n × Ambient n => (1 - aFun r w.2) • w.1 + r • w.2) :=
    ((contDiff_const.sub hq).smul contDiff_fst).add (contDiff_snd.const_smul r)
  exact hc.smul hV

theorem aFun_le {r M : ℝ} {y : Ambient n} (_hM : 0 ≤ M) (hy : ‖y‖ ≤ M) :
    aFun r y ≤ r ^ 2 * M ^ 2 / 4 := by
  unfold aFun
  have h1 : ‖y‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
  have h2 : 0 ≤ r ^ 2 := sq_nonneg r
  nlinarith

theorem coeff_one_sub (A : ℝ) (hA : 0 ≤ A) : |(1 + A)⁻¹ * (1 - A) - 1| ≤ 2 * A := by
  have hpos : 0 < 1 + A := by linarith
  have hid : (1 + A)⁻¹ * (1 - A) - 1 = -(2 * A / (1 + A)) := by
    field_simp
    ring
  rw [hid, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
  nlinarith

theorem coeff_inv_sub (A : ℝ) (hA : 0 ≤ A) : |(1 + A)⁻¹ - 1| ≤ A := by
  have hpos : 0 < 1 + A := by linarith
  have hid : (1 + A)⁻¹ - 1 = -(A / (1 + A)) := by
    field_simp
    ring
  rw [hid, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
  nlinarith

theorem inv_le_one_of_nonneg (A : ℝ) (hA : 0 ≤ A) : (1 + A)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by linarith)

theorem ratMap_sub_eq (r : ℝ) (x y : Ambient n) :
    ratMap r (x, y) - x - r • y =
      ((1 + aFun r y)⁻¹ * (1 - aFun r y) - 1) • x + ((1 + aFun r y)⁻¹ - 1) • (r • y) := by
  unfold ratMap
  module

/-- The value error of the rational curve is quadratic in r. -/
theorem ratMap_sub_bound {r : ℝ} (hr : |r| ≤ 1) {x y : Ambient n} (hx : ‖x‖ = 1) {M : ℝ}
    (hM : 0 ≤ M) (hy : ‖y‖ ≤ M) :
    ‖ratMap r (x, y) - x - r • y‖ ≤ r ^ 2 * (M ^ 2 / 2 + M ^ 3 / 4) := by
  have hA0 := aFun_nonneg r y
  have hAM := aFun_le (r := r) hM hy
  rw [ratMap_sub_eq]
  have h1 := coeff_one_sub (aFun r y) hA0
  have h2 := coeff_inv_sub (aFun r y) hA0
  have hry : ‖r • y‖ ≤ M := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |r| * ‖y‖ ≤ 1 * M := mul_le_mul hr hy (norm_nonneg _) zero_le_one
      _ = M := one_mul M
  calc
    _ ≤ ‖((1 + aFun r y)⁻¹ * (1 - aFun r y) - 1) • x‖ + ‖((1 + aFun r y)⁻¹ - 1) • (r • y)‖ :=
      norm_add_le _ _
    _ = |(1 + aFun r y)⁻¹ * (1 - aFun r y) - 1| * 1 + |(1 + aFun r y)⁻¹ - 1| * ‖r • y‖ := by
      rw [norm_smul, norm_smul, hx, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ 2 * aFun r y * 1 + aFun r y * M := by
      gcongr
    _ ≤ 2 * (r ^ 2 * M ^ 2 / 4) * 1 + r ^ 2 * M ^ 2 / 4 * M := by
      gcongr
    _ = r ^ 2 * (M ^ 2 / 2 + M ^ 3 / 4) := by ring

theorem norm_curveVector {r : ℝ} {x y : Ambient n} (hx : ‖x‖ = 1) (hxy : ⟪x, y⟫ = 0) :
    ‖(1 - aFun r y) • x + r • y‖ = 1 + aFun r y := by
  have ha := aFun_nonneg r y
  have hsq : ‖(1 - aFun r y) • x + r • y‖ ^ 2 = (1 + aFun r y) ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      hxy, hx, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    unfold aFun
    ring
  have h1 : 0 ≤ ‖(1 - aFun r y) • x + r • y‖ := norm_nonneg _
  nlinarith [hsq, sq_nonneg (‖(1 - aFun r y) • x + r • y‖ - (1 + aFun r y)),
    sq_nonneg (‖(1 - aFun r y) • x + r • y‖ + (1 + aFun r y))]

/-- The derivative error of the rational curve is quadratic in r. -/
theorem ratDeriv_sub_bound {r : ℝ} (hr : |r| ≤ 1) {x y : Ambient n} (hx : ‖x‖ = 1)
    (hxy : ⟪x, y⟫ = 0) {M : ℝ} (hM : 0 ≤ M) (hy : ‖y‖ ≤ M) (α β : Ambient n) :
    ‖ratDeriv r (x, y) (α, β) - α - r • β‖ ≤
      r ^ 2 * (M ^ 2 / 2 * ‖α‖ + (M ^ 2 / 4 + M) * ‖β‖) := by
  set A := aFun r y with hAdef
  set c := (1 + A)⁻¹ with hcdef
  set D := r ^ 2 / 2 * ⟪y, β⟫ with hDdef
  have hA0 : 0 ≤ A := aFun_nonneg r y
  have hAM : A ≤ r ^ 2 * M ^ 2 / 4 := aFun_le hM hy
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_nonneg A hA0
  have hV : ‖(1 - A) • x + r • y‖ = 1 + A := norm_curveVector hx hxy
  have hcV : c ^ 2 * (1 + A) ≤ 1 := by
    have hpos : 0 < 1 + A := by linarith
    rw [hcdef, inv_pow, inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hD : |D| ≤ r ^ 2 / 2 * (M * ‖β‖) := by
    rw [hDdef, abs_mul, abs_of_nonneg (by positivity)]
    gcongr
    exact (abs_real_inner_le_norm y β).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
  have heq : ratDeriv r (x, y) (α, β) - α - r • β =
      (c * (1 - A) - 1) • α + (c - 1) • (r • β) + (-(c * D)) • x +
        (-(c ^ 2 * D)) • ((1 - A) • x + r • y) := by
    rw [ratDeriv_apply]
    simp only [hAdef.symm, hcdef.symm, hDdef.symm]
    rw [hcdef, inv_pow]
    module
  rw [heq]
  have h1 := coeff_one_sub A hA0
  have h2 := coeff_inv_sub A hA0
  have hrb : ‖r • β‖ ≤ ‖β‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |r| * ‖β‖ ≤ 1 * ‖β‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)
      _ = ‖β‖ := one_mul _
  calc
    _ ≤ ‖(c * (1 - A) - 1) • α‖ + ‖(c - 1) • (r • β)‖ + ‖(-(c * D)) • x‖ +
          ‖(-(c ^ 2 * D)) • ((1 - A) • x + r • y)‖ := by
      refine (norm_add_le _ _).trans ?_
      gcongr
      refine (norm_add_le _ _).trans ?_
      gcongr
      exact norm_add_le _ _
    _ = |c * (1 - A) - 1| * ‖α‖ + |c - 1| * ‖r • β‖ + c * |D| * 1 + c ^ 2 * |D| * (1 + A) := by
      rw [norm_smul (c * (1 - A) - 1) α, norm_smul (c - 1) (r • β), norm_smul (-(c * D)) x,
        norm_smul (-(c ^ 2 * D)) ((1 - A) • x + r • y), hx, hV, Real.norm_eq_abs,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg, abs_neg, abs_mul c D, abs_mul (c ^ 2) D,
        abs_of_nonneg hc0, abs_of_nonneg (by positivity : 0 ≤ c ^ 2)]
    _ ≤ 2 * A * ‖α‖ + A * ‖β‖ + 1 * |D| * 1 + |D| := by
      have hcD : c * |D| * 1 ≤ 1 * |D| * 1 := by
        gcongr
      have hc2D : c ^ 2 * |D| * (1 + A) ≤ |D| := by
        have := mul_le_mul_of_nonneg_right hcV (abs_nonneg D)
        nlinarith
      have hα : |c * (1 - A) - 1| * ‖α‖ ≤ 2 * A * ‖α‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      have hβ : |c - 1| * ‖r • β‖ ≤ A * ‖β‖ :=
        mul_le_mul h2 hrb (norm_nonneg _) hA0
      linarith
    _ ≤ 2 * (r ^ 2 * M ^ 2 / 4) * ‖α‖ + r ^ 2 * M ^ 2 / 4 * ‖β‖ +
          1 * (r ^ 2 / 2 * (M * ‖β‖)) * 1 + r ^ 2 / 2 * (M * ‖β‖) := by
      gcongr
    _ = r ^ 2 * (M ^ 2 / 2 * ‖α‖ + (M ^ 2 / 4 + M) * ‖β‖) := by ring

end

end Finsler.RationalSphereCurve
