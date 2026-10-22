module

public import Finsler.Analysis.NormalizeDeriv
public import Finsler.Analysis.ContractionInverse
public import Finsler.Analysis.IntervalH1SuperpositionDeriv

/-! The radial remainder of a flow written in polar form. For a C¹ map R on (E × E) × ℝ, the
function rad(y,v) = ‖v‖²·R((y, v/‖v‖), ‖v‖) vanishes at v = 0, is bounded by A‖v‖² when ‖R‖ ≤ A,
is differentiable at 0 with derivative 0, and away from 0 has derivative of norm at most
(2A + 3B)‖v‖ when also ‖DR‖ ≤ B (the radial projection contributes 2/‖v‖, the radius 1). On a
small ball it is therefore 1/2-Lipschitz, which is what the contraction inverse needs. -/

@[expose] public section

namespace Finsler.RadialRemainder

open Set Filter Metric
open scoped Topology

noncomputable section

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The polar point ((y, v/‖v‖), ‖v‖). -/
def polar (y v : E) : (E × E) × ℝ := ((y, ‖v‖⁻¹ • v), ‖v‖)

/-- The radial remainder ‖v‖²·R(polar y v). -/
def rad (R : (E × E) × ℝ → W) (y v : E) : W := ‖v‖ ^ 2 • R (polar y v)

theorem rad_zero (R : (E × E) × ℝ → W) (y : E) : rad R y 0 = 0 := by
  simp [rad]

theorem norm_polar_snd_le (y v : E) : ‖(polar y v).1.2‖ ≤ 1 := by
  simp only [polar]
  rcases eq_or_ne v 0 with h | h
  · simp [h]
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

theorem norm_rad_le {R : (E × E) × ℝ → W} {y v : E} {A : ℝ} (hA : ‖R (polar y v)‖ ≤ A) :
    ‖rad R y v‖ ≤ A * ‖v‖ ^ 2 := by
  unfold rad
  rw [norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  calc ‖v‖ ^ 2 * ‖R (polar y v)‖ ≤ ‖v‖ ^ 2 * A := mul_le_mul_of_nonneg_left hA (sq_nonneg _)
    _ = A * ‖v‖ ^ 2 := mul_comm _ _

/-- Differentiability at the origin with derivative zero. -/
theorem rad_hasFDerivAt_zero {R : (E × E) × ℝ → W} {y : E} {A : ℝ}
    (hA : ∀ v : E, ‖v‖ ≤ 1 → ‖R (polar y v)‖ ≤ A) :
    HasFDerivAt (rad R y) (0 : E →L[ℝ] W) 0 := by
  apply Finsler.SobolevSuperpositionDeriv.hasFDerivAt_of_quadratic (K := A)
  intro d hd
  rw [zero_add, rad_zero, sub_zero, zero_apply, sub_zero]
  exact norm_rad_le (hA d hd)

/-- Away from the origin the derivative of the radial remainder is O(‖v‖). -/
theorem rad_hasFDerivAt {R : (E × E) × ℝ → W} (hR : ContDiff ℝ 1 R) {y v : E} (hv : v ≠ 0)
    (hv1 : ‖v‖ ≤ 1) {A B : ℝ} (hA : ‖R (polar y v)‖ ≤ A) (hB : ‖fderiv ℝ R (polar y v)‖ ≤ B) :
    ∃ D : E →L[ℝ] W, HasFDerivAt (rad R y) D v ∧ ‖D‖ ≤ (2 * A + 3 * B) * ‖v‖ := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
  have hB0 : 0 ≤ B := (ContinuousLinearMap.opNorm_nonneg _).trans hB
  -- the norm and its derivative
  have hnorm : HasFDerivAt (fun w : E => ‖w‖) (fderiv ℝ (fun w : E => ‖w‖) v) v :=
    ((contDiffAt_norm (n := 1) ℝ hv).differentiableAt (by norm_num)).hasFDerivAt
  have hnb : ‖fderiv ℝ (fun w : E => ‖w‖) v‖ ≤ 1 := by
    have h := norm_fderiv_le_of_lipschitz ℝ (f := fun w : E => ‖w‖) (x₀ := v)
      (C := 1) lipschitzWith_one_norm
    simpa using h
  -- the radial projection
  obtain ⟨Dn, hDn, hDnb⟩ := Finsler.NormalizeDeriv.exists_hasFDerivAt_normalize hv
  -- the polar map
  set Np : E →L[ℝ] (E × E) × ℝ :=
    (((0 : E →L[ℝ] E).prod Dn).prod (fderiv ℝ (fun w : E => ‖w‖) v)) with hNp
  have hpolar : HasFDerivAt (polar y) Np v :=
    ((hasFDerivAt_const y v).prodMk hDn).prodMk hnorm
  have hNpb : ‖Np‖ ≤ 2 * ‖v‖⁻¹ + 1 := by
    rw [hNp]
    calc ‖((0 : E →L[ℝ] E).prod Dn).prod (fderiv ℝ (fun w : E => ‖w‖) v)‖
        ≤ ‖(0 : E →L[ℝ] E).prod Dn‖ + ‖fderiv ℝ (fun w : E => ‖w‖) v‖ := by
          rw [ContinuousLinearMap.opNorm_prod]
          exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
      _ ≤ 2 * ‖v‖⁻¹ + 1 := by
          gcongr
          rw [ContinuousLinearMap.opNorm_prod]
          exact norm_prod_le_iff.mpr ⟨by simp, hDnb⟩
  -- the composite R ∘ polar
  have hRd : HasFDerivAt R (fderiv ℝ R (polar y v)) (polar y v) :=
    ((hR.differentiable (by norm_num)) _).hasFDerivAt
  have hRp : HasFDerivAt (fun w => R (polar y w)) ((fderiv ℝ R (polar y v)).comp Np) v :=
    hRd.comp v hpolar
  -- the squared norm
  have hsq : HasFDerivAt (fun w : E => ‖w‖ ^ 2) ((2 * ‖v‖) • fderiv ℝ (fun w : E => ‖w‖) v) v := by
    have h := hnorm.pow 2
    simpa [pow_one, mul_comm] using h
  have hprod := hsq.smul hRp
  refine ⟨_, hprod, ?_⟩
  -- the bound
  have h1 : ‖(‖v‖ ^ 2) • (fderiv ℝ R (polar y v)).comp Np‖ ≤ ‖v‖ ^ 2 * (B * (2 * ‖v‖⁻¹ + 1)) := by
    calc ‖(‖v‖ ^ 2) • (fderiv ℝ R (polar y v)).comp Np‖
        ≤ ‖‖v‖ ^ 2‖ * ‖(fderiv ℝ R (polar y v)).comp Np‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖v‖ ^ 2 * (B * (2 * ‖v‖⁻¹ + 1)) := by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul hB hNpb (norm_nonneg _) hB0)
  have h2 : ‖((2 * ‖v‖) • fderiv ℝ (fun w : E => ‖w‖) v).smulRight (R (polar y v))‖ ≤
      2 * ‖v‖ * A := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc ‖(2 * ‖v‖) • fderiv ℝ (fun w : E => ‖w‖) v‖ * ‖R (polar y v)‖
        ≤ (2 * ‖v‖ * 1) * A := by
          gcongr
          calc ‖(2 * ‖v‖) • fderiv ℝ (fun w : E => ‖w‖) v‖
              ≤ ‖2 * ‖v‖‖ * ‖fderiv ℝ (fun w : E => ‖w‖) v‖ := ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ 2 * ‖v‖ * 1 := by
                rw [Real.norm_of_nonneg (by positivity)]
                gcongr
      _ = 2 * ‖v‖ * A := by ring
  have h3 : ‖v‖ ^ 2 * (B * (2 * ‖v‖⁻¹ + 1)) ≤ 3 * B * ‖v‖ := by
    have : ‖v‖ ^ 2 * (B * (2 * ‖v‖⁻¹ + 1)) = 2 * B * ‖v‖ + B * ‖v‖ ^ 2 := by
      field_simp
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hv1 (mul_nonneg hB0 hn.le)]
  calc ‖(‖v‖ ^ 2) • (fderiv ℝ R (polar y v)).comp Np +
        ((2 * ‖v‖) • fderiv ℝ (fun w : E => ‖w‖) v).smulRight (R (polar y v))‖
      ≤ ‖(‖v‖ ^ 2) • (fderiv ℝ R (polar y v)).comp Np‖ +
        ‖((2 * ‖v‖) • fderiv ℝ (fun w : E => ‖w‖) v).smulRight (R (polar y v))‖ :=
        norm_add_le _ _
    _ ≤ 3 * B * ‖v‖ + 2 * ‖v‖ * A := add_le_add (h1.trans h3) h2
    _ = (2 * A + 3 * B) * ‖v‖ := by ring

section Inverse

variable {R : (E × E) × ℝ → W} (hR : ContDiff ℝ 1 R) {y : E} {A B ρ : ℝ}
  (hA : ∀ v : E, ‖v‖ ≤ 1 → ‖R (polar y v)‖ ≤ A)
  (hB : ∀ v : E, ‖v‖ ≤ 1 → ‖fderiv ℝ R (polar y v)‖ ≤ B)
  (hρ1 : ρ ≤ 1) (hρ : (2 * A + 3 * B) * ρ ≤ 1 / 2)

include hR hA hB hρ1 hρ in
set_option maxHeartbeats 1000000 in
/-- On a small ball the radial remainder is 1/2-Lipschitz. -/
theorem rad_lipschitz :
    ∀ v ∈ closedBall (0 : E) ρ, ∀ w ∈ closedBall (0 : E) ρ,
      ‖rad R y v - rad R y w‖ ≤ ‖v - w‖ / 2 := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0 (by simp))
  have hB0 : 0 ≤ B :=
    (ContinuousLinearMap.opNorm_nonneg _).trans (hB 0 (by simp))
  have hd : ∀ v ∈ closedBall (0 : E) ρ, DifferentiableAt ℝ (rad R y) v ∧
      ‖fderiv ℝ (rad R y) v‖ ≤ 1 / 2 := by
    intro v hv
    have hv' : ‖v‖ ≤ ρ := by simpa using hv
    have hv1 : ‖v‖ ≤ 1 := hv'.trans hρ1
    rcases eq_or_ne v 0 with h0 | h0
    · subst h0
      have h := rad_hasFDerivAt_zero (R := R) (y := y) hA
      refine ⟨h.differentiableAt, ?_⟩
      rw [h.fderiv, norm_zero]
      norm_num
    · obtain ⟨D, hD, hDb⟩ := rad_hasFDerivAt hR h0 hv1 (hA v hv1) (hB v hv1)
      refine ⟨hD.differentiableAt, ?_⟩
      rw [hD.fderiv]
      calc ‖D‖ ≤ (2 * A + 3 * B) * ‖v‖ := hDb
        _ ≤ (2 * A + 3 * B) * ρ := mul_le_mul_of_nonneg_left hv' (by linarith)
        _ ≤ 1 / 2 := hρ
  intro v hv w hw
  have h := (convex_closedBall (0 : E) ρ).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => (hd x hx).1) (fun x hx => (hd x hx).2) hw hv
  linarith

variable [CompleteSpace W]

end Inverse

section InverseE

variable [CompleteSpace E] {R : (E × E) × ℝ → E} (hR : ContDiff ℝ 1 R) {y : E} {A B ρ : ℝ}
  (hA : ∀ v : E, ‖v‖ ≤ 1 → ‖R (polar y v)‖ ≤ A)
  (hB : ∀ v : E, ‖v‖ ≤ 1 → ‖fderiv ℝ R (polar y v)‖ ≤ B)
  (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρ : (2 * A + 3 * B) * ρ ≤ 1 / 2)

include hR hA hB hρ0 hρ1 hρ in
/-- Existence of a preimage under v ↦ v + rad(y,v) in the ball of radius ρ. -/
theorem exists_rad_preimage {z : E} (hz : ‖z‖ ≤ ρ / 2) :
    ∃ v ∈ closedBall (0 : E) ρ, v + rad R y v = z :=
  Finsler.ContractionInverse.exists_preimage hρ0 (rad_zero R y)
    (rad_lipschitz hR hA hB hρ1 hρ) hz

omit [CompleteSpace E] in
include hR hA hB hρ1 hρ in
/-- Uniqueness and 2-Lipschitz dependence of preimages. -/
theorem norm_sub_le_two_rad {v w : E} (hv : v ∈ closedBall (0 : E) ρ)
    (hw : w ∈ closedBall (0 : E) ρ) :
    ‖v - w‖ ≤ 2 * ‖(v + rad R y v) - (w + rad R y w)‖ :=
  Finsler.ContractionInverse.norm_sub_le_two (rad_lipschitz hR hA hB hρ1 hρ) hv hw

end InverseE

end

end Finsler.RadialRemainder
