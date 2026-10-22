module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The derivative of the radial projection v ↦ v/‖v‖ away from the origin has norm at most
2/‖v‖. This is the only singular factor in the C¹ estimate of the Finsler exponential map at the
zero section. -/

@[expose] public section

namespace Finsler.NormalizeDeriv

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem exists_hasFDerivAt_normalize {v : F} (hv : v ≠ 0) :
    ∃ D : F →L[ℝ] F, HasFDerivAt (fun w : F => ‖w‖⁻¹ • w) D v ∧ ‖D‖ ≤ 2 * ‖v‖⁻¹ := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnorm : HasFDerivAt (fun w : F => ‖w‖) (fderiv ℝ (fun w : F => ‖w‖) v) v :=
    ((contDiffAt_norm (n := 1) ℝ hv).differentiableAt (by norm_num)).hasFDerivAt
  have hnb : ‖fderiv ℝ (fun w : F => ‖w‖) v‖ ≤ 1 := by
    have h := norm_fderiv_le_of_lipschitz ℝ (f := fun w : F => ‖w‖) (x₀ := v)
      (C := 1) lipschitzWith_one_norm
    simpa using h
  set D1 := fderiv ℝ (fun w : F => ‖w‖) v with hD1
  have hinv : HasFDerivAt (fun w : F => ‖w‖⁻¹) ((-(‖v‖ ^ 2)⁻¹) • D1) v :=
    (hasDerivAt_inv hn.ne').comp_hasFDerivAt v hnorm
  have hD := hinv.smul (hasFDerivAt_id v)
  refine ⟨_, hD, ?_⟩
  have hb1 : ‖(‖v‖⁻¹ • ContinuousLinearMap.id ℝ F)‖ ≤ ‖v‖⁻¹ := by
    calc ‖(‖v‖⁻¹ • ContinuousLinearMap.id ℝ F)‖ ≤ ‖‖v‖⁻¹‖ * ‖ContinuousLinearMap.id ℝ F‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ ‖v‖⁻¹ * 1 := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
          gcongr
          exact ContinuousLinearMap.norm_id_le
      _ = ‖v‖⁻¹ := mul_one _
  have hb2 : ‖((-(‖v‖ ^ 2)⁻¹) • D1).smulRight v‖ ≤ ‖v‖⁻¹ := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    calc ‖(-(‖v‖ ^ 2)⁻¹) • D1‖ * ‖v‖ ≤ ((‖v‖ ^ 2)⁻¹ * 1) * ‖v‖ := by
          gcongr
          calc ‖(-(‖v‖ ^ 2)⁻¹) • D1‖ ≤ ‖-(‖v‖ ^ 2)⁻¹‖ * ‖D1‖ :=
                ContinuousLinearMap.opNorm_smul_le _ _
            _ ≤ (‖v‖ ^ 2)⁻¹ * 1 := by
                rw [norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity)]
                gcongr
      _ = ‖v‖⁻¹ := by field_simp
  calc ‖‖v‖⁻¹ • ContinuousLinearMap.id ℝ F + ((-(‖v‖ ^ 2)⁻¹) • D1).smulRight (id v)‖
      ≤ ‖(‖v‖⁻¹ • ContinuousLinearMap.id ℝ F)‖ + ‖((-(‖v‖ ^ 2)⁻¹) • D1).smulRight v‖ :=
        norm_add_le _ _
    _ ≤ ‖v‖⁻¹ + ‖v‖⁻¹ := add_le_add hb1 hb2
    _ = 2 * ‖v‖⁻¹ := by ring

end

end Finsler.NormalizeDeriv
