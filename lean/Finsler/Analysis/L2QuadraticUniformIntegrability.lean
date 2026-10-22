module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Quadratic growth converts genuine L² convergence into uniform L¹
integrability. This uses Vitali, not an assumed fixed pointwise dominator. -/

@[expose] public section

namespace Finsler.QuadraticVitali

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

variable {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
  {μ : Measure α}

theorem eLpNorm_norm_sq (f : α → E) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => ‖f x‖ ^ 2) 1 μ = (eLpNorm f 2 μ) ^ 2 := by
  simpa only [Real.rpow_two, ENNReal.ofReal_ofNat, one_mul, ENNReal.rpow_two] using
    (eLpNorm_norm_rpow (p := 1) f hf (by norm_num : (0 : ℝ) < 2))

theorem norm_sq_unifIntegrable {f : ι → α → E}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hu : UnifIntegrable f 2 μ) :
    UnifIntegrable (fun i x => ‖f i x‖ ^ 2) 1 μ := by
  have hpow := ENNReal.Tendsto.pow (n := 2) hu
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hpow
  apply tendsto_nhds_bot_mono hpow
  apply Eventually.of_forall
  intro ε
  simp only [iSup_le_iff]
  intro i s hs
  rw [eLpNorm_norm_sq _ (hf i).restrict]
  gcongr
  exact le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le hs le_rfl))

theorem const_mul_unifIntegrable {g : ι → α → ℝ}
    (hu : UnifIntegrable g 1 μ) (C : ℝ) :
    UnifIntegrable (fun i x => C * g i x) 1 μ := by
  have hmul := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) hu (Or.inr (by finiteness))
  simp only [mul_zero] at hmul
  apply tendsto_nhds_bot_mono hmul
  apply Eventually.of_forall
  intro ε
  simp only [iSup_le_iff]
  intro i s hs
  change eLpNorm (C • g i) 1 (μ.restrict s) ≤ _
  rw [eLpNorm_const_smul]
  gcongr
  exact le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le hs le_rfl))

theorem quadratic_bound_unifIntegrable {f : ι → α → E} {g : ι → α → ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hu : UnifIntegrable f 2 μ)
    (hg : ∀ i, AEStronglyMeasurable (g i) μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ C * ‖f i x‖ ^ 2) :
    UnifIntegrable g 1 μ := by
  apply (const_mul_unifIntegrable (norm_sq_unifIntegrable hf hu) C).ae_mono hg
  intro i
  filter_upwards [hbound i] with x hx
  have hnonneg : 0 ≤ C * ‖f i x‖ ^ 2 := mul_nonneg hC (sq_nonneg _)
  simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hnonneg, Real.norm_eq_abs] using
    ENNReal.ofReal_le_ofReal hx

theorem lp_convergent_quadratic_unifIntegrable {v : ℕ → Lp E 2 μ} {v₀ : Lp E 2 μ}
    (hv : Tendsto v atTop (𝓝 v₀)) {g : ℕ → α → ℝ}
    (hg : ∀ i, AEStronglyMeasurable (g i) μ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖g i x‖ ≤ C * ‖v i x‖ ^ 2) :
    UnifIntegrable g 1 μ := by
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  exact quadratic_bound_unifIntegrable (fun i => Lp.aestronglyMeasurable (v i))
    (unifIntegrable_of_tendsto_Lp (by norm_num) (by norm_num)
      (fun i => Lp.memLp (v i)) (Lp.memLp v₀)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' v v₀).mp hv)) hg hC hbound

end

end Finsler.QuadraticVitali
