module

public import Finsler.Analysis.L2QuadraticUniformIntegrability

/-! Uniform L¹/L² integrability of Banach-valued coefficients with quadratic
or linear growth along genuinely strongly convergent L² sequences. -/

@[expose] public section

namespace Finsler.CoefficientVitali

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable section

variable {α E G ι : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedAddCommGroup G] {μ : Measure α} {p : ℝ≥0∞}

theorem unifIntegrable_of_norm_le {f : ι → α → E} {g : ι → α → G}
    (hg : UnifIntegrable g p μ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hb : ∀ i, ∀ᵐ t ∂μ, ‖f i t‖ ≤ ‖g i t‖) : UnifIntegrable f p μ := by
  apply tendsto_nhds_bot_mono hg
  apply Eventually.of_forall
  intro ε
  simp only [iSup_le_iff]
  intro i s hs
  exact (eLpNorm_mono_ae (hf i).restrict ((hb i).filter_mono ae_restrict_le)).trans
    (le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le hs le_rfl)))

theorem unifIntegrable_const_smul [NormedSpace ℝ E] {f : ι → α → E}
    (hf : UnifIntegrable f p μ) (C : ℝ) :
    UnifIntegrable (fun i t => C • f i t) p μ := by
  have hm := ENNReal.Tendsto.const_mul (a := ‖C‖ₑ) hf (Or.inr (by finiteness))
  simp only [mul_zero] at hm
  apply tendsto_nhds_bot_mono hm
  apply Eventually.of_forall
  intro ε
  simp only [iSup_le_iff]
  intro i s hs
  change eLpNorm (C • f i) p (μ.restrict s) ≤ _
  rw [eLpNorm_const_smul]
  gcongr
  exact le_iSup_of_le i (le_iSup_of_le s (le_iSup_of_le hs le_rfl))

theorem lp_convergent_linear_unifIntegrable [NormedSpace ℝ E]
    {v : ℕ → Lp E 2 μ} {v₀ : Lp E 2 μ} (hv : Tendsto v atTop (𝓝 v₀))
    {g : ℕ → α → G} (hg : ∀ i, AEStronglyMeasurable (g i) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ∀ᵐ t ∂μ, ‖g i t‖ ≤ C * ‖v i t‖) :
    UnifIntegrable g 2 μ := by
  let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hui := unifIntegrable_of_tendsto_Lp (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (fun i => Lp.memLp (v i)) (Lp.memLp v₀)
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' v v₀).mp hv)
  apply unifIntegrable_of_norm_le (unifIntegrable_const_smul hui C) hg
  intro i
  filter_upwards [hb i] with t ht
  simpa only [norm_smul, Real.norm_of_nonneg hC] using ht

theorem lp_convergent_quadratic_unifIntegrable
    {v : ℕ → Lp E 2 μ} {v₀ : Lp E 2 μ} (hv : Tendsto v atTop (𝓝 v₀))
    {g : ℕ → α → G} (hg : ∀ i, AEStronglyMeasurable (g i) μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ∀ᵐ t ∂μ, ‖g i t‖ ≤ C * ‖v i t‖ ^ 2) :
    UnifIntegrable g 1 μ := by
  have hui := Finsler.QuadraticVitali.lp_convergent_quadratic_unifIntegrable hv
    (fun i => (hg i).norm) hC (fun i => (hb i).mono fun _ ht => by
      simpa only [norm_norm] using ht)
  exact unifIntegrable_of_norm_le hui hg (fun i => ae_of_all _ fun t => by simp)

end

end Finsler.CoefficientVitali
