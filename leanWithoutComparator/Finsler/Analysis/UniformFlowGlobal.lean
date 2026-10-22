module

public import Finsler.Analysis.UniformFlow

/-! The uniform-time flow with its global structure exposed: a globally C^(k+1) field g, its
global flow Φ (the ODE holds for all initial data and times), an open thickening of the compact
set on which g agrees with the original field, and a time τ for which trajectories from the
compact set stay in that thickening. -/

@[expose] public section

namespace Finsler.UniformFlowGlobal

open Set Filter Metric Finsler.UniformFlow
open scoped Topology ContDiff NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

theorem exists_global_flow {X : E → E} {O : Set E} (hO : IsOpen O) (k : ℕ)
    (hX : ContDiffOn ℝ (k + 1) X O) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ g : E → E, ∃ Φ : E → ℝ → E, ∃ δ τ : ℝ, 0 < δ ∧ 0 < τ ∧
      ContDiff ℝ (k + 1) g ∧ ContDiff ℝ (k + 1) (fun p : E × ℝ => Φ p.1 p.2) ∧
      (∀ z, Φ z 0 = z) ∧ (∀ z t, HasDerivAt (Φ z) (g (Φ z t)) t) ∧
      cthickening δ K ⊆ O ∧ (∀ z ∈ cthickening δ K, g z = X z) ∧
      ∀ z ∈ K, ∀ t : ℝ, |t| < τ → Φ z t ∈ cthickening δ K := by
  have hX' : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) X O := by exact_mod_cast hX
  obtain ⟨g, δ, hδ, hg, hcs, hδO, hgX⟩ := exists_global_extension hO hX' hK hKO
  have hg' : ContDiff ℝ (k + 1) g := by exact_mod_cast hg
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hg (by simp)
  obtain ⟨M, hM⟩ := hcs.exists_bound_of_continuous hg.continuous
  set M' := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨g, ODE.globalSolution g hC, δ, δ / (2 * M'), hδ, by positivity, hg',
    ODE.contDiff_globalSolution k g hC hg', ODE.globalSolution_zero g hC,
    fun z t => ODE.hasDerivAt_globalSolution g hC z t, hδO, hgX, ?_⟩
  intro z hz t ht
  have hdisp : ‖ODE.globalSolution g hC z t - z‖ ≤ M' * |t| := by
    rw [ODE.globalSolution_eq_integral g hC z t, add_sub_cancel_left]
    calc ‖∫ s in (0 : ℝ)..t, g (ODE.globalSolution g hC z s)‖ ≤ M' * |t - 0| :=
          intervalIntegral.norm_integral_le_of_norm_le_const
            (fun s _ => (hM _).trans (le_max_left _ _))
      _ = M' * |t| := by rw [sub_zero]
  have hle : M' * |t| ≤ δ := by
    have h1 : M' * |t| ≤ M' * (δ / (2 * M')) := mul_le_mul_of_nonneg_left ht.le hM'pos.le
    have h2 : M' * (δ / (2 * M')) = δ / 2 := by field_simp
    linarith
  apply mem_cthickening_of_dist_le _ z δ K hz
  rw [dist_eq_norm]
  exact hdisp.trans hle

end

end Finsler.UniformFlowGlobal
