module

public import Finsler.Analysis.IntervalH1CurveRealization

/-! Continuity into the H¹ graph space from uniform convergence. Two graph elements whose values
and velocities are almost everywhere given by functions that differ by at most ε on (0,1) are at
H¹ distance at most 2ε, since (0,1) has measure one. Hence uniform convergence of positions and
velocities gives convergence in the graph space, and joint continuity in a parameter and in
t ∈ [0,1] gives uniform convergence by compactness of [0,1]. -/

@[expose] public section

namespace Finsler.SobolevC1Continuity

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevCurveRealization
open MeasureTheory Set Filter Metric
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- The H¹ distance is at most twice the supremum of the position and velocity differences. -/
theorem norm_sub_le_of_ae {u₁ u₂ : Space n} {c₁ c₂ c₁' c₂' : ℝ → Ambient n} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hv₁ : value u₁ =ᵐ[intervalMeasure] c₁) (hv₂ : value u₂ =ᵐ[intervalMeasure] c₂)
    (hw₁ : velocity u₁ =ᵐ[intervalMeasure] c₁') (hw₂ : velocity u₂ =ᵐ[intervalMeasure] c₂')
    (h0 : ∀ t ∈ Ioo (0 : ℝ) 1, ‖c₁ t - c₂ t‖ ≤ ε)
    (h1 : ∀ t ∈ Ioo (0 : ℝ) 1, ‖c₁' t - c₂' t‖ ≤ ε) :
    ‖u₁ - u₂‖ ≤ 2 * ε := by
  have hval : ‖value (u₁ - u₂)‖ ≤ ε := by
    have he : value (u₁ - u₂) = value u₁ - value u₂ := (valueL n).map_sub u₁ u₂
    rw [he]
    apply valueLp_norm_le_of_ae_bound hε
    filter_upwards [Lp.coeFn_sub (value u₁) (value u₂), hv₁, hv₂,
      ae_restrict_mem measurableSet_Ioo] with t ha hb hc ht
    rw [ha, Pi.sub_apply, hb, hc]
    exact h0 t ht
  have hvel : ‖velocity (u₁ - u₂)‖ ≤ ε := by
    have he : velocity (u₁ - u₂) = velocity u₁ - velocity u₂ := (velocityL n).map_sub u₁ u₂
    rw [he]
    apply valueLp_norm_le_of_ae_bound hε
    filter_upwards [Lp.coeFn_sub (velocity u₁) (velocity u₂), hw₁, hw₂,
      ae_restrict_mem measurableSet_Ioo] with t ha hb hc ht
    rw [ha, Pi.sub_apply, hb, hc]
    exact h1 t ht
  have hsq := norm_sq_eq (u₁ - u₂)
  have h2 : ‖u₁ - u₂‖ ^ 2 ≤ (2 * ε) ^ 2 := by
    rw [hsq]
    have ha := pow_le_pow_left₀ (norm_nonneg _) hval 2
    have hb := pow_le_pow_left₀ (norm_nonneg _) hvel 2
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h2

/-- Uniform convergence of positions and velocities on (0,1) gives convergence in the graph
space. -/
theorem tendsto_of_uniform {X : Type*} {l : Filter X} {u : X → Space n} {u₀ : Space n}
    {c c' : X → ℝ → Ambient n} {c₀ c₀' : ℝ → Ambient n}
    (hv : ∀ᶠ x in l, value (u x) =ᵐ[intervalMeasure] c x)
    (hw : ∀ᶠ x in l, velocity (u x) =ᵐ[intervalMeasure] c' x)
    (hv₀ : value u₀ =ᵐ[intervalMeasure] c₀) (hw₀ : velocity u₀ =ᵐ[intervalMeasure] c₀')
    (hunif : ∀ ε > 0, ∀ᶠ x in l, ∀ t ∈ Ioo (0 : ℝ) 1,
      ‖c x t - c₀ t‖ ≤ ε ∧ ‖c' x t - c₀' t‖ ≤ ε) :
    Tendsto u l (𝓝 u₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hv, hw, hunif (ε / 4) (by positivity)] with x h1 h2 h3
  rw [dist_eq_norm]
  have h := norm_sub_le_of_ae (by positivity : (0 : ℝ) ≤ ε / 4) h1 hv₀ h2 hw₀
    (fun t ht => (h3 t ht).1) (fun t ht => (h3 t ht).2)
  linarith

/-- Joint continuity at the points (x₀, t), t ∈ [0,1], gives uniform convergence on [0,1]. -/
theorem eventually_uniform {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] {x₀ : X}
    {f : X → ℝ → E}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun q : X × ℝ => f q.1 q.2) (x₀, t))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc (0 : ℝ) 1, ‖f x t - f x₀ t‖ < ε := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro t ht
  have h1 := (hf t ht).eventually (Metric.ball_mem_nhds (f x₀ t) (half_pos hε))
  have hc : ContinuousAt (fun z : X × ℝ => f x₀ z.2) (x₀, t) :=
    ContinuousAt.comp_of_eq (g := fun q : X × ℝ => f q.1 q.2) (hf t ht)
      (continuousAt_const.prodMk continuousAt_snd) rfl
  have h2 := hc.eventually (Metric.ball_mem_nhds (f x₀ t) (half_pos hε))
  filter_upwards [h1, h2] with z hz1 hz2
  rw [dist_eq_norm] at hz1 hz2
  calc ‖f z.1 z.2 - f x₀ z.2‖ = ‖(f z.1 z.2 - f x₀ t) - (f x₀ z.2 - f x₀ t)‖ := by
        congr 1
        abel
    _ ≤ ‖f z.1 z.2 - f x₀ t‖ + ‖f x₀ z.2 - f x₀ t‖ := norm_sub_le _ _
    _ < ε := by linarith

end

end Finsler.SobolevC1Continuity
