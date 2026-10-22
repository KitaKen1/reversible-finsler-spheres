module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Calculus.MeanValue

/-! Inverting a perturbation of the identity by the contraction principle. If e vanishes at 0
and is 1/2-Lipschitz on the closed ball of radius ρ, then v ↦ v + e(v) has, for each z of norm at
most ρ/2, a unique preimage in the ball; the preimage is 2-Lipschitz in z and moves by at most
twice the sup-distance when e is perturbed. This replaces an inverse function theorem at the zero
section, where the Finsler exponential map is only C¹. -/

@[expose] public section

namespace Finsler.ContractionInverse

open Set Metric
open scoped NNReal ENNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

section Fixed

variable {e : E → E} {ρ : ℝ} (hρ : 0 ≤ ρ) (he0 : e 0 = 0)
  (hlip : ∀ v ∈ closedBall (0 : E) ρ, ∀ w ∈ closedBall (0 : E) ρ, ‖e v - e w‖ ≤ ‖v - w‖ / 2)
  {z : E} (hz : ‖z‖ ≤ ρ / 2)

omit [CompleteSpace E] in
include he0 hlip hz in
theorem mapsTo : MapsTo (fun v => z - e v) (closedBall (0 : E) ρ) (closedBall (0 : E) ρ) := by
  intro v hv
  rw [mem_closedBall_zero_iff] at hv ⊢
  have h0 : (0 : E) ∈ closedBall (0 : E) ρ := mem_closedBall_self (le_trans (norm_nonneg v) hv)
  have h1 := hlip v (mem_closedBall_zero_iff.mpr hv) 0 h0
  rw [he0, sub_zero, sub_zero] at h1
  calc ‖z - e v‖ ≤ ‖z‖ + ‖e v‖ := norm_sub_le _ _
    _ ≤ ρ / 2 + ‖v‖ / 2 := add_le_add hz h1
    _ ≤ ρ := by linarith

include hρ he0 hlip hz in
/-- Existence of a preimage of z under v ↦ v + e(v) in the ball. -/
theorem exists_preimage : ∃ v ∈ closedBall (0 : E) ρ, v + e v = z := by
  have hmaps := mapsTo he0 hlip hz
  have hcontr : ContractingWith (1 / 2 : ℝ≥0) (hmaps.restrict _ _ _) := by
    refine ⟨NNReal.half_lt_self one_ne_zero, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    change dist (z - e a) (z - e b) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist (a : E) (b : E)
    rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_left, norm_sub_rev]
    have h := hlip a a.2 b b.2
    push_cast
    linarith
  have h0 : (0 : E) ∈ closedBall (0 : E) ρ := mem_closedBall_self hρ
  obtain ⟨v, hv, hfix, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hmaps h0
    (edist_ne_top _ _)
  refine ⟨v, hv, ?_⟩
  have hzv : z - e v = v := hfix
  calc v + e v = (z - e v) + e v := by rw [hzv]
    _ = z := sub_add_cancel z (e v)

omit [CompleteSpace E] in
include hlip in
/-- Uniqueness and 2-Lipschitz dependence of preimages. -/
theorem norm_sub_le_two {v w : E} (hv : v ∈ closedBall (0 : E) ρ) (hw : w ∈ closedBall (0 : E) ρ) :
    ‖v - w‖ ≤ 2 * ‖(v + e v) - (w + e w)‖ := by
  have h := hlip v hv w hw
  have h2 : ‖v - w‖ ≤ ‖(v + e v) - (w + e w)‖ + ‖e v - e w‖ := by
    have : v - w = ((v + e v) - (w + e w)) - (e v - e w) := by abel
    rw [this]
    exact norm_sub_le _ _
  linarith

end Fixed

omit [CompleteSpace E] in
/-- Dependence of preimages on the perturbation. -/
theorem norm_sub_le_of_perturb {e₁ e₂ : E → E} {ρ : ℝ}
    (hlip : ∀ v ∈ closedBall (0 : E) ρ, ∀ w ∈ closedBall (0 : E) ρ, ‖e₁ v - e₁ w‖ ≤ ‖v - w‖ / 2)
    {z : E} {v₁ v₂ : E} (hv₁ : v₁ ∈ closedBall (0 : E) ρ) (hv₂ : v₂ ∈ closedBall (0 : E) ρ)
    (h₁ : v₁ + e₁ v₁ = z) (h₂ : v₂ + e₂ v₂ = z) : ‖v₁ - v₂‖ ≤ 2 * ‖e₂ v₂ - e₁ v₂‖ := by
  have h := hlip v₁ hv₁ v₂ hv₂
  have heq : v₁ - v₂ = (e₂ v₂ - e₁ v₂) + (e₁ v₂ - e₁ v₁) := by
    calc v₁ - v₂ = ((v₁ + e₁ v₁) - e₁ v₁) - ((v₂ + e₂ v₂) - e₂ v₂) := by abel
      _ = (z - e₁ v₁) - (z - e₂ v₂) := by rw [h₁, h₂]
      _ = (e₂ v₂ - e₁ v₂) + (e₁ v₂ - e₁ v₁) := by abel
  have h2 : ‖v₁ - v₂‖ ≤ ‖e₂ v₂ - e₁ v₂‖ + ‖e₁ v₂ - e₁ v₁‖ := by
    rw [heq]
    exact norm_add_le _ _
  rw [norm_sub_rev (e₁ v₂)] at h2
  linarith

section Deriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A derivative bound 1/2 on the closed ball gives the Lipschitz hypothesis. -/
theorem lipschitz_of_fderiv_le {e : F → F} {ρ : ℝ}
    (hd : ∀ v ∈ closedBall (0 : F) ρ, DifferentiableAt ℝ e v)
    (hb : ∀ v ∈ closedBall (0 : F) ρ, ‖fderiv ℝ e v‖ ≤ 1 / 2) :
    ∀ v ∈ closedBall (0 : F) ρ, ∀ w ∈ closedBall (0 : F) ρ, ‖e v - e w‖ ≤ ‖v - w‖ / 2 := by
  intro v hv w hw
  have h := (convex_closedBall (0 : F) ρ).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => hd x hx) hb hw hv
  linarith

end Deriv

end

end Finsler.ContractionInverse
