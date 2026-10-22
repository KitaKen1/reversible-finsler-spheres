module

public import Finsler.Geometry.ChartTransfer
public import Finsler.Geometry.ShortSegments

/-! Energy estimates for short segments. The coordinate Lagrangian dominates c₀‖Dφ(y)w‖² by the
round comparison of the metric, and the chart is a left inverse of the inverse chart, so on a
compact ball of the chart target c‖w‖² ≤ F²(y,w). Transport to a second chart preserves the
Lagrangian of the jet. Along a coordinate geodesic the density is constant, so the ambient image of
the segment stays within √(F²(y,V)/c₀) of its start point. -/

@[expose] public section

namespace Finsler.SegmentEstimates

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.EikonalChart
open Finsler.SphereRetraction Finsler.AmbientEnergyRegularity Finsler.AmbientLagrangian
open Finsler.AmbientCalibrator Finsler.ChartTransfer Finsler.ChartPath
open Function Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- The coordinate Lagrangian dominates the squared ambient velocity. -/
theorem coordinateLagrangian_ge {c₀ : ℝ}
    (hb : ∀ q : Total n, c₀ * ‖ambientVector n q‖ ^ 2 ≤ F.value q ^ 2) (p : Sphere n)
    {y : Coordinates n} (hy : y ∈ (extChartAt (𝓡 n) p).target) (w : Coordinates n) :
    c₀ * ‖fderiv ℝ (inverseAmbient p) y w‖ ^ 2 ≤ coordinateLagrangian F p (y, w) := by
  have hj := inverseAmbient_jet p hy w
  have h2 : fderiv ℝ (inverseAmbient p) y w =
      ambientVector n ⟨inverseSphere p y,
        mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y w⟩ :=
    congrArg Prod.snd hj
  have hL : coordinateLagrangian F p (y, w) = F.value ⟨inverseSphere p y,
        mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y w⟩ ^ 2 := by
    change lagrangian F (jetMap (inverseAmbient p) (y, w)) = _
    rw [hj, lagrangian_ambientPair]
  rw [h2, hL]
  exact hb _

/-- A uniform lower bound for the coordinate Lagrangian on a compact ball of the chart target. -/
theorem exists_coordinateLagrangian_lower {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
    (hball : closedBall y₀ r ⊆ (extChartAt (𝓡 n) p).target) :
    ∃ c > 0, ∀ y ∈ closedBall y₀ r, ∀ w : Coordinates n,
      c * ‖w‖ ^ 2 ≤ coordinateLagrangian F p (y, w) := by
  obtain ⟨c₀, C₀, hc₀, -, hb⟩ := Finsler.MetricComparison.exists_squared_bounds F
  have hcont : ContinuousOn (fun y => fderiv ℝ (chartNormalize p) (inverseAmbient p y))
      (closedBall y₀ r) := by
    intro y hy
    have hyt := hball hy
    have h1 : ContinuousAt (fderiv ℝ (chartNormalize p)) (inverseAmbient p y) :=
      ((chartNormalize_smoothAt p (inverseAmbient_ne_zero p y)
        (normalize_inverseAmbient_mem p hyt)).fderiv_right (m := 0) (by simp)).continuousAt
    exact (h1.comp (inverseAmbient_smoothAt p hyt).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall y₀ r).exists_bound_of_continuousOn hcont
  set M' := max M 0 + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  refine ⟨c₀ / M' ^ 2, by positivity, ?_⟩
  intro y hy w
  have hyt := hball hy
  have hw : w = fderiv ℝ (chartNormalize p) (inverseAmbient p y)
      (fderiv ℝ (inverseAmbient p) y w) := by
    have h := congrArg (fun T : Coordinates n →L[ℝ] Coordinates n => T w)
      (fderiv_chartNormalize_comp p hyt)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h
    exact h.symm
  have hnorm : ‖w‖ ≤ M' * ‖fderiv ℝ (inverseAmbient p) y w‖ := by
    calc ‖w‖ = ‖fderiv ℝ (chartNormalize p) (inverseAmbient p y)
          (fderiv ℝ (inverseAmbient p) y w)‖ := by rw [← hw]
      _ ≤ ‖fderiv ℝ (chartNormalize p) (inverseAmbient p y)‖ *
          ‖fderiv ℝ (inverseAmbient p) y w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M' * ‖fderiv ℝ (inverseAmbient p) y w‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          have := hM y hy
          have : M ≤ max M 0 := le_max_left _ _
          linarith
  have hL := coordinateLagrangian_ge F (fun q => (hb q).1) p hyt w
  have hsq : ‖w‖ ^ 2 ≤ M' ^ 2 * ‖fderiv ℝ (inverseAmbient p) y w‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc c₀ / M' ^ 2 * ‖w‖ ^ 2 ≤ c₀ / M' ^ 2 * (M' ^ 2 * ‖fderiv ℝ (inverseAmbient p) y w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = c₀ * ‖fderiv ℝ (inverseAmbient p) y w‖ ^ 2 := by
        field_simp
    _ ≤ _ := hL

section Transfer

variable {p₁ p₂ : Sphere n} {x : ℝ → Coordinates n} {t : ℝ}
  (hx : ContDiffAt ℝ 2 x t) (hxt : x t ∈ (extChartAt (𝓡 n) p₁).target)
  (hs : inverseSphere p₁ (x t) ∈ (extChartAt (𝓡 n) p₂).source)

include hx hxt hs in
/-- Transport to a second chart preserves the Lagrangian of the jet. -/
theorem transfer_lagrangian :
    coordinateLagrangian F p₂ (curveJet (transferCurve p₁ p₂ x) t) =
      coordinateLagrangian F p₁ (curveJet x t) := by
  have hx2 := transfer_contDiffAt hx hxt hs
  have hx2t := transfer_mem_target (x := x) (t := t) hs
  have h2 : jetMap (inverseAmbient p₂) (curveJet (transferCurve p₁ p₂ x) t) =
      curveJet (inverseAmbient p₂ ∘ transferCurve p₁ p₂ x) t :=
    jetMap_curveJet ((inverseAmbient_smoothAt p₂ hx2t).differentiableAt (by simp))
      (hx2.differentiableAt (by norm_num))
  have h1 : jetMap (inverseAmbient p₁) (curveJet x t) = curveJet (inverseAmbient p₁ ∘ x) t :=
    jetMap_curveJet ((inverseAmbient_smoothAt p₁ hxt).differentiableAt (by simp))
      (hx.differentiableAt (by norm_num))
  have he : curveJet (inverseAmbient p₂ ∘ transferCurve p₁ p₂ x) t =
      curveJet (inverseAmbient p₁ ∘ x) t :=
    (curveJet_congr_eventually (inverseAmbient_transfer_eventually hx hxt hs)).eq_of_nhds
  change lagrangian F (jetMap (inverseAmbient p₂) (curveJet (transferCurve p₁ p₂ x) t)) =
    lagrangian F (jetMap (inverseAmbient p₁) (curveJet x t))
  rw [h2, h1, he]

end Transfer

/-- The ambient image of a coordinate geodesic segment stays within √(F²(y,v)/c₀) of its start. -/
theorem norm_segment_sub_le {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hb : ∀ q : Total n, c₀ * ‖ambientVector n q‖ ^ 2 ≤ F.value q ^ 2) (p : Sphere n)
    {γ : ℝ → Coordinates n}
    (hC2 : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 γ t)
    (hT : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt (𝓡 n) p).target)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hacc : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (deriv γ) t = spray (coordinateLagrangian F p) (curveJet γ t)) :
    ∀ t ∈ Icc (0 : ℝ) 1, ‖inverseAmbient p (γ t) - inverseAmbient p (γ 0)‖ ≤
      Real.sqrt (coordinateLagrangian F p (curveJet γ 0) / c₀) := by
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s => inverseAmbient p (γ s))
      (fderiv ℝ (inverseAmbient p) (γ t) (deriv γ t)) t := by
    intro t ht
    exact ((inverseAmbient_smoothAt p (hT t ht)).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      t (((hC2 t ht).differentiableAt (by norm_num)).hasDerivAt)
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1, ‖fderiv ℝ (inverseAmbient p) (γ t) (deriv γ t)‖ ≤
      Real.sqrt (coordinateLagrangian F p (curveJet γ 0) / c₀) := by
    intro t ht
    have ht' := Ico_subset_Icc_self ht
    have h1 := coordinateLagrangian_ge F hb p (hT t ht') (deriv γ t)
    have h2 := density_const F p hC2 hT hV hacc ht'
    have h3 : coordinateLagrangian F p (γ t, deriv γ t) = coordinateLagrangian F p (curveJet γ t) := rfl
    rw [h3, h2] at h1
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc₀]
    linarith
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun s => inverseAmbient p (γ s)) (a := 0) (b := 1)
    (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound
  intro t ht
  have ht1 := h t ht
  have hs : 0 ≤ Real.sqrt (coordinateLagrangian F p (curveJet γ 0) / c₀) := Real.sqrt_nonneg _
  calc ‖inverseAmbient p (γ t) - inverseAmbient p (γ 0)‖ ≤
        Real.sqrt (coordinateLagrangian F p (curveJet γ 0) / c₀) * (t - 0) := ht1
    _ ≤ Real.sqrt (coordinateLagrangian F p (curveJet γ 0) / c₀) := by
        have : t - 0 ≤ 1 := by linarith [ht.2]
        nlinarith [ht.1]

end

end Finsler.SegmentEstimates
