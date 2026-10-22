module

public import Finsler.Geometry.AmbientCalibrator
public import Finsler.Analysis.OdeUnique

/-! Coordinate geodesics are chart independent. A C² curve with vanishing Euler–Lagrange
residual and injective velocity Hessian has the spray as acceleration. The coordinate residual
of a curve in a sphere chart is the ambient residual of its image composed with the chart
differential; the second inverse chart factors through the first via the transition map near the
curve, so a coordinate geodesic of one chart, transported to another chart, has vanishing
residual there and is a coordinate geodesic of the second chart. Uniqueness for the jet ODE
identifies a coordinate geodesic with the exp-data geodesic of the same initial jet. -/

@[expose] public section

namespace Finsler.ChartTransfer

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.EikonalChart
open Finsler.SphereRetraction Finsler.AmbientEnergyRegularity Finsler.AmbientLagrangian
open Finsler.AmbientCalibrator Finsler.OdeUnique
open Function Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem curveJet_hasDerivAt {x : ℝ → E} {t : ℝ} (hx : ContDiffAt ℝ 2 x t) :
    HasDerivAt (curveJet x) (deriv x t, deriv (deriv x) t) t := by
  have h1 : HasDerivAt x (deriv x t) t :=
    (hx.differentiableAt (by norm_num)).hasDerivAt
  have h2 : HasDerivAt (deriv x) (deriv (deriv x) t) t := by
    have hd : ContDiffAt ℝ 1 (deriv x) t := hx.derivWithin (m := 1) (by norm_num)
    exact (hd.differentiableAt (by norm_num)).hasDerivAt
  exact h1.prodMk h2

/-- A C² curve with vanishing residual and injective velocity Hessian has the spray as
acceleration. -/
theorem spray_of_residual_eq_zero (L : E × E → ℝ) {x : ℝ → E} {t : ℝ}
    (hx : ContDiffAt ℝ 2 x t) (hL : ContDiffAt ℝ 2 L (curveJet x t))
    (hH : Injective (velocityHessian L (curveJet x t)))
    (hres : residual L x t = 0) :
    deriv (deriv x) t = spray L (curveJet x t) := by
  have hd : DifferentiableAt ℝ (velocityTerm L) (curveJet x t) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ L) (curveJet x t) := hL.fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun y => (fderiv ℝ L y).comp
        (ContinuousLinearMap.inr ℝ E E)) (curveJet x t) := h1.clm_comp contDiffAt_const
    exact h2.differentiableAt (by norm_num)
  have hm : HasDerivAt (momentum L x)
      (fderiv ℝ (velocityTerm L) (curveJet x t) (deriv x t, deriv (deriv x) t)) t :=
    hd.hasFDerivAt.comp_hasDerivAt t (curveJet_hasDerivAt hx)
  rw [Finsler.EulerCovariance.residual, hm.deriv] at hres
  have hz : (curveJet x t).2 = deriv x t := rfl
  have h := velocityTerm_fderiv_apply L hL (z := curveJet x t) (deriv (deriv x) t)
  rw [hz] at h
  rw [h] at hres
  apply hH
  rw [velocityHessian_spray L _ hH]
  rw [sub_eq_zero] at hres
  rw [hres]
  abel

end General

variable {n : ℕ} (F : ReversibleMetric n)

theorem inverseAmbient_ne_zero (p : Sphere n) (y : Coordinates n) : inverseAmbient p y ≠ 0 := by
  intro h
  have h1 : ‖inverseAmbient p y‖ = 1 := mem_sphere_zero_iff_norm.mp (inverseSphere p y).2
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem normalize_inverseAmbient_mem (p : Sphere n) {y : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) :
    normalize (inverseAmbient p y) ∈ (extChartAt (𝓡 n) p).source := by
  rw [inverseAmbient, normalize_inclusion]
  exact (extChartAt (𝓡 n) p).map_target hy

/-- The chart is a left inverse of the inverse chart at the level of differentials. -/
theorem fderiv_chartNormalize_comp (p : Sphere n) {y : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) :
    (fderiv ℝ (chartNormalize p) (inverseAmbient p y)).comp (fderiv ℝ (inverseAmbient p) y) =
      ContinuousLinearMap.id ℝ (Coordinates n) := by
  have hev : (chartNormalize p ∘ inverseAmbient p) =ᶠ[𝓝 y] id := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hy] with y' hy'
    exact chartNormalize_inverseAmbient hy'
  have h1 : DifferentiableAt ℝ (chartNormalize p) (inverseAmbient p y) :=
    (chartNormalize_smoothAt p (inverseAmbient_ne_zero p y)
      (normalize_inverseAmbient_mem p hy)).differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (inverseAmbient p) y :=
    (inverseAmbient_smoothAt p hy).differentiableAt (by simp)
  rw [← fderiv_comp y h1 h2, hev.fderiv_eq, fderiv_id]

theorem fderiv_inverseAmbient_injective (p : Sphere n) {y : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) : Injective (fderiv ℝ (inverseAmbient p) y) := by
  intro a b hab
  have h := congrArg (fun T : Coordinates n →L[ℝ] Coordinates n => T a)
    (fderiv_chartNormalize_comp p hy)
  have h' := congrArg (fun T : Coordinates n →L[ℝ] Coordinates n => T b)
    (fderiv_chartNormalize_comp p hy)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at h h'
  rw [← h, ← h', hab]

/-- The coordinate residual of an arbitrary C² curve with nonzero velocity in a chart is the
ambient residual of its image composed with the chart differential. -/
theorem coordinate_residual_local (p : Sphere n) {x : ℝ → Coordinates n} {t : ℝ}
    (hx : ContDiffAt ℝ 2 x t) (hxt : x t ∈ (extChartAt (𝓡 n) p).target) (hv : deriv x t ≠ 0) :
    residual (coordinateLagrangian F p) x t =
      (residual (lagrangian F) (inverseAmbient p ∘ x) t).comp
        (fderiv ℝ (inverseAmbient p) (x t)) := by
  have hφ := (inverseAmbient_smoothAt p hxt).of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)
  have hL : ContDiffAt ℝ 2 (lagrangian F) (jetMap (inverseAmbient p) (curveJet x t)) :=
    (lagrangian_smoothAt F (inverseAmbient_jet_mem_slitDomain p (z := curveJet x t) hxt hv)).of_le
      (by simp)
  exact residual_pullback hφ hx hL

/-- The transport of a coordinate curve of the chart at p₁ to the chart at p₂. -/
def transferCurve (p₁ p₂ : Sphere n) (x : ℝ → Coordinates n) (s : ℝ) : Coordinates n :=
  chartNormalize p₂ (inverseAmbient p₁ (x s))

section Transfer

variable {p₁ p₂ : Sphere n} {x : ℝ → Coordinates n} {t : ℝ}
  (hx : ContDiffAt ℝ 2 x t) (hxt : x t ∈ (extChartAt (𝓡 n) p₁).target)
  (hs : inverseSphere p₁ (x t) ∈ (extChartAt (𝓡 n) p₂).source)

include hx hxt hs

theorem transfer_contDiffAt : ContDiffAt ℝ 2 (transferCurve p₁ p₂ x) t := by
  have hΓ : ContDiffAt ℝ 2 (fun s => inverseAmbient p₁ (x s)) t :=
    ((inverseAmbient_smoothAt p₁ hxt).of_le (by simp)).comp t hx
  have hs' : normalize (inverseAmbient p₁ (x t)) ∈ (extChartAt (𝓡 n) p₂).source := by
    rw [inverseAmbient, normalize_inclusion]
    exact hs
  have hc : ContDiffAt ℝ 2 (chartNormalize p₂) (inverseAmbient p₁ (x t)) :=
    (chartNormalize_smoothAt p₂ (inverseAmbient_ne_zero p₁ (x t)) hs').of_le (by simp)
  exact hc.comp t hΓ

omit hx hxt in
theorem transfer_mem_target : transferCurve p₁ p₂ x t ∈ (extChartAt (𝓡 n) p₂).target := by
  apply chartNormalize_mem_target
  rw [inverseAmbient, normalize_inclusion]
  exact hs

/-- Near t the second inverse chart of the transported curve is the image curve. -/
theorem inverseAmbient_transfer_eventually :
    (fun s => inverseAmbient p₂ (transferCurve p₁ p₂ x s)) =ᶠ[𝓝 t]
      fun s => inverseAmbient p₁ (x s) := by
  have hc : ContinuousAt (fun s => inverseSphere p₁ (x s)) t :=
    (inverseSphere_smoothAt p₁ hxt).continuousAt.comp hx.continuousAt
  filter_upwards [hc.preimage_mem_nhds ((isOpen_extChartAt_source p₂).mem_nhds hs)] with s hs'
  exact inverseAmbient_chartNormalize hs'

theorem transfer_deriv_ne_zero (hv : deriv x t ≠ 0) : deriv (transferCurve p₁ p₂ x) t ≠ 0 := by
  intro h0
  have hx2 := transfer_contDiffAt hx hxt hs
  have hd2 : HasDerivAt (transferCurve p₁ p₂ x) (deriv (transferCurve p₁ p₂ x) t) t :=
    (hx2.differentiableAt (by norm_num)).hasDerivAt
  have hφ2 : DifferentiableAt ℝ (inverseAmbient p₂) (transferCurve p₁ p₂ x t) :=
    (inverseAmbient_smoothAt p₂ (transfer_mem_target hs)).differentiableAt (by simp)
  have hA : HasDerivAt (fun s => inverseAmbient p₂ (transferCurve p₁ p₂ x s))
      (fderiv ℝ (inverseAmbient p₂) (transferCurve p₁ p₂ x t)
        (deriv (transferCurve p₁ p₂ x) t)) t :=
    hφ2.hasFDerivAt.comp_hasDerivAt t hd2
  have hφ1 : DifferentiableAt ℝ (inverseAmbient p₁) (x t) :=
    (inverseAmbient_smoothAt p₁ hxt).differentiableAt (by simp)
  have hB : HasDerivAt (fun s => inverseAmbient p₁ (x s))
      (fderiv ℝ (inverseAmbient p₁) (x t) (deriv x t)) t :=
    hφ1.hasFDerivAt.comp_hasDerivAt t ((hx.differentiableAt (by norm_num)).hasDerivAt)
  have heq := (hA.congr_of_eventuallyEq
    (inverseAmbient_transfer_eventually hx hxt hs).symm).unique hB
  rw [h0, map_zero] at heq
  apply hv
  apply fderiv_inverseAmbient_injective p₁ hxt
  rw [map_zero]
  exact heq.symm

/-- The residual of the transported curve vanishes when the residual of the curve does. -/
theorem transfer_residual_eq_zero (hv : deriv x t ≠ 0)
    (hres : residual (coordinateLagrangian F p₁) x t = 0) :
    residual (coordinateLagrangian F p₂) (transferCurve p₁ p₂ x) t = 0 := by
  have hx2 := transfer_contDiffAt hx hxt hs
  have hx2t := transfer_mem_target (x := x) (t := t) hs
  have hv2 := transfer_deriv_ne_zero hx hxt hs hv
  rw [coordinate_residual_local F p₂ hx2 hx2t hv2]
  have hcongr : residual (lagrangian F) (inverseAmbient p₂ ∘ transferCurve p₁ p₂ x) t =
      residual (lagrangian F) (inverseAmbient p₁ ∘ x) t :=
    residual_congr_eventually (lagrangian F) (inverseAmbient_transfer_eventually hx hxt hs)
  rw [hcongr]
  have hpt : inverseAmbient p₂ (transferCurve p₁ p₂ x t) = inverseAmbient p₁ (x t) :=
    (inverseAmbient_transfer_eventually hx hxt hs).eq_of_nhds
  have hsrc1 : inverseSphere p₂ (transferCurve p₁ p₂ x t) ∈ (extChartAt (𝓡 n) p₁).source := by
    have he : inverseSphere p₂ (transferCurve p₁ p₂ x t) = inverseSphere p₁ (x t) :=
      Subtype.ext hpt
    rw [he]
    exact (extChartAt (𝓡 n) p₁).map_target hxt
  have hev : inverseAmbient p₂ =ᶠ[𝓝 (transferCurve p₁ p₂ x t)]
      (inverseAmbient p₁ ∘ fun y' => chartNormalize p₁ (inverseAmbient p₂ y')) := by
    have hc : ContinuousAt (inverseSphere p₂) (transferCurve p₁ p₂ x t) :=
      (inverseSphere_smoothAt p₂ hx2t).continuousAt
    filter_upwards [hc.preimage_mem_nhds ((isOpen_extChartAt_source p₁).mem_nhds hsrc1)]
      with y' hy'
    exact (inverseAmbient_chartNormalize hy').symm
  have hτ : chartNormalize p₁ (inverseAmbient p₂ (transferCurve p₁ p₂ x t)) = x t := by
    rw [hpt]
    exact chartNormalize_inverseAmbient hxt
  have hdτ : DifferentiableAt ℝ (fun y' => chartNormalize p₁ (inverseAmbient p₂ y'))
      (transferCurve p₁ p₂ x t) := by
    have hc1 : DifferentiableAt ℝ (chartNormalize p₁) (inverseAmbient p₂ (transferCurve p₁ p₂ x t)) := by
      rw [hpt]
      exact (chartNormalize_smoothAt p₁ (inverseAmbient_ne_zero p₁ (x t))
        (normalize_inverseAmbient_mem p₁ hxt)).differentiableAt (by simp)
    exact hc1.comp _ ((inverseAmbient_smoothAt p₂ hx2t).differentiableAt (by simp))
  have hA1 : HasFDerivAt (inverseAmbient p₁) (fderiv ℝ (inverseAmbient p₁) (x t))
      (chartNormalize p₁ (inverseAmbient p₂ (transferCurve p₁ p₂ x t))) := by
    rw [hτ]
    exact ((inverseAmbient_smoothAt p₁ hxt).differentiableAt (by simp)).hasFDerivAt
  have hcomp := (hA1.comp (transferCurve p₁ p₂ x t) hdτ.hasFDerivAt).congr_of_eventuallyEq hev
  rw [hcomp.fderiv, ← ContinuousLinearMap.comp_assoc,
    ← coordinate_residual_local F p₁ hx hxt hv, hres, ContinuousLinearMap.zero_comp]

/-- A coordinate geodesic of the first chart, transported to the second chart, has the spray of
the second chart as acceleration. -/
theorem transfer_spray (hv : deriv x t ≠ 0)
    (hacc : deriv (deriv x) t = spray (coordinateLagrangian F p₁) (curveJet x t)) :
    deriv (deriv (transferCurve p₁ p₂ x)) t =
      spray (coordinateLagrangian F p₂) (curveJet (transferCurve p₁ p₂ x) t) := by
  have hres := coordinate_residual_eq_zero F p₁ hx hxt hv hacc
  have hres2 := transfer_residual_eq_zero F hx hxt hs hv hres
  have hx2 := transfer_contDiffAt hx hxt hs
  have hx2t := transfer_mem_target (x := x) (t := t) hs
  have hv2 := transfer_deriv_ne_zero hx hxt hs hv
  exact spray_of_residual_eq_zero _ hx2
    ((coordinateLagrangian_smoothAt_nonzero F p₂ (z := curveJet _ t) hx2t hv2).of_le (by simp))
    (coordinate_velocityHessian_injective F p₂ hx2t hv2) hres2

end Transfer

/-- A coordinate geodesic on [0,1] is the exp-data geodesic with the same initial jet. -/
theorem eq_scaledGeodesic {p : Sphere n} {y₀ : Coordinates n} {r : ℝ} (D : ExpData F p y₀ r)
    {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {v : Coordinates n} (hv : v ≠ 0)
    (hvρ : ‖v‖ < D.ρ) {x : ℝ → Coordinates n}
    (hx : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 x t)
    (hxt : ∀ t ∈ Icc (0 : ℝ) 1, x t ∈ (extChartAt (𝓡 n) p).target)
    (hxv : ∀ t ∈ Icc (0 : ℝ) 1, deriv x t ≠ 0)
    (hacc : ∀ t ∈ Icc (0 : ℝ) 1,
      deriv (deriv x) t = spray (coordinateLagrangian F p) (curveJet x t))
    (h0 : x 0 = y) (h0' : deriv x 0 = v) :
    ∀ t ∈ Icc (0 : ℝ) 1, x t = scaledGeodesic D.Φ (y, ‖v‖⁻¹ • v) ‖v‖ t := by
  obtain ⟨hγC, -, -, hγacc, hγ0, hγ0'⟩ := geodesic_facts D hy hv hvρ
  have heq : EqOn (curveJet x) (curveJet (scaledGeodesic D.Φ (y, ‖v‖⁻¹ • v) ‖v‖)) (Icc 0 1) := by
    apply eqOn_of_contDiffAt
      (v := fun z : Coordinates n × Coordinates n => (z.2, spray (coordinateLagrangian F p) z))
    · intro t ht
      have hs := coordinate_spray_contDiffAt F p (hxt t ht) (hxv t ht) 1
      rw [Nat.cast_one] at hs
      exact contDiffAt_snd.prodMk hs
    · intro t ht
      have h := curveJet_hasDerivAt (hx t ht)
      rw [hacc t ht] at h
      exact h
    · intro t ht
      have h := curveJet_hasDerivAt (hγC t ht)
      rw [hγacc t ht] at h
      exact h
    · simp only [curveJet, h0, h0', hγ0, hγ0']
  intro t ht
  exact congrArg Prod.fst (heq ht)

/-- The coordinate geodesic from y to z. -/
def geo {p : Sphere n} {y₀ : Coordinates n} {r : ℝ} (D : ExpData F p y₀ r)
    (y z : Coordinates n) : ℝ → Coordinates n :=
  scaledGeodesic D.Φ (y, ‖expInv D y z‖⁻¹ • expInv D y z) ‖expInv D y z‖

section Consistency

variable {F} {p₁ p₂ : Sphere n} {y₀₁ y₀₂ : Coordinates n} {r₁ r₂ : ℝ}
  (D₁ : ExpData F p₁ y₀₁ r₁) (D₂ : ExpData F p₂ y₀₂ r₂)

/-- Chart independence of short segments: the coordinate geodesic segment of the first chart and
the one of the second chart between the same sphere points coincide, provided the first stays in
the second chart and its transported initial velocity is inside the exp-data ball. -/
theorem segment_transfer {y₁ z₁ : Coordinates n} (hy₁ : y₁ ∈ closedBall y₀₁ r₁)
    (hz₁ : ‖z₁ - y₁‖ < D₁.ρ / 2) (hne : z₁ ≠ y₁)
    {y₂ z₂ : Coordinates n} (hy₂ : y₂ ∈ closedBall y₀₂ r₂) (hz₂ : ‖z₂ - y₂‖ ≤ D₂.ρ / 2)
    (hy₁₂ : chartNormalize p₂ (inverseAmbient p₁ y₁) = y₂)
    (hz₁₂ : chartNormalize p₂ (inverseAmbient p₁ z₁) = z₂)
    (hsrc : ∀ t ∈ Icc (0 : ℝ) 1,
      inverseSphere p₁ (geo F D₁ y₁ z₁ t) ∈ (extChartAt (𝓡 n) p₂).source)
    (hsmall : ‖deriv (transferCurve p₁ p₂ (geo F D₁ y₁ z₁)) 0‖ < D₂.ρ) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      inverseAmbient p₂ (geo F D₂ y₂ z₂ t) = inverseAmbient p₁ (geo F D₁ y₁ z₁ t) := by
  have hV₁ : expInv D₁ y₁ z₁ ≠ 0 := expInv_ne_zero D₁ hy₁ hz₁.le hne
  have hV₁ρ : ‖expInv D₁ y₁ z₁‖ < D₁.ρ := by
    have h := norm_expInv_le D₁ hy₁ hz₁.le
    linarith
  obtain ⟨hC, hT, hD, hA, h0, -⟩ := geodesic_facts D₁ hy₁ hV₁ hV₁ρ
  have h0g : geo F D₁ y₁ z₁ 0 = y₁ := h0
  have h1g : geo F D₁ y₁ z₁ 1 = z₁ := geodesic_endpoint D₁ hy₁ hz₁.le hne
  have hx2C : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 (transferCurve p₁ p₂ (geo F D₁ y₁ z₁)) t :=
    fun t ht => transfer_contDiffAt (hC t ht) (hT t ht) (hsrc t ht)
  have hx2T : ∀ t ∈ Icc (0 : ℝ) 1, transferCurve p₁ p₂ (geo F D₁ y₁ z₁) t ∈ (extChartAt (𝓡 n) p₂).target :=
    fun t ht => transfer_mem_target (hsrc t ht)
  have hx2D : ∀ t ∈ Icc (0 : ℝ) 1, deriv (transferCurve p₁ p₂ (geo F D₁ y₁ z₁)) t ≠ 0 :=
    fun t ht => transfer_deriv_ne_zero (hC t ht) (hT t ht) (hsrc t ht) (hD t ht)
  have hx2A : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv (transferCurve p₁ p₂ (geo F D₁ y₁ z₁))) t =
      spray (coordinateLagrangian F p₂) (curveJet (transferCurve p₁ p₂ (geo F D₁ y₁ z₁)) t) :=
    fun t ht => transfer_spray F (hC t ht) (hT t ht) (hsrc t ht) (hD t ht) (hA t ht)
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have hx20 : transferCurve p₁ p₂ (geo F D₁ y₁ z₁) 0 = y₂ := by
    unfold transferCurve
    rw [h0g, hy₁₂]
  set v₂ := deriv (transferCurve p₁ p₂ (geo F D₁ y₁ z₁)) 0 with hv₂
  have hv₂0 : v₂ ≠ 0 := hx2D 0 h0mem
  have heq := eq_scaledGeodesic F D₂ hy₂ hv₂0 hsmall hx2C hx2T hx2D hx2A hx20 rfl
  -- the endpoint identifies the initial velocity with the exp inverse
  have hend : transferCurve p₁ p₂ (geo F D₁ y₁ z₁) 1 = z₂ := by
    unfold transferCurve
    rw [h1g, hz₁₂]
  have hexp : y₂ + v₂ + Finsler.RadialRemainder.rad D₂.R y₂ v₂ = z₂ := by
    rw [← Finsler.ExpInverseRegularity.expMap_eq D₂ hy₂, ← hend, heq 1 h1mem]
    simp only [scaledGeodesic, mul_one, Finsler.ExpInverseRegularity.expMap]
  obtain ⟨hVmem, hVspec⟩ := expInv_spec D₂ hy₂ hz₂
  have hvmem : v₂ ∈ closedBall (0 : Coordinates n) D₂.ρ := by
    rw [mem_closedBall, dist_zero_right]
    exact hsmall.le
  have hvV : v₂ = expInv D₂ y₂ z₂ :=
    eq_of_exp_eq D₂ hy₂ hvmem hVmem (hexp.trans hVspec.symm)
  intro t ht
  have h1 := heq t ht
  rw [hvV] at h1
  have h2 : geo F D₂ y₂ z₂ t = transferCurve p₁ p₂ (geo F D₁ y₁ z₁) t := h1.symm
  rw [h2]
  exact inverseAmbient_chartNormalize (hsrc t ht)

end Consistency

end

end Finsler.ChartTransfer
