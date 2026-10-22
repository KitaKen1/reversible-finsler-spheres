module

public import Finsler.Geometry.SegmentAtlas
public import Finsler.Analysis.SobolevC1Continuity

/-! Joint continuity of coordinate geodesic segments. The segment from y to z is the first
component of the flow at the unit jet (y, V/‖V‖) and time ‖V‖t, so its velocity is
‖V‖·∂_τΦ. Off the diagonal both are continuous in (y, z, t) by continuity of V and of the flow and
its derivative. On the diagonal V → 0, and a bound M for the flow derivative on a compact set of
jets and times gives ‖geo − y‖ ≤ M‖V‖|t| and ‖velocity‖ ≤ M‖V‖, so the segment tends to the constant
curve with zero velocity. -/

@[expose] public section

namespace Finsler.SegmentContinuity

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.EikonalChart
open Finsler.ExpInverseRegularity Finsler.ChartTransfer Finsler.SegmentAtlas
open Function Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

/-- The flow as a function on pairs. -/
def flowMap (q : (Coordinates n × Coordinates n) × ℝ) : Coordinates n × Coordinates n :=
  D.Φ q.1 q.2

theorem flowMap_contDiff : ContDiff ℝ 3 (flowMap D) := D.smooth

/-- The unit initial jet of the segment from y to z. -/
def jetOf (y z : Coordinates n) : Coordinates n × Coordinates n :=
  (y, ‖expInv D y z‖⁻¹ • expInv D y z)

/-- The velocity of the coordinate geodesic segment. -/
def geoVel (y z : Coordinates n) (t : ℝ) : Coordinates n :=
  ‖expInv D y z‖ •
    (fderiv ℝ (flowMap D) (jetOf D y z, ‖expInv D y z‖ * t)
      ((0 : Coordinates n × Coordinates n), (1 : ℝ))).1

theorem geo_eq (y z : Coordinates n) (t : ℝ) :
    geo F D y z t = (flowMap D (jetOf D y z, ‖expInv D y z‖ * t)).1 := rfl

/-- The time derivative of the flow component along a jet. -/
theorem flow_fst_hasDerivAt (w : Coordinates n × Coordinates n) (s t : ℝ) :
    HasDerivAt (fun τ : ℝ => (flowMap D (w, s * τ)).1)
      (s • (fderiv ℝ (flowMap D) (w, s * t) ((0 : Coordinates n × Coordinates n), (1 : ℝ))).1) t := by
  have hd : HasDerivAt (fun τ : ℝ => (w, s * τ)) ((0 : Coordinates n × Coordinates n), s) t := by
    have h2 : HasDerivAt (fun τ : ℝ => s * τ) s t := by
      simpa using (hasDerivAt_id t).const_mul s
    exact (hasDerivAt_const t w).prodMk h2
  have hΦ : HasFDerivAt (flowMap D) (fderiv ℝ (flowMap D) (w, s * t)) (w, s * t) :=
    ((flowMap_contDiff D).differentiable (by norm_num) _).hasFDerivAt
  have h := hΦ.comp_hasDerivAt t hd
  have h1 := (hasFDerivAt_fst (𝕜 := ℝ) (p := flowMap D (w, s * t))).comp_hasDerivAt t h
  have he : ((0 : Coordinates n × Coordinates n), s) =
      s • ((0 : Coordinates n × Coordinates n), (1 : ℝ)) := by simp
  rw [he, map_smul] at h1
  exact h1

theorem geo_hasDerivAt (y z : Coordinates n) (t : ℝ) :
    HasDerivAt (geo F D y z) (geoVel D y z t) t :=
  flow_fst_hasDerivAt D (jetOf D y z) ‖expInv D y z‖ t

/-- A bound for the derivative of the flow on a compact set of jets and times. -/
theorem exists_flow_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ closedBall y₀ r,
    ∀ u ∈ closedBall (0 : Coordinates n) 1, ∀ τ ∈ Icc (-2 : ℝ) 2,
      ‖fderiv ℝ (flowMap D) ((y, u), τ)‖ ≤ M := by
  have hK : IsCompact ((closedBall y₀ r ×ˢ closedBall (0 : Coordinates n) 1) ×ˢ Icc (-2 : ℝ) 2) :=
    ((isCompact_closedBall y₀ r).prod (isCompact_closedBall 0 1)).prod isCompact_Icc
  have hc : Continuous (fderiv ℝ (flowMap D)) :=
    (flowMap_contDiff D).continuous_fderiv (by norm_num)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro y hy u hu τ hτ
  exact (hM ((y, u), τ) ⟨⟨hy, hu⟩, hτ⟩).trans (le_max_left _ _)

theorem norm_unit_le (v : Coordinates n) : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
  rcases eq_or_ne v 0 with h | h
  · simp [h]
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

/-- Displacement and velocity bounds of a segment in terms of ‖V‖. -/
theorem norm_geo_sub_le {M : ℝ}
    (hM : ∀ y ∈ closedBall y₀ r, ∀ u ∈ closedBall (0 : Coordinates n) 1,
      ∀ τ ∈ Icc (-2 : ℝ) 2, ‖fderiv ℝ (flowMap D) ((y, u), τ)‖ ≤ M)
    {y z : Coordinates n} (hy : y ∈ closedBall y₀ r) {t : ℝ}
    (ht : |‖expInv D y z‖ * t| ≤ 2) :
    ‖geo F D y z t - y‖ ≤ M * |‖expInv D y z‖ * t| ∧ ‖geoVel D y z t‖ ≤ ‖expInv D y z‖ * M := by
  set s := ‖expInv D y z‖ with hs
  set u := ‖expInv D y z‖⁻¹ • expInv D y z with hu
  have hu1 : u ∈ closedBall (0 : Coordinates n) 1 := by
    rw [mem_closedBall, dist_zero_right]
    exact norm_unit_le _
  have hbound : ∀ τ ∈ Icc (-2 : ℝ) 2,
      ‖(fderiv ℝ (flowMap D) ((y, u), τ) ((0 : Coordinates n × Coordinates n), (1 : ℝ))).1‖ ≤ M := by
    intro τ hτ
    calc _ ≤ ‖fderiv ℝ (flowMap D) ((y, u), τ) ((0 : Coordinates n × Coordinates n), (1 : ℝ))‖ :=
          norm_fst_le _
      _ ≤ ‖fderiv ℝ (flowMap D) ((y, u), τ)‖ *
          ‖((0 : Coordinates n × Coordinates n), (1 : ℝ))‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * 1 := by
          apply mul_le_mul (hM y hy u hu1 τ hτ) (by simp) (norm_nonneg _)
          exact (norm_nonneg _).trans (hM y hy u hu1 τ hτ)
      _ = M := mul_one M
  have hst : s * t ∈ Icc (-2 : ℝ) 2 := abs_le.mp ht
  constructor
  · have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun τ : ℝ => (flowMap D ((y, u), 1 * τ)).1)
      (f' := fun τ => 1 • (fderiv ℝ (flowMap D) ((y, u), 1 * τ)
        ((0 : Coordinates n × Coordinates n), (1 : ℝ))).1)
      (s := Icc (-2 : ℝ) 2) (C := M)
      (fun τ _ => (flow_fst_hasDerivAt D (y, u) 1 τ).hasDerivWithinAt)
      (fun τ hτ => by simpa using hbound τ hτ) (convex_Icc _ _)
      (show (0 : ℝ) ∈ Icc (-2 : ℝ) 2 by constructor <;> norm_num) hst
    simp only [one_mul] at hmv
    have h0 : (flowMap D ((y, u), 0)).1 = y := by
      simp [flowMap, D.init]
    rw [h0, sub_zero, Real.norm_eq_abs] at hmv
    exact hmv
  · unfold geoVel
    rw [norm_smul, norm_norm]
    exact mul_le_mul_of_nonneg_left (hbound _ hst) (norm_nonneg _)

theorem expInv_continuousAt {y₁ z₁ : Coordinates n} (hy₁ : y₁ ∈ ball y₀ r)
    (hz₁ : ‖z₁ - y₁‖ < D.ρ / 2) :
    ContinuousAt (fun q : Coordinates n × Coordinates n => expInv D q.1 q.2) (y₁, z₁) := by
  have hmem : invDomain D ∈ 𝓝 (y₁, z₁) := by
    have h1 : ∀ᶠ q : Coordinates n × Coordinates n in 𝓝 (y₁, z₁), q.1 ∈ ball y₀ r :=
      continuousAt_fst.preimage_mem_nhds (isOpen_ball.mem_nhds hy₁)
    have h2 : ∀ᶠ q : Coordinates n × Coordinates n in 𝓝 (y₁, z₁), ‖q.2 - q.1‖ < D.ρ / 2 :=
      (continuous_norm.comp (continuous_snd.sub continuous_fst)).continuousAt.eventually
        (gt_mem_nhds hz₁)
    filter_upwards [h1, h2] with q hq1 hq2
    exact ⟨ball_subset_closedBall hq1, hq2.le⟩
  exact (expInv_continuousOn D).continuousAt hmem

/-- Joint continuity of the segment and its velocity in (y, z, t). -/
theorem geo_continuousAt {y₁ z₁ : Coordinates n} (hy₁ : y₁ ∈ ball y₀ r)
    (hz₁ : ‖z₁ - y₁‖ < D.ρ / 2) (t₀ : ℝ) :
    ContinuousAt (fun q : (Coordinates n × Coordinates n) × ℝ => geo F D q.1.1 q.1.2 q.2)
      ((y₁, z₁), t₀) ∧
    ContinuousAt (fun q : (Coordinates n × Coordinates n) × ℝ => geoVel D q.1.1 q.1.2 q.2)
      ((y₁, z₁), t₀) := by
  have hV : ContinuousAt (fun q : (Coordinates n × Coordinates n) × ℝ => expInv D q.1.1 q.1.2)
      ((y₁, z₁), t₀) :=
    ContinuousAt.comp_of_eq (g := fun q : Coordinates n × Coordinates n => expInv D q.1 q.2)
      (expInv_continuousAt D hy₁ hz₁) continuousAt_fst rfl
  have hN : ContinuousAt (fun q : (Coordinates n × Coordinates n) × ℝ => ‖expInv D q.1.1 q.1.2‖)
      ((y₁, z₁), t₀) := hV.norm
  have hFd : Continuous (fderiv ℝ (flowMap D)) :=
    (flowMap_contDiff D).continuous_fderiv (by norm_num)
  have hF : Continuous (flowMap D) := (flowMap_contDiff D).continuous
  rcases eq_or_ne z₁ y₁ with hzy | hzy
  · subst hzy
    have hy₁' : z₁ ∈ closedBall y₀ r := ball_subset_closedBall hy₁
    obtain ⟨M, hM0, hM⟩ := exists_flow_bound D
    have hV0 : expInv D z₁ z₁ = 0 := expInv_self D hy₁'
    -- eventually the start point is in the closed ball and the flow time is small
    have hev : ∀ᶠ q : (Coordinates n × Coordinates n) × ℝ in 𝓝 ((z₁, z₁), t₀),
        q.1.1 ∈ closedBall y₀ r ∧ |‖expInv D q.1.1 q.1.2‖ * q.2| ≤ 2 := by
      have h1 : ∀ᶠ q : (Coordinates n × Coordinates n) × ℝ in 𝓝 ((z₁, z₁), t₀),
          q.1.1 ∈ ball y₀ r :=
        (continuous_fst.comp continuous_fst).continuousAt.preimage_mem_nhds
          (isOpen_ball.mem_nhds hy₁)
      have hc : ContinuousAt (fun q : (Coordinates n × Coordinates n) × ℝ =>
          |‖expInv D q.1.1 q.1.2‖ * q.2|) ((z₁, z₁), t₀) := (hN.mul continuousAt_snd).abs
      have h2 : ∀ᶠ q : (Coordinates n × Coordinates n) × ℝ in 𝓝 ((z₁, z₁), t₀),
          |‖expInv D q.1.1 q.1.2‖ * q.2| < 2 := by
        apply hc.eventually (gt_mem_nhds _)
        simp [hV0]
      filter_upwards [h1, h2] with q hq1 hq2
      exact ⟨ball_subset_closedBall hq1, hq2.le⟩
    constructor
    · rw [ContinuousAt, geo_self D hy₁' t₀, tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun q : (Coordinates n × Coordinates n) × ℝ =>
          M * |‖expInv D q.1.1 q.1.2‖ * q.2| + ‖q.1.1 - z₁‖) (𝓝 ((z₁, z₁), t₀)) (𝓝 0) := by
        have hc : ContinuousAt (fun q : (Coordinates n × Coordinates n) × ℝ =>
            M * |‖expInv D q.1.1 q.1.2‖ * q.2| + ‖q.1.1 - z₁‖) ((z₁, z₁), t₀) :=
          (continuousAt_const.mul (hN.mul continuousAt_snd).abs).add
            ((continuous_fst.comp continuous_fst).continuousAt.sub continuousAt_const).norm
        have h := hc.tendsto
        simpa [hV0] using h
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
      filter_upwards [hev] with q hq
      have hb := (norm_geo_sub_le D hM hq.1 hq.2).1
      calc ‖geo F D q.1.1 q.1.2 q.2 - z₁‖ =
            ‖(geo F D q.1.1 q.1.2 q.2 - q.1.1) + (q.1.1 - z₁)‖ := by congr 1; abel
        _ ≤ ‖geo F D q.1.1 q.1.2 q.2 - q.1.1‖ + ‖q.1.1 - z₁‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    · have hv0 : geoVel D z₁ z₁ t₀ = 0 := by
        simp [geoVel, hV0]
      rw [ContinuousAt, hv0, tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun q : (Coordinates n × Coordinates n) × ℝ =>
          ‖expInv D q.1.1 q.1.2‖ * M) (𝓝 ((z₁, z₁), t₀)) (𝓝 0) := by
        have h := hN.tendsto.mul_const M
        simpa [hV0] using h
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
      filter_upwards [hev] with q hq
      rw [sub_zero]
      exact (norm_geo_sub_le D hM hq.1 hq.2).2
  · have hy₁' : y₁ ∈ closedBall y₀ r := ball_subset_closedBall hy₁
    have hV0 : expInv D y₁ z₁ ≠ 0 := expInv_ne_zero D hy₁' hz₁.le hzy
    have hN0 : ‖expInv D y₁ z₁‖ ≠ 0 := norm_ne_zero_iff.mpr hV0
    have hjet : ContinuousAt (fun q : (Coordinates n × Coordinates n) × ℝ =>
        (jetOf D q.1.1 q.1.2, ‖expInv D q.1.1 q.1.2‖ * q.2)) ((y₁, z₁), t₀) :=
      ((continuous_fst.comp continuous_fst).continuousAt.prodMk ((hN.inv₀ hN0).smul hV)).prodMk
        (hN.mul continuousAt_snd)
    constructor
    · exact continuous_fst.continuousAt.comp (hF.continuousAt.comp hjet)
    · have h1 : ContinuousAt (fun q : (Coordinates n × Coordinates n) × ℝ =>
          fderiv ℝ (flowMap D) (jetOf D q.1.1 q.1.2, ‖expInv D q.1.1 q.1.2‖ * q.2)
            ((0 : Coordinates n × Coordinates n), (1 : ℝ))) ((y₁, z₁), t₀) :=
        (hFd.continuousAt.comp hjet).clm_apply continuousAt_const
      exact hN.smul (continuous_fst.continuousAt.comp h1)

section Sphere

open Finsler.AmbientCalibrator Finsler.SphereRetraction Finsler.AmbientEnergyRegularity

variable {F' : ReversibleMetric n}

/-- The velocity of the segment of a package. -/
def segVel (S : SegChart F') (P Q : Sphere n) (t : ℝ) : Ambient n :=
  fderiv ℝ (inverseAmbient S.p)
    (geo F' S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) t)
    (geoVel S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) t)

theorem chart_dist_lt (S : SegChart F') {P Q : Sphere n} (hP : P ∈ segDom S)
    (hQ : ‖(Q : Ambient n) - P‖ < S.δ) :
    ‖chartNormalize S.p (Q : Ambient n) - extChartAt (𝓡 n) S.p P‖ < S.D.ρ / 2 := by
  obtain ⟨-, -, hzb⟩ := good_of_dom S hP (hQ.trans_le S.hδη)
  rw [← dist_eq_norm]
  exact mem_ball.mp hzb

/-- The segment stays in the chart target on [0,1]. -/
theorem geo_mem_target (S : SegChart F') {P Q : Sphere n} (hP : P ∈ segDom S)
    (hQ : ‖(Q : Ambient n) - P‖ < S.δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    geo F' S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) t ∈
      (extChartAt (𝓡 n) S.p).target := by
  have hy := chart_mem_closedBall S hP
  have hz := chart_dist_lt S hP hQ
  by_cases hzy : chartNormalize S.p (Q : Ambient n) = extChartAt (𝓡 n) S.p P
  · rw [hzy, geo_self S.D hy]
    exact S.hball hy
  · have hV := expInv_ne_zero S.D hy hz.le hzy
    have hVρ : ‖expInv S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n))‖ <
        S.D.ρ := by
      have := norm_expInv_le S.D hy hz.le
      linarith
    obtain ⟨-, hT, -, -, -, -⟩ := geodesic_facts S.D hy hV hVρ
    exact hT t ht

theorem segCurve_hasDerivAt (S : SegChart F') {P Q : Sphere n} (hP : P ∈ segDom S)
    (hQ : ‖(Q : Ambient n) - P‖ < S.δ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (segCurve S P Q) (segVel S P Q t) t := by
  have hT := geo_mem_target S hP hQ ht
  exact ((inverseAmbient_smoothAt S.p hT).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
    t (geo_hasDerivAt S.D _ _ t)

/-- Joint continuity of the segment of a package and its velocity in (P, Q, t). -/
theorem segCurve_continuousAt (S : SegChart F') {P₀ Q₀ : Sphere n} (hP₀ : P₀ ∈ segDom S)
    (hQ₀ : ‖(Q₀ : Ambient n) - P₀‖ < S.δ) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun q : (Sphere n × Sphere n) × ℝ => segCurve S q.1.1 q.1.2 q.2)
      ((P₀, Q₀), t₀) ∧
    ContinuousAt (fun q : (Sphere n × Sphere n) × ℝ => segVel S q.1.1 q.1.2 q.2)
      ((P₀, Q₀), t₀) := by
  have hyb : extChartAt (𝓡 n) S.p P₀ ∈ ball S.y₀ S.r := ball_subset_ball S.hr'r hP₀.2
  obtain ⟨hQ0, hQs, -⟩ := good_of_dom S hP₀ (hQ₀.trans_le S.hδη)
  have hz := chart_dist_lt S hP₀ hQ₀
  obtain ⟨hg, hgv⟩ := geo_continuousAt S.D hyb hz t₀
  have hcoord : ContinuousAt (fun q : (Sphere n × Sphere n) × ℝ =>
      ((extChartAt (𝓡 n) S.p q.1.1, chartNormalize S.p (q.1.2 : Ambient n)), q.2))
      ((P₀, Q₀), t₀) := by
    have h1 : ContinuousAt (fun q : (Sphere n × Sphere n) × ℝ => extChartAt (𝓡 n) S.p q.1.1)
        ((P₀, Q₀), t₀) :=
      ContinuousAt.comp_of_eq (g := extChartAt (𝓡 n) S.p)
        (f := fun q : (Sphere n × Sphere n) × ℝ => q.1.1) (continuousAt_extChartAt' hP₀.1)
        (continuous_fst.comp continuous_fst).continuousAt rfl
    have h2 : ContinuousAt (fun q : (Sphere n × Sphere n) × ℝ =>
        chartNormalize S.p (q.1.2 : Ambient n)) ((P₀, Q₀), t₀) :=
      ContinuousAt.comp_of_eq (g := chartNormalize S.p)
        (f := fun q : (Sphere n × Sphere n) × ℝ => (q.1.2 : Ambient n))
        (chartNormalize_smoothAt S.p hQ0 hQs).continuousAt
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).continuousAt rfl
    exact (h1.prodMk h2).prodMk continuousAt_snd
  have hT := geo_mem_target S hP₀ hQ₀ ht₀
  have hφ : ContinuousAt (inverseAmbient S.p)
      (geo F' S.D (extChartAt (𝓡 n) S.p P₀) (chartNormalize S.p (Q₀ : Ambient n)) t₀) :=
    (inverseAmbient_smoothAt S.p hT).continuousAt
  have hDφ : ContinuousAt (fderiv ℝ (inverseAmbient S.p))
      (geo F' S.D (extChartAt (𝓡 n) S.p P₀) (chartNormalize S.p (Q₀ : Ambient n)) t₀) :=
    ((inverseAmbient_smoothAt S.p hT).fderiv_right (m := 0) (by simp)).continuousAt
  have hgeo : ContinuousAt (fun q : (Sphere n × Sphere n) × ℝ =>
      geo F' S.D (extChartAt (𝓡 n) S.p q.1.1) (chartNormalize S.p (q.1.2 : Ambient n)) q.2)
      ((P₀, Q₀), t₀) :=
    ContinuousAt.comp (g := fun q : (Coordinates n × Coordinates n) × ℝ => geo F' S.D q.1.1 q.1.2 q.2)
      (f := fun q : (Sphere n × Sphere n) × ℝ =>
        ((extChartAt (𝓡 n) S.p q.1.1, chartNormalize S.p (q.1.2 : Ambient n)), q.2))
      (x := ((P₀, Q₀), t₀)) hg hcoord
  have hvel : ContinuousAt (fun q : (Sphere n × Sphere n) × ℝ =>
      geoVel S.D (extChartAt (𝓡 n) S.p q.1.1) (chartNormalize S.p (q.1.2 : Ambient n)) q.2)
      ((P₀, Q₀), t₀) :=
    ContinuousAt.comp (g := fun q : (Coordinates n × Coordinates n) × ℝ => geoVel S.D q.1.1 q.1.2 q.2)
      (f := fun q : (Sphere n × Sphere n) × ℝ =>
        ((extChartAt (𝓡 n) S.p q.1.1, chartNormalize S.p (q.1.2 : Ambient n)), q.2))
      (x := ((P₀, Q₀), t₀)) hgv hcoord
  have hc1 := ContinuousAt.comp (g := inverseAmbient S.p)
    (f := fun q : (Sphere n × Sphere n) × ℝ =>
      geo F' S.D (extChartAt (𝓡 n) S.p q.1.1) (chartNormalize S.p (q.1.2 : Ambient n)) q.2)
    (x := ((P₀, Q₀), t₀)) hφ hgeo
  have hc2 := (ContinuousAt.comp (g := fderiv ℝ (inverseAmbient S.p))
    (f := fun q : (Sphere n × Sphere n) × ℝ =>
      geo F' S.D (extChartAt (𝓡 n) S.p q.1.1) (chartNormalize S.p (q.1.2 : Ambient n)) q.2)
    (x := ((P₀, Q₀), t₀)) hDφ hgeo).clm_apply hvel
  exact ⟨hc1, hc2⟩

/-- Along a coordinate segment the coordinate density is the energy F²(y, V). -/
theorem geo_energy_const {y z : Coordinates n} (hy : y ∈ closedBall y₀ r)
    (hz : ‖z - y‖ < D.ρ / 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    coordinateLagrangian F p (geo F D y z t, geoVel D y z t) =
      coordinateLagrangian F p (y, expInv D y z) := by
  have hvel : geoVel D y z t = deriv (geo F D y z) t := (geo_hasDerivAt D y z t).deriv.symm
  rw [hvel]
  by_cases hzy : z = y
  · subst hzy
    have hgeo : geo F D z z = fun _ => z := funext fun s => geo_self D hy s
    rw [hgeo, deriv_const, expInv_self D hy]
  · have hV := expInv_ne_zero D hy hz.le hzy
    have hVρ : ‖expInv D y z‖ < D.ρ := by
      have := norm_expInv_le D hy hz.le
      linarith
    obtain ⟨hC, hT, hD, hA, h0, h0'⟩ := geodesic_facts D hy hV hVρ
    have h : coordinateLagrangian F p (curveJet (geo F D y z) t) =
        coordinateLagrangian F p (curveJet (geo F D y z) 0) :=
      Finsler.ChartPath.density_const F p hC hT hD hA ht
    have h0g : geo F D y z 0 = y := h0
    have h0g' : deriv (geo F D y z) 0 = expInv D y z := h0'
    change coordinateLagrangian F p (curveJet (geo F D y z) t) = _
    rw [h]
    simp only [curveJet, h0g, h0g']

end Sphere

section GlobalPath

open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.ChartPath
open Finsler.SobolevOfPrimitive Finsler.SobolevC1Continuity Finsler.AmbientCalibrator
open Finsler.SphereRetraction Finsler.AmbientLagrangian Finsler.AmbientEnergyRegularity
open Finsler.SphereDistance (minEnergy pathsBetween)
open MeasureTheory

variable {F' : ReversibleMetric n}

theorem segCurve_zero (S : SegChart F') {P : Sphere n} (hP : P ∈ segDom S) (Q : Sphere n) :
    segCurve S P Q 0 = P := by
  unfold segCurve geo scaledGeodesic
  rw [mul_zero, S.D.init]
  exact inverseAmbient_chart_of_dom S hP

theorem segCurve_one (S : SegChart F') {P Q : Sphere n} (hP : P ∈ segDom S)
    (hQ : ‖(Q : Ambient n) - P‖ < S.δ) : segCurve S P Q 1 = Q := by
  have hy := chart_mem_closedBall S hP
  have hz := chart_dist_lt S hP hQ
  obtain ⟨-, hQs, -⟩ := good_of_dom S hP (hQ.trans_le S.hδη)
  rw [normalize_inclusion] at hQs
  have hQz : inverseAmbient S.p (chartNormalize S.p (Q : Ambient n)) = Q :=
    inverseAmbient_chartNormalize hQs
  unfold segCurve
  by_cases hzy : chartNormalize S.p (Q : Ambient n) = extChartAt (𝓡 n) S.p P
  · rw [hzy, geo_self S.D hy]
    rw [hzy] at hQz
    exact hQz
  · have h1 : geo F' S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) 1 =
        chartNormalize S.p (Q : Ambient n) := geodesic_endpoint S.D hy hz.le hzy
    rw [h1, hQz]

theorem segCurve_energy (S : SegChart F') {P Q : Sphere n} (hP : P ∈ segDom S)
    (hQ : ‖(Q : Ambient n) - P‖ < S.δ) :
    ∫ t in (0 : ℝ)..1, lagrangian F' (segCurve S P Q t, segVel S P Q t) = minEnergy F' P Q := by
  have hy := chart_mem_closedBall S hP
  have hz := chart_dist_lt S hP hQ
  have hconst : EqOn (fun t => lagrangian F' (segCurve S P Q t, segVel S P Q t))
      (fun _ => coordinateLagrangian F' S.p (extChartAt (𝓡 n) S.p P,
        expInv S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n))))
      (uIcc (0 : ℝ) 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact geo_energy_const S.D hy hz ht
  rw [intervalIntegral.integral_congr hconst, intervalIntegral.integral_const, sub_zero, one_smul,
    minE_of_dom S hP hQ]
  rfl

/-- The global H¹ short-segment map: for endpoints within a uniform δ the segment is an H¹ sphere
path from P to Q realizing the minimal energy, and it depends continuously on (P, Q) in H¹. -/
theorem exists_segment_path (F : ReversibleMetric n) :
    ∃ δ > 0, ∃ segPath : Sphere n → Sphere n → Space n,
      (∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
        segPath P Q ∈ pathsBetween n P Q ∧ pathEnergy F (segPath P Q) = minEnergy F P Q) ∧
      ∀ P₀ Q₀ : Sphere n, ‖(Q₀ : Ambient n) - P₀‖ < δ →
        ContinuousAt (fun x : Sphere n × Sphere n => segPath x.1 x.2) (P₀, Q₀) := by
  obtain ⟨δ, hδ, ι, S, hcover, hδS, hcons⟩ := exists_segment_atlas F
  choose idx hidx hPidx using hcover
  have hdata : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContinuousOn (segCurve (S (idx P)) P Q) (Icc 0 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivAt (segCurve (S (idx P)) P Q) (segVel (S (idx P)) P Q t) t) ∧
      ContinuousOn (segVel (S (idx P)) P Q) (Icc 0 1) := by
    intro P Q hQ
    have hQS := hQ.trans_le (hδS _ (hidx P))
    refine ⟨fun t ht => (segCurve_hasDerivAt _ (hPidx P) hQS ht).continuousAt.continuousWithinAt,
      fun t ht => segCurve_hasDerivAt _ (hPidx P) hQS (Ioo_subset_Icc_self ht), fun t ht => ?_⟩
    have h := (segCurve_continuousAt _ (hPidx P) hQS ht).2
    have h' : ContinuousAt (segVel (S (idx P)) P Q) t :=
      ContinuousAt.comp (g := fun q : (Sphere n × Sphere n) × ℝ =>
        segVel (S (idx P)) q.1.1 q.1.2 q.2) (f := fun s : ℝ => ((P, Q), s)) (x := t) h
        (continuousAt_const.prodMk continuousAt_id)
    exact h'.continuousWithinAt
  classical
  let segPath : Sphere n → Sphere n → Space n := fun P Q =>
    if h : ‖(Q : Ambient n) - P‖ < δ then
      ofC1 (hdata P Q h).1 (hdata P Q h).2.1 (hdata P Q h).2.2 else 0
  have hseg : ∀ P Q : Sphere n, ∀ h : ‖(Q : Ambient n) - P‖ < δ,
      segPath P Q = ofC1 (hdata P Q h).1 (hdata P Q h).2.1 (hdata P Q h).2.2 := by
    intro P Q h
    simp [segPath, h]
  refine ⟨δ, hδ, segPath, ?_, ?_⟩
  · intro P Q hQ
    have hQS := hQ.trans_le (hδS _ (hidx P))
    rw [hseg P Q hQ]
    refine ⟨?_, ?_⟩
    · have h := ofC1_mem (hdata P Q hQ).1 (hdata P Q hQ).2.1 (hdata P Q hQ).2.2
        (fun t _ => mem_sphere_zero_iff_norm.mp (inverseSphere _ _).2)
      rwa [segCurve_zero _ (hPidx P), segCurve_one _ (hPidx P) hQS] at h
    · rw [pathEnergy_ofC1]
      exact segCurve_energy _ (hPidx P) hQS
  · intro P₀ Q₀ hQ₀
    have hP₀T : P₀ ∈ segDom (S (idx P₀)) := hPidx P₀
    have hQ₀T := hQ₀.trans_le (hδS _ (hidx P₀))
    have hev1 : ∀ᶠ x : Sphere n × Sphere n in 𝓝 (P₀, Q₀), x.1 ∈ segDom (S (idx P₀)) :=
      continuousAt_fst.preimage_mem_nhds ((segDom_isOpen F (S (idx P₀))).mem_nhds hP₀T)
    have hev2 : ∀ᶠ x : Sphere n × Sphere n in 𝓝 (P₀, Q₀), ‖(x.2 : Ambient n) - x.1‖ < δ :=
      (continuous_norm.comp ((continuous_subtype_val.comp continuous_snd).sub
        (continuous_subtype_val.comp continuous_fst))).continuousAt.eventually (gt_mem_nhds hQ₀)
    apply tendsto_of_uniform (c := fun x t => segCurve (S (idx P₀)) x.1 x.2 t)
      (c' := fun x t => segVel (S (idx P₀)) x.1 x.2 t)
      (c₀ := segCurve (S (idx P₀)) P₀ Q₀) (c₀' := segVel (S (idx P₀)) P₀ Q₀)
    · filter_upwards [hev1, hev2] with x hx1 hx2
      show value (segPath x.1 x.2) =ᵐ[intervalMeasure] _
      rw [hseg x.1 x.2 hx2]
      have h1 : value (ofC1 (hdata x.1 x.2 hx2).1 (hdata x.1 x.2 hx2).2.1 (hdata x.1 x.2 hx2).2.2)
          =ᵐ[intervalMeasure] segCurve (S (idx x.1)) x.1 x.2 :=
        value_ofPrimitive_ae _ _ _
      filter_upwards [h1, ae_restrict_mem measurableSet_Ioo] with t ht1 ht2
      rw [ht1]
      exact hcons (idx P₀) (hidx P₀) (idx x.1) (hidx x.1) x.1 x.2 hx1 (hPidx x.1) hx2 t
        (Ioo_subset_Icc_self ht2)
    · filter_upwards [hev1, hev2] with x hx1 hx2
      show velocity (segPath x.1 x.2) =ᵐ[intervalMeasure] _
      rw [hseg x.1 x.2 hx2]
      filter_upwards [velocity_ofC1_ae (hdata x.1 x.2 hx2).1 (hdata x.1 x.2 hx2).2.1
        (hdata x.1 x.2 hx2).2.2, ae_restrict_mem measurableSet_Ioo] with t ht1 ht2
      rw [ht1]
      have hQT := hx2.trans_le (hδS _ (hidx P₀))
      have hQI := hx2.trans_le (hδS _ (hidx x.1))
      have hA := segCurve_hasDerivAt _ (hPidx x.1) hQI (Ioo_subset_Icc_self ht2)
      have hB := segCurve_hasDerivAt (S (idx P₀)) hx1 hQT (Ioo_subset_Icc_self ht2)
      have heq : segCurve (S (idx x.1)) x.1 x.2 =ᶠ[𝓝 t] segCurve (S (idx P₀)) x.1 x.2 := by
        filter_upwards [Ioo_mem_nhds ht2.1 ht2.2] with s hs
        exact hcons (idx P₀) (hidx P₀) (idx x.1) (hidx x.1) x.1 x.2 hx1 (hPidx x.1) hx2 s
          (Ioo_subset_Icc_self hs)
      exact hA.unique (hB.congr_of_eventuallyEq heq)
    · show value (segPath P₀ Q₀) =ᵐ[intervalMeasure] _
      rw [hseg P₀ Q₀ hQ₀]
      exact value_ofPrimitive_ae _ _ _
    · show velocity (segPath P₀ Q₀) =ᵐ[intervalMeasure] _
      rw [hseg P₀ Q₀ hQ₀]
      exact velocity_ofC1_ae _ _ _
    · intro ε hε
      have h1 := eventually_uniform (x₀ := (P₀, Q₀))
        (f := fun x t => segCurve (S (idx P₀)) x.1 x.2 t)
        (fun t ht => (segCurve_continuousAt _ hP₀T hQ₀T ht).1) hε
      have h2 := eventually_uniform (x₀ := (P₀, Q₀))
        (f := fun x t => segVel (S (idx P₀)) x.1 x.2 t)
        (fun t ht => (segCurve_continuousAt _ hP₀T hQ₀T ht).2) hε
      filter_upwards [h1, h2] with x hx1 hx2 t ht
      exact ⟨(hx1 t (Ioo_subset_Icc_self ht)).le, (hx2 t (Ioo_subset_Icc_self ht)).le⟩

end GlobalPath

end

end Finsler.SegmentContinuity
