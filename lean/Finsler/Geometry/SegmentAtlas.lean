module

public import Finsler.Geometry.SegmentEstimates

/-! Chart packages for short segments and their compatibility. A package around a chart carries
uniform radii: for start points y in a ball, ambient points within η of the start point lie in the
good set of the calibrator, the minimal energy to endpoints within δ is F²(y, V(y, chart Q)), and
the coordinate Lagrangian is bounded below. On the overlap of two packages the segments coincide:
the ambient image of a segment stays within √(e(P,Q)/c₀) of P, so it lies in the second chart, and
the transported initial velocity has F² = e(P,Q), so it is small; `segment_transfer` applies. -/

@[expose] public section

namespace Finsler.SegmentAtlas

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.ExpBounds Finsler.RadialRemainder Finsler.ParamTaylor
open Finsler.CoordinateExpInverse Finsler.EikonalChart Finsler.ShortCalibrator
open Finsler.SphereRetraction Finsler.AmbientEnergyRegularity Finsler.AmbientLagrangian
open Finsler.AmbientCalibrator Finsler.ShortSegments Finsler.ChartTransfer Finsler.ChartPath
open Finsler.SegmentEstimates Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SphereDistance Finsler.SobolevAffine
open Function Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

/-- The geodesic path from y to z ≠ y, with its continuous representative. -/
theorem exists_geodesic_path_rep {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {z : Coordinates n}
    (hz : ‖z - y‖ ≤ D.ρ / 2) (hne : z ≠ y) :
    ∃ w : Space n, w ∈ pathsBetween n (inverseAmbient p y) (inverseAmbient p z) ∧
      pathEnergy F w = coordinateLagrangian F p (y, expInv D y z) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, continuousRepresentative w t = inverseAmbient p (geo F D y z t) := by
  set v := expInv D y z with hvdef
  have hv0 : v ≠ 0 := expInv_ne_zero D hy hz hne
  have hvρ : ‖v‖ ≤ D.ρ := by simpa using (expInv_spec D hy hz).1
  have hsτ : |‖v‖| < D.τ := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact lt_of_le_of_lt hvρ D.ρ_lt_τ
  have hs : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  set u : Coordinates n × Coordinates n := (y, ‖v‖⁻¹ • v) with hu
  have hmem : u ∈ unitJets y₀ r := normalize_mem_unitJets hy hv0
  have hΦ : ContDiff ℝ ((2 : ℕ) + 1)
      (fun q : (Coordinates n × Coordinates n) × ℝ => D.Φ q.1 q.2) := by
    exact_mod_cast D.smooth
  have hode := D.ode u hmem
  refine ⟨chartPath p (fun _ ht => scaledGeodesic_mem F p hode (abs_mul_lt hsτ ht))
      (continuousOn_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
      (hasDerivAt_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
      (deriv_continuousOn_of_C2 fun _ _ =>
        (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt), ?_, ?_, ?_⟩
  · have h := chartPath_mem p (fun _ ht => scaledGeodesic_mem F p hode (abs_mul_lt hsτ ht))
      (continuousOn_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
      (hasDerivAt_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
      (deriv_continuousOn_of_C2 fun _ _ =>
        (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
    rwa [scaledGeodesic_zero (D.init u), geodesic_endpoint D hy hz hne] at h
  · rw [pathEnergy_scaledGeodesic_eq F p hΦ (by norm_num) (D.init u) D.τ_pos hode hs hsτ]
    simp only [hu, smul_smul, mul_inv_cancel₀ hs, one_smul]
  · intro t ht
    exact representative_ofC1 _ _ _ ht

theorem geo_self {y : Coordinates n} (hy : y ∈ closedBall y₀ r) (t : ℝ) : geo F D y y t = y := by
  unfold geo scaledGeodesic
  rw [expInv_self D hy]
  simp only [norm_zero, inv_zero, smul_zero, zero_mul]
  have h := D.init (y, 0)
  rw [h]

end

noncomputable section

/-- A chart package for short segments. -/
structure SegChart (F : ReversibleMetric n) where
  p : Sphere n
  y₀ : Coordinates n
  r : ℝ
  D : ExpData F p y₀ r
  r' : ℝ
  η : ℝ
  δ : ℝ
  c : ℝ
  hr : 0 < r
  hball : closedBall y₀ r ⊆ (extChartAt (𝓡 n) p).target
  hr' : 0 < r'
  hr'r : r' ≤ r
  hη : 0 < η
  hδ : 0 < δ
  hδη : δ ≤ η
  hδ1 : δ ≤ 1
  hc : 0 < c
  good : ∀ y ∈ ball y₀ r', ∀ X : Ambient n, ‖X - inverseAmbient p y‖ < η → X ∈ goodSet D y
  minE : ∀ y ∈ ball y₀ r', ∀ Q : Sphere n, ‖(Q : Ambient n) - inverseAmbient p y‖ < δ →
    minEnergy F (inverseAmbient p y) Q = ambientEnergy D y Q
  lower : ∀ y ∈ closedBall y₀ r, ∀ w : Coordinates n,
    c * ‖w‖ ^ 2 ≤ coordinateLagrangian F p (y, w)

theorem exists_segChart (F : ReversibleMetric n) (P₀ : Sphere n) :
    ∃ S : SegChart F, S.p = P₀ ∧ S.y₀ = extChartAt (𝓡 n) P₀ P₀ := by
  set y₀ := extChartAt (𝓡 n) P₀ P₀ with hy₀def
  have hy₀ : y₀ ∈ (extChartAt (𝓡 n) P₀).target :=
    (extChartAt (𝓡 n) P₀).map_source (mem_extChartAt_source P₀)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp ((isOpen_extChartAt_target P₀).mem_nhds hy₀)
  have hr : (0 : ℝ) < ε / 2 := by positivity
  have hball : closedBall y₀ (ε / 2) ⊆ (extChartAt (𝓡 n) P₀).target :=
    (closedBall_subset_ball (by linarith)).trans hεsub
  obtain ⟨D⟩ := exists_expData F P₀ hball
  obtain ⟨r', hr', hr'r, rIn, rOut, hrIn, hlt, huni⟩ := exists_uniform_radius D hr hball
  obtain ⟨c, hc, hlow⟩ := exists_minEnergy_lower F
  obtain ⟨C, hC, hup⟩ := exists_minEnergy_upper F
  obtain ⟨δ, hδ, hδ1, hδr, hδC⟩ := exists_small_scale hc hC hrIn
  obtain ⟨cl, hcl, hlower⟩ := exists_coordinateLagrangian_lower F hball
  have hgood : ∀ y ∈ ball y₀ r', ∀ X : Ambient n, ‖X - inverseAmbient P₀ y‖ < rOut →
      X ∈ goodSet D y := by
    intro y hy X hX
    apply huni y hy
    rw [mem_closedBall, dist_eq_norm]
    exact hX.le
  have hminE : ∀ y ∈ ball y₀ r', ∀ Q : Sphere n,
      ‖(Q : Ambient n) - inverseAmbient P₀ y‖ < δ →
      minEnergy F (inverseAmbient P₀ y) Q = ambientEnergy D y Q := by
    intro y hy Q hQ
    have hy' : y ∈ closedBall y₀ (ε / 2) :=
      mem_closedBall.mpr ((mem_ball.mp hy).le.trans hr'r)
    have hyt : y ∈ (extChartAt (𝓡 n) P₀).target := hball hy'
    obtain ⟨hne, hmin⟩ := hup _ _ (norm_inverseAmbient y) (norm_sphere Q) (hQ.le.trans hδ1)
    let χ : ContDiffBump (inverseAmbient P₀ y) := ⟨rIn, rOut, hrIn, hlt⟩
    have hsub : closedBall (inverseAmbient P₀ y) χ.rOut ⊆ goodSet D y := huni y hy
    have hsmall : minEnergy F (inverseAmbient P₀ y) Q < c * χ.rIn ^ 2 :=
      hmin.trans_lt (hδC _ (norm_nonneg _) hQ)
    have hle := ambientEnergy_le_minEnergy D hc hlow hy' hyt χ hsub hne hsmall
    have hQgood : (Q : Ambient n) ∈ goodSet D y := by
      apply hsub
      rw [mem_closedBall, dist_eq_norm]
      exact (hQ.trans_le (hδr.trans hlt.le)).le
    obtain ⟨w, hw, hwE⟩ := exists_path_energy_eq D hy' hyt hne hQgood
    exact le_antisymm ((minEnergy_le F hw).trans hwE.le) hle
  exact ⟨⟨P₀, y₀, ε / 2, D, r', rOut, δ, cl, hr, hball, hr', hr'r, hrIn.trans hlt, hδ,
    hδr.trans hlt.le, hδ1, hcl, hgood, hminE, hlower⟩, rfl, rfl⟩

/-- The start points of a package. -/
def segDom {F : ReversibleMetric n} (S : SegChart F) : Set (Sphere n) :=
  {P | P ∈ (extChartAt (𝓡 n) S.p).source ∧ extChartAt (𝓡 n) S.p P ∈ ball S.y₀ S.r'}

/-- The segment of a package from P to Q. -/
def segCurve {F : ReversibleMetric n} (S : SegChart F) (P Q : Sphere n) (t : ℝ) :
    Ambient n :=
  inverseAmbient S.p (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) t)

section Overlap

variable {F : ReversibleMetric n}

theorem inverseAmbient_chart_of_dom (S : SegChart F) {P : Sphere n} (hP : P ∈ segDom S) :
    inverseAmbient S.p (extChartAt (𝓡 n) S.p P) = P := by
  unfold inverseAmbient inverseSphere
  rw [(extChartAt (𝓡 n) S.p).left_inv hP.1]

theorem chartNormalize_sphere (S : SegChart F) (P : Sphere n) :
    chartNormalize S.p (P : Ambient n) = extChartAt (𝓡 n) S.p P := by
  unfold chartNormalize
  rw [normalize_inclusion]

theorem chart_mem_closedBall (S : SegChart F) {P : Sphere n} (hP : P ∈ segDom S) :
    extChartAt (𝓡 n) S.p P ∈ closedBall S.y₀ S.r :=
  mem_closedBall.mpr ((mem_ball.mp hP.2).le.trans S.hr'r)

theorem good_of_dom (S : SegChart F) {P : Sphere n} (hP : P ∈ segDom S) {X : Ambient n}
    (hX : ‖X - P‖ < S.η) : X ∈ goodSet S.D (extChartAt (𝓡 n) S.p P) := by
  apply S.good _ hP.2
  rw [inverseAmbient_chart_of_dom S hP]
  exact hX

theorem minE_of_dom (S : SegChart F) {P : Sphere n} (hP : P ∈ segDom S) {Q : Sphere n}
    (hQ : ‖(Q : Ambient n) - P‖ < S.δ) :
    minEnergy F P Q = ambientEnergy S.D (extChartAt (𝓡 n) S.p P) Q := by
  have h := S.minE _ hP.2 Q (by rw [inverseAmbient_chart_of_dom S hP]; exact hQ)
  rwa [inverseAmbient_chart_of_dom S hP] at h

/-- On the overlap of two packages the segments coincide. -/
theorem seg_eq {S T : SegChart F} {P Q : Sphere n} (hPS : P ∈ segDom S) (hPT : P ∈ segDom T)
    (hQS : ‖(Q : Ambient n) - P‖ < S.δ) (hQT : ‖(Q : Ambient n) - P‖ < T.δ)
    {c₀ C : ℝ} (hc₀ : 0 < c₀) (hb : ∀ q : Total n, c₀ * ‖ambientVector n q‖ ^ 2 ≤ F.value q ^ 2)
    (hup : minEnergy F P Q ≤ C * ‖(Q : Ambient n) - P‖ ^ 2)
    (hη : C * ‖(Q : Ambient n) - P‖ ^ 2 < c₀ * T.η ^ 2)
    (hρ : C * ‖(Q : Ambient n) - P‖ ^ 2 < T.c * T.D.ρ ^ 2) :
    ∀ t ∈ Icc (0 : ℝ) 1, segCurve T P Q t = segCurve S P Q t := by
  have hy₁ := chart_mem_closedBall S hPS
  have hy₂ := chart_mem_closedBall T hPT
  have hP₁ := inverseAmbient_chart_of_dom S hPS
  have hP₂ := inverseAmbient_chart_of_dom T hPT
  have hQg₁ : (Q : Ambient n) ∈ goodSet S.D (extChartAt (𝓡 n) S.p P) :=
    good_of_dom S hPS (hQS.trans_le S.hδη)
  have hQg₂ : (Q : Ambient n) ∈ goodSet T.D (extChartAt (𝓡 n) T.p P) :=
    good_of_dom T hPT (hQT.trans_le T.hδη)
  obtain ⟨-, hQs₁, hz₁b⟩ := hQg₁
  obtain ⟨-, hQs₂, hz₂b⟩ := hQg₂
  rw [normalize_inclusion] at hQs₁ hQs₂
  have hz₁ : ‖chartNormalize S.p (Q : Ambient n) - extChartAt (𝓡 n) S.p P‖ < S.D.ρ / 2 := by
    rw [← dist_eq_norm]
    exact mem_ball.mp hz₁b
  have hz₂ : ‖chartNormalize T.p (Q : Ambient n) - extChartAt (𝓡 n) T.p P‖ < T.D.ρ / 2 := by
    rw [← dist_eq_norm]
    exact mem_ball.mp hz₂b
  have hQz₁ : inverseAmbient S.p (chartNormalize S.p (Q : Ambient n)) = Q :=
    inverseAmbient_chartNormalize hQs₁
  intro t ht
  by_cases hQP : (Q : Ambient n) = P
  · have hQP' : Q = P := Subtype.ext hQP
    subst hQP'
    unfold segCurve
    rw [chartNormalize_sphere S, chartNormalize_sphere T, geo_self _ hy₂, geo_self _ hy₁, hP₁, hP₂]
  · have hne : chartNormalize S.p (Q : Ambient n) ≠ extChartAt (𝓡 n) S.p P := by
      intro h
      apply hQP
      rw [← hQz₁, h, hP₁]
    have hV₁ : expInv S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) ≠ 0 :=
      expInv_ne_zero S.D hy₁ hz₁.le hne
    have hV₁ρ : ‖expInv S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n))‖ <
        S.D.ρ := by
      have := norm_expInv_le S.D hy₁ hz₁.le
      linarith
    obtain ⟨hC, hT, hD, hA, h0, h0'⟩ := geodesic_facts S.D hy₁ hV₁ hV₁ρ
    have h0g : geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) 0 =
        extChartAt (𝓡 n) S.p P := h0
    have h0g' : deriv (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n))) 0 =
        expInv S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) := h0'
    have hE : coordinateLagrangian F S.p
        (curveJet (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n))) 0) =
        minEnergy F P Q := by
      rw [minE_of_dom S hPS hQS]
      simp only [curveJet, h0g, h0g']
      rfl
    have hsrc : ∀ s ∈ Icc (0 : ℝ) 1, inverseSphere S.p
        (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) s) ∈
          (extChartAt (𝓡 n) T.p).source := by
      intro s hs
      have hnear : ‖inverseAmbient S.p
          (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) s) -
          inverseAmbient S.p
            (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) 0)‖ ≤
          Real.sqrt (coordinateLagrangian F S.p (curveJet
            (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n))) 0) / c₀) :=
        norm_segment_sub_le F hc₀ hb S.p hC hT hD hA s hs
      have hnear' : ‖inverseAmbient S.p
          (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) s) - P‖ ≤
          Real.sqrt (minEnergy F P Q / c₀) := by
        rw [hE, h0g, hP₁] at hnear
        exact hnear
      have hlt : ‖inverseAmbient S.p
          (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)) s) - P‖ <
          T.η := by
        refine hnear'.trans_lt ?_
        rw [Real.sqrt_lt' T.hη, div_lt_iff₀ hc₀]
        have h1 := hup.trans_lt hη
        nlinarith
      obtain ⟨-, hs', -⟩ := good_of_dom T hPT hlt
      rwa [inverseAmbient, normalize_inclusion] at hs'
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
    have hsmall : ‖deriv (transferCurve S.p T.p
        (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)))) 0‖ <
        T.D.ρ := by
      have hL : coordinateLagrangian F T.p (curveJet (transferCurve S.p T.p
          (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)))) 0) =
          coordinateLagrangian F S.p (curveJet
            (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n))) 0) :=
        transfer_lagrangian F (hC 0 h0mem) (hT 0 h0mem) (hsrc 0 h0mem)
      have hx20 : transferCurve S.p T.p
          (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n))) 0 =
          extChartAt (𝓡 n) T.p P := by
        unfold transferCurve
        rw [h0g, hP₁, chartNormalize_sphere T]
      have hlow := T.lower _ hy₂ (deriv (transferCurve S.p T.p
        (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)))) 0)
      have hj2 : curveJet (transferCurve S.p T.p
          (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)))) 0 =
          (extChartAt (𝓡 n) T.p P, deriv (transferCurve S.p T.p
            (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)))) 0) := by
        simp only [curveJet, hx20]
      rw [hj2, hE] at hL
      rw [hL] at hlow
      have h3 : T.c * ‖deriv (transferCurve S.p T.p
          (geo F S.D (extChartAt (𝓡 n) S.p P) (chartNormalize S.p (Q : Ambient n)))) 0‖ ^ 2 <
          T.c * T.D.ρ ^ 2 := by linarith
      have h4 := lt_of_mul_lt_mul_left h3 T.hc.le
      exact lt_of_pow_lt_pow_left₀ 2 T.D.ρ_pos.le h4
    have hy₁₂ : chartNormalize T.p (inverseAmbient S.p (extChartAt (𝓡 n) S.p P)) =
        extChartAt (𝓡 n) T.p P := by
      rw [hP₁, chartNormalize_sphere T]
    have hz₁₂ : chartNormalize T.p (inverseAmbient S.p (chartNormalize S.p (Q : Ambient n))) =
        chartNormalize T.p (Q : Ambient n) := by
      rw [hQz₁]
    exact segment_transfer S.D T.D hy₁ hz₁ hne hy₂ hz₂.le hy₁₂ hz₁₂ hsrc hsmall t ht

end Overlap

section Global

variable (F : ReversibleMetric n)

theorem segDom_isOpen (S : SegChart F) : IsOpen (segDom S) :=
  (continuousOn_extChartAt S.p).isOpen_inter_preimage (isOpen_extChartAt_source S.p) isOpen_ball

/-- A threshold below which C x² stays under a. -/
theorem exists_threshold {C a : ℝ} (hC : 0 < C) (ha : 0 < a) :
    ∃ τ > 0, ∀ x : ℝ, 0 ≤ x → x < τ → C * x ^ 2 < a := by
  refine ⟨min 1 (a / C), lt_min one_pos (div_pos ha hC), ?_⟩
  intro x hx hxτ
  have h1 : x < 1 := hxτ.trans_le (min_le_left _ _)
  have h2 : x < a / C := hxτ.trans_le (min_le_right _ _)
  have h3 : x ^ 2 ≤ x := by nlinarith
  have h4 : C * x < a := by
    rw [lt_div_iff₀ hC] at h2
    linarith
  nlinarith

/-- A finite atlas of packages with a uniform δ on which the segments of any two packages
containing the start point coincide. -/
theorem exists_segment_atlas :
    ∃ δ > 0, ∃ ι : Finset (Sphere n), ∃ S : Sphere n → SegChart F,
      (∀ P : Sphere n, ∃ P₀ ∈ ι, P ∈ segDom (S P₀)) ∧ (∀ P₀ ∈ ι, δ ≤ (S P₀).δ) ∧
      ∀ P₀ ∈ ι, ∀ P₁ ∈ ι, ∀ P Q : Sphere n, P ∈ segDom (S P₀) → P ∈ segDom (S P₁) →
        ‖(Q : Ambient n) - P‖ < δ → ∀ t ∈ Icc (0 : ℝ) 1, segCurve (S P₁) P Q t = segCurve (S P₀) P Q t := by
  choose S hSp hSy using exists_segChart F
  have hself : ∀ P₀ : Sphere n, P₀ ∈ segDom (S P₀) := by
    intro P₀
    refine ⟨?_, ?_⟩
    · rw [hSp P₀]
      exact mem_extChartAt_source P₀
    · rw [hSp P₀, hSy P₀]
      exact mem_ball_self (S P₀).hr'
  obtain ⟨ι, hι⟩ := isCompact_univ.elim_finite_subcover (fun P₀ => segDom (S P₀))
    (fun P₀ => segDom_isOpen F (S P₀)) (fun P _ => mem_iUnion.mpr ⟨P, hself P⟩)
  have hcover : ∀ P : Sphere n, ∃ P₀ ∈ ι, P ∈ segDom (S P₀) := by
    intro P
    have h := hι (mem_univ P)
    simp only [mem_iUnion] at h
    obtain ⟨i, hi, hP⟩ := h
    exact ⟨i, hi, hP⟩
  obtain ⟨c₀, C₀, hc₀, -, hb⟩ := Finsler.MetricComparison.exists_squared_bounds F
  obtain ⟨C, hC, hup⟩ := exists_minEnergy_upper F
  have hthr : ∀ P₀ : Sphere n, ∃ τ > 0, ∀ x : ℝ, 0 ≤ x → x < τ →
      C * x ^ 2 < c₀ * (S P₀).η ^ 2 ∧ C * x ^ 2 < (S P₀).c * (S P₀).D.ρ ^ 2 := by
    intro P₀
    have hη2 : 0 < c₀ * (S P₀).η ^ 2 := mul_pos hc₀ (pow_pos (S P₀).hη 2)
    have hρ2 : 0 < (S P₀).c * (S P₀).D.ρ ^ 2 := mul_pos (S P₀).hc (pow_pos (S P₀).D.ρ_pos 2)
    obtain ⟨τ₁, hτ₁, h₁⟩ := exists_threshold hC hη2
    obtain ⟨τ₂, hτ₂, h₂⟩ := exists_threshold hC hρ2
    refine ⟨min τ₁ τ₂, lt_min hτ₁ hτ₂, fun x hx hxτ => ⟨h₁ x hx ?_, h₂ x hx ?_⟩⟩
    · exact hxτ.trans_le (min_le_left _ _)
    · exact hxτ.trans_le (min_le_right _ _)
  choose τ hτ hτC using hthr
  have hne : ι.Nonempty := by
    obtain ⟨P₀, hP₀, -⟩ := hcover (northPole n)
    exact ⟨P₀, hP₀⟩
  set δ := ι.inf' hne (fun P₀ => min (S P₀).δ (τ P₀)) with hδdef
  have hδpos : 0 < δ := (Finset.lt_inf'_iff hne).mpr fun P₀ _ => lt_min (S P₀).hδ (hτ P₀)
  have hδle : ∀ P₀ ∈ ι, δ ≤ min (S P₀).δ (τ P₀) := fun P₀ hP₀ => Finset.inf'_le _ hP₀
  refine ⟨δ, hδpos, ι, S, hcover, fun P₀ hP₀ => (hδle P₀ hP₀).trans (min_le_left _ _), ?_⟩
  intro P₀ hP₀ P₁ hP₁ P Q hPS hPT hQ t ht
  have hQS : ‖(Q : Ambient n) - P‖ < (S P₀).δ :=
    hQ.trans_le ((hδle P₀ hP₀).trans (min_le_left _ _))
  have hQT : ‖(Q : Ambient n) - P‖ < (S P₁).δ :=
    hQ.trans_le ((hδle P₁ hP₁).trans (min_le_left _ _))
  have hQτ : ‖(Q : Ambient n) - P‖ < τ P₁ :=
    hQ.trans_le ((hδle P₁ hP₁).trans (min_le_right _ _))
  have hQ1 : ‖(Q : Ambient n) - P‖ ≤ 1 := hQS.le.trans (S P₀).hδ1
  obtain ⟨-, hmin⟩ := hup P Q (norm_sphere P) (norm_sphere Q) hQ1
  obtain ⟨h1, h2⟩ := hτC P₁ _ (norm_nonneg _) hQτ
  exact seg_eq hPS hPT hQS hQT hc₀ (fun q => (hb q).1) hmin h1 h2 t ht

/-- The constant path at the start point, with its representative. -/
theorem exists_const_path_rep {a b : Ambient n} (hne : (pathsBetween n a b).Nonempty) :
    ∃ w ∈ pathsBetween n a a, pathEnergy F w = 0 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, continuousRepresentative w t = a := by
  obtain ⟨w, hw, hw0, -⟩ := hne
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  refine ⟨restrict w h0 h0 le_rfl, ⟨restrict_mem hw h0 h0 le_rfl, ?_, ?_⟩, ?_, ?_⟩
  · rw [representative_restrict_zero, hw0]
  · rw [representative_restrict_one, hw0]
  · have h := pathEnergy_restrict_le F hw h0 h0 le_rfl
    rw [sub_self, zero_mul] at h
    exact le_antisymm h (pathEnergy_nonneg F _)
  · intro t ht
    rw [representative_restrict w h0 h0 le_rfl ht]
    simp [aff, hw0]

/-- The global short-segment map: a uniform δ and a segment map that near every start point is the
segment of one package, and whose H¹ path realizes the minimal energy. -/
theorem exists_segment_map :
    ∃ δ > 0, ∃ seg : Sphere n → Sphere n → ℝ → Ambient n,
      (∀ P : Sphere n, ∃ S : SegChart F, P ∈ segDom S ∧ δ ≤ S.δ ∧ ∀ P' ∈ segDom S, ∀ Q : Sphere n,
        ‖(Q : Ambient n) - P'‖ < δ → ∀ t ∈ Icc (0 : ℝ) 1, seg P' Q t = segCurve S P' Q t) ∧
      ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
        ∃ w ∈ pathsBetween n P Q, pathEnergy F w = minEnergy F P Q ∧
          ∀ t ∈ Icc (0 : ℝ) 1, continuousRepresentative w t = seg P Q t := by
  obtain ⟨δ, hδ, ι, S, hcover, hδS, hcons⟩ := exists_segment_atlas F
  choose idx hidx hPidx using hcover
  refine ⟨δ, hδ, fun P Q t => segCurve (S (idx P)) P Q t, ?_, ?_⟩
  · intro P
    refine ⟨S (idx P), hPidx P, hδS _ (hidx P), ?_⟩
    intro P' hP' Q hQ t ht
    exact hcons (idx P) (hidx P) (idx P') (hidx P') P' Q hP' (hPidx P') hQ t ht
  · intro P Q hQ
    have hPT : P ∈ segDom (S (idx P)) := hPidx P
    have hQT : ‖(Q : Ambient n) - P‖ < (S (idx P)).δ := hQ.trans_le (hδS _ (hidx P))
    have hy := chart_mem_closedBall (S (idx P)) hPT
    have hP₁ := inverseAmbient_chart_of_dom (S (idx P)) hPT
    obtain ⟨-, hQs, hzb⟩ := good_of_dom (S (idx P)) hPT (hQT.trans_le (S (idx P)).hδη)
    rw [normalize_inclusion] at hQs
    obtain ⟨C, hC, hup⟩ := exists_minEnergy_upper F
    by_cases hQP : (Q : Ambient n) = P
    · have hQP' : Q = P := Subtype.ext hQP
      subst hQP'
      obtain ⟨hne, -⟩ := hup Q Q (norm_sphere Q) (norm_sphere Q) (by simp)
      obtain ⟨w, hw, hwE, hwrep⟩ := exists_const_path_rep F hne
      refine ⟨w, hw, by rw [hwE, minEnergy_self F (norm_sphere Q)], ?_⟩
      intro t ht
      rw [hwrep t ht]
      change (Q : Ambient n) = segCurve (S (idx Q)) Q Q t
      unfold segCurve
      rw [chartNormalize_sphere (S (idx Q)), geo_self _ hy, hP₁]
    · have hz : ‖chartNormalize (S (idx P)).p (Q : Ambient n) -
          extChartAt (𝓡 n) (S (idx P)).p P‖ < (S (idx P)).D.ρ / 2 := by
        rw [← dist_eq_norm]
        exact mem_ball.mp hzb
      have hQz : inverseAmbient (S (idx P)).p (chartNormalize (S (idx P)).p (Q : Ambient n)) = Q :=
        inverseAmbient_chartNormalize hQs
      have hne : chartNormalize (S (idx P)).p (Q : Ambient n) ≠ extChartAt (𝓡 n) (S (idx P)).p P := by
        intro h
        apply hQP
        rw [← hQz, h, hP₁]
      obtain ⟨w, hw, hwE, hwrep⟩ := exists_geodesic_path_rep (S (idx P)).D hy hz.le hne
      rw [hP₁, hQz] at hw
      refine ⟨w, hw, ?_, hwrep⟩
      rw [hwE, minE_of_dom (S (idx P)) hPT hQT]
      rfl

end Global

end

end Finsler.SegmentAtlas
