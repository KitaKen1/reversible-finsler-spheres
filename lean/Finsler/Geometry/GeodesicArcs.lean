module

public import Finsler.Geometry.SegmentContinuity
public import Finsler.Geometry.OrdinaryGeodesic
public import Finsler.Geometry.PolygonCritical

/-! Short arcs of closed geodesics are short segments. In a chart the coordinate curve of a
geodesic has the spray as acceleration, and so has every affine reparametrization of it, the spray
being quadratic in the velocity. A short arc with small initial velocity is therefore the
exp-data geodesic with its initial jet; its end point is the exponential of its initial velocity,
so by injectivity of the exponential this velocity is the local inverse V(y,z) and the arc is the
segment of the package. -/

@[expose] public section

namespace Finsler.GeodesicArcs

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.EikonalChart
open Finsler.ExpInverseRegularity Finsler.ChartTransfer Finsler.SegmentAtlas
open Finsler.SegmentContinuity Finsler.Loops Finsler.AmbientEnergyRegularity Finsler.RadialRemainder
open Finsler.SphereRetraction
open Function Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- The coordinate curve of a regular loop has nonzero velocity in the chart. -/
theorem deriv_coordinateCurve_ne_zero {γ : SmoothLoop n} (hreg : Finsler.Geodesics.Regular γ)
    (p : Sphere n) {t : ℝ} (ht : γ t ∈ (extChartAt (𝓡 n) p).source) :
    deriv (coordinateCurve p γ) t ≠ 0 := by
  intro h0
  have hy := (extChartAt (𝓡 n) p).map_source ht
  have hc := (coordinateCurve_smoothAt p γ ht).differentiableAt (by simp)
  have hφ := (inverseAmbient_smoothAt p hy).differentiableAt (by simp)
  have hcomp : HasDerivAt (inverseAmbient p ∘ coordinateCurve p γ)
      (fderiv ℝ (inverseAmbient p) (coordinateCurve p γ t) (deriv (coordinateCurve p γ) t)) t :=
    hφ.hasFDerivAt.comp_hasDerivAt t hc.hasDerivAt
  have hpos := hcomp.congr_of_eventuallyEq
    (inverseAmbient_coordinateCurve_eventually p γ ht).symm
  rw [h0, map_zero] at hpos
  exact Finsler.PolygonCritical.deriv_position_ne_zero γ hreg t hpos.deriv

/-- In a chart, the coordinate curve of a geodesic has the spray as acceleration. -/
theorem coordinateCurve_spray {γ : SmoothLoop n} (hreg : Finsler.Geodesics.Regular γ)
    (he : CoordinateEuler F γ) (p : Sphere n) {t : ℝ} (ht : γ t ∈ (extChartAt (𝓡 n) p).source) :
    deriv (deriv (coordinateCurve p γ)) t =
      spray (coordinateLagrangian F p) (curveJet (coordinateCurve p γ) t) := by
  have hy := (extChartAt (𝓡 n) p).map_source ht
  have hv := deriv_coordinateCurve_ne_zero hreg p ht
  exact spray_of_residual_eq_zero (coordinateLagrangian F p)
    ((coordinateCurve_smoothAt p γ ht).of_le (by simp))
    ((coordinateLagrangian_smoothAt_nonzero F p (z := curveJet (coordinateCurve p γ) t) hy hv).of_le
      (by simp))
    (coordinate_velocityHessian_injective F p hy hv) (he p t ht)

section Arc

variable {F} {γ : SmoothLoop n} (hreg : Finsler.Geodesics.Regular γ) (he : CoordinateEuler F γ)
  (p : Sphere n) {a h : ℝ}

theorem arc_hasDerivAt {s : ℝ} (hs : γ (a + s * h) ∈ (extChartAt (𝓡 n) p).source) :
    HasDerivAt (fun s => coordinateCurve p γ (a + s * h))
      (h • deriv (coordinateCurve p γ) (a + s * h)) s := by
  have hc := ((coordinateCurve_smoothAt p γ hs).differentiableAt (by simp)).hasDerivAt
  have hl : HasDerivAt (fun s : ℝ => a + s * h) h s := by
    have := ((hasDerivAt_id' s).mul_const h).const_add a
    rwa [one_mul] at this
  exact hc.scomp s hl

theorem arc_deriv_eventually {s : ℝ} (hs : γ (a + s * h) ∈ (extChartAt (𝓡 n) p).source) :
    deriv (fun s => coordinateCurve p γ (a + s * h)) =ᶠ[𝓝 s]
      fun s => h • deriv (coordinateCurve p γ) (a + s * h) := by
  have hcont : ContinuousAt (fun s : ℝ => γ (a + s * h)) s :=
    γ.smooth.continuous.continuousAt.comp
      ((continuous_const.add (continuous_id.mul continuous_const)).continuousAt)
  have hev := hcont.preimage_mem_nhds ((isOpen_extChartAt_source p).mem_nhds hs)
  filter_upwards [hev] with s' hs'
  exact (arc_hasDerivAt p hs').deriv

include hreg he in
theorem arc_spray (hh : h ≠ 0) {s : ℝ} (hs : γ (a + s * h) ∈ (extChartAt (𝓡 n) p).source) :
    deriv (deriv (fun s => coordinateCurve p γ (a + s * h))) s =
      spray (coordinateLagrangian F p) (curveJet (fun s => coordinateCurve p γ (a + s * h)) s) := by
  have hy : coordinateCurve p γ (a + s * h) ∈ (extChartAt (𝓡 n) p).target :=
    (extChartAt (𝓡 n) p).map_source hs
  have hv := deriv_coordinateCurve_ne_zero hreg p hs
  have h1 : deriv (deriv (fun s => coordinateCurve p γ (a + s * h))) s =
      deriv (fun s => h • deriv (coordinateCurve p γ) (a + s * h)) s :=
    (arc_deriv_eventually p hs).deriv_eq
  have hdd : HasDerivAt (deriv (coordinateCurve p γ))
      (deriv (deriv (coordinateCurve p γ)) (a + s * h)) (a + s * h) :=
    (((coordinateCurve_smoothAt p γ hs).derivWithin (m := 1) (by simp)).differentiableAt
      (by norm_num)).hasDerivAt
  have hl : HasDerivAt (fun s : ℝ => a + s * h) h s := by
    have := ((hasDerivAt_id' s).mul_const h).const_add a
    rwa [one_mul] at this
  have h2 : HasDerivAt (fun s => h • deriv (coordinateCurve p γ) (a + s * h))
      (h • (h • deriv (deriv (coordinateCurve p γ)) (a + s * h))) s :=
    (hdd.scomp s hl).const_smul h
  have hjet : curveJet (fun s => coordinateCurve p γ (a + s * h)) s =
      (coordinateCurve p γ (a + s * h), h • deriv (coordinateCurve p γ) (a + s * h)) := by
    unfold curveJet
    rw [(arc_hasDerivAt p hs).deriv]
  rw [h1, h2.deriv, coordinateCurve_spray F hreg he p hs, hjet, smul_smul, ← sq,
    coordinate_spray_smul F p hy hv hh]
  rfl

include hreg he in
/-- A short arc of a geodesic with small coordinate velocity is the segment of the package. -/
theorem arc_eq_segCurve (S : SegChart F) (hh : 0 < h) (hP : γ a ∈ segDom S)
    (hQ : ‖(γ (a + h) : Ambient n) - γ a‖ < S.δ)
    (hsrc : ∀ s ∈ Icc (0 : ℝ) 1, γ (a + s * h) ∈ (extChartAt (𝓡 n) S.p).source)
    (hsmall : ‖h • deriv (coordinateCurve S.p γ) a‖ < S.D.ρ) :
    ∀ s ∈ Icc (0 : ℝ) 1, (γ (a + s * h) : Ambient n) = segCurve S (γ a) (γ (a + h)) s := by
  have hh0 : h ≠ 0 := hh.ne'
  have ha : a + 0 * h = a := by ring
  have ha1 : a + 1 * h = a + h := by ring
  have h0src : γ (a + 0 * h) ∈ (extChartAt (𝓡 n) S.p).source := hsrc 0 ⟨le_rfl, zero_le_one⟩
  have hx0 : coordinateCurve S.p γ (a + 0 * h) = extChartAt (𝓡 n) S.p (γ a) := by
    rw [ha]
    rfl
  have hy : coordinateCurve S.p γ (a + 0 * h) ∈ closedBall S.y₀ S.r := by
    rw [hx0]
    exact chart_mem_closedBall S hP
  have hv : deriv (fun s => coordinateCurve S.p γ (a + s * h)) 0 =
      h • deriv (coordinateCurve S.p γ) a := by
    have := (arc_hasDerivAt S.p h0src).deriv
    rw [ha] at this
    exact this
  have hvne : deriv (fun s => coordinateCurve S.p γ (a + s * h)) 0 ≠ 0 := by
    rw [hv]
    exact smul_ne_zero hh0 (deriv_coordinateCurve_ne_zero hreg S.p (ha ▸ h0src))
  have hvρ : ‖deriv (fun s => coordinateCurve S.p γ (a + s * h)) 0‖ < S.D.ρ := by
    rw [hv]
    exact hsmall
  have hgeo := eq_scaledGeodesic F S.D hy hvne hvρ (x := fun s => coordinateCurve S.p γ (a + s * h))
    (fun s hs => ContDiffAt.comp (g := coordinateCurve S.p γ) (f := fun s : ℝ => a + s * h) (x := s)
      ((coordinateCurve_smoothAt S.p γ (hsrc s hs)).of_le (by simp))
      (contDiffAt_const.add (contDiffAt_id.mul contDiffAt_const)))
    (fun s hs => (extChartAt (𝓡 n) S.p).map_source (hsrc s hs))
    (fun s hs => by
      rw [(arc_hasDerivAt S.p (hsrc s hs)).deriv]
      exact smul_ne_zero hh0 (deriv_coordinateCurve_ne_zero hreg S.p (hsrc s hs)))
    (fun s hs => arc_spray hreg he S.p hh0 (hsrc s hs)) rfl rfl
  have hz : chartNormalize S.p (γ (a + h) : Ambient n) = coordinateCurve S.p γ (a + 1 * h) := by
    rw [chartNormalize_sphere, ha1]
    rfl
  have hexp : coordinateCurve S.p γ (a + 0 * h) +
      deriv (fun s => coordinateCurve S.p γ (a + s * h)) 0 +
      rad S.D.R (coordinateCurve S.p γ (a + 0 * h))
        (deriv (fun s => coordinateCurve S.p γ (a + s * h)) 0) =
      coordinateCurve S.p γ (a + 1 * h) := by
    rw [S.D.exp_eq _ hy _ hvne]
    have := hgeo 1 ⟨zero_le_one, le_rfl⟩
    unfold scaledGeodesic at this
    rw [mul_one] at this
    exact this.symm
  have hzy : ‖coordinateCurve S.p γ (a + 1 * h) - coordinateCurve S.p γ (a + 0 * h)‖ ≤
      S.D.ρ / 2 := by
    have := chart_dist_lt S hP hQ
    rw [hz, ← hx0] at this
    exact this.le
  obtain ⟨hVmem, hVspec⟩ := expInv_spec S.D hy hzy
  have hvV : deriv (fun s => coordinateCurve S.p γ (a + s * h)) 0 =
      expInv S.D (coordinateCurve S.p γ (a + 0 * h)) (coordinateCurve S.p γ (a + 1 * h)) :=
    eq_of_exp_eq S.D hy (mem_closedBall_zero_iff.mpr hvρ.le) hVmem (hexp.trans hVspec.symm)
  intro s hs
  have hinv : (γ (a + s * h) : Ambient n) =
      inverseAmbient S.p (coordinateCurve S.p γ (a + s * h)) := by
    show _ = inverseAmbient S.p (extChartAt (𝓡 n) S.p (γ (a + s * h)))
    unfold inverseAmbient inverseSphere
    rw [(extChartAt (𝓡 n) S.p).left_inv (hsrc s hs)]
  rw [hinv, hgeo s hs, hvV]
  unfold segCurve geo
  rw [hz, ← hx0]

include hreg he in
/-- The energy of such an arc is the minimal energy between its ends. -/
theorem arc_energy (S : SegChart F) (hh : 0 < h) (hP : γ a ∈ segDom S)
    (hQ : ‖(γ (a + h) : Ambient n) - γ a‖ < S.δ)
    (hsrc : ∀ s ∈ Icc (0 : ℝ) 1, γ (a + s * h) ∈ (extChartAt (𝓡 n) S.p).source)
    (hsmall : ‖h • deriv (coordinateCurve S.p γ) a‖ < S.D.ρ) :
    h * ∫ t in a..(a + h), Finsler.AmbientLagrangian.lagrangian F (Finsler.AmbientLagrangian.loopJet γ t) =
      Finsler.SphereDistance.minEnergy F (γ a : Ambient n) (γ (a + h)) := by
  have harc := arc_eq_segCurve hreg he S hh hP hQ hsrc hsmall
  have hvel : ∀ s ∈ Ioo (0 : ℝ) 1, segVel S (γ a) (γ (a + h)) s =
      h • Finsler.EnergyConservation.velocity γ (a + s * h) := by
    intro s hs
    have h1 := segCurve_hasDerivAt S hP hQ (Ioo_subset_Icc_self hs)
    have hl : HasDerivAt (fun s : ℝ => a + s * h) h s := by
      have := ((hasDerivAt_id' s).mul_const h).const_add a
      rwa [one_mul] at this
    have h2' := (Finsler.EnergyConservation.position_hasDerivAt γ (a + s * h)).scomp s hl
    have h2 : HasDerivAt (fun s => Finsler.EnergyConservation.position γ (a + s * h))
        (h • Finsler.EnergyConservation.velocity γ (a + s * h)) s := h2'
    have hev : (fun s => Finsler.EnergyConservation.position γ (a + s * h)) =ᶠ[𝓝 s]
        segCurve S (γ a) (γ (a + h)) := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
      exact harc s' (Ioo_subset_Icc_self hs')
    exact h1.unique (h2.congr_of_eventuallyEq hev.symm)
  have hcongr : ∫ s in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F
      (segCurve S (γ a) (γ (a + h)) s, segVel S (γ a) (γ (a + h)) s) =
      ∫ s in (0 : ℝ)..1, h ^ 2 * Finsler.AmbientLagrangian.lagrangian F (Finsler.AmbientLagrangian.loopJet γ (a + h * s)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
    intro s hs
    have e1 := harc s (Ioo_subset_Icc_self hs)
    have e2 := hvel s hs
    simp only
    rw [← e1, e2, Finsler.EnergyConservation.lagrangian_velocity_smul,
      Finsler.EnergyConservation.loopJet_eq, mul_comm h s]
    rfl
  have hsub := intervalIntegral.integral_comp_add_mul
    (fun t => Finsler.AmbientLagrangian.lagrangian F (Finsler.AmbientLagrangian.loopJet γ t)) hh.ne' a (a := 0) (b := 1)
  rw [mul_zero, add_zero, mul_one] at hsub
  rw [← segCurve_energy S hP hQ, hcongr, intervalIntegral.integral_const_mul, hsub, smul_eq_mul]
  field_simp

end Arc

section Scale

variable {F} {γ : SmoothLoop n}

/-- The conditions under which the arc of γ on [a, a + h] is the segment of the package S. -/
def ArcGood (γ : SmoothLoop n) (S : SegChart F) (a h : ℝ) : Prop :=
  γ a ∈ segDom S ∧ ‖(γ (a + h) : Ambient n) - γ a‖ < S.δ ∧
    (∀ s ∈ Icc (0 : ℝ) 1, γ (a + s * h) ∈ (extChartAt (𝓡 n) S.p).source) ∧
    ‖h • deriv (coordinateCurve S.p γ) a‖ < S.D.ρ

/-- Near every time, short arcs are good for the package centred at the point. -/
theorem local_arc_scale (t : ℝ) :
    ∃ ε > 0, ∃ S : SegChart F, ∀ a ∈ ball t ε, ∀ h ∈ Ioo (0 : ℝ) ε, ArcGood γ S a h := by
  obtain ⟨S, hSp, hSy⟩ := exists_segChart F (γ t)
  have hmem : γ t ∈ segDom S := by
    refine ⟨?_, ?_⟩
    · rw [hSp]
      exact mem_extChartAt_source _
    · rw [hSp, ← hSy]
      exact mem_ball_self S.hr'
  have hγc : Continuous (fun b : ℝ => γ b) := γ.smooth.continuous
  have hU : (fun b : ℝ => γ b) ⁻¹' segDom S ∈ 𝓝 t :=
    hγc.continuousAt.preimage_mem_nhds ((segDom_isOpen F S).mem_nhds hmem)
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.mp hU
  have hγa : Continuous (fun b : ℝ => (γ b : Ambient n)) := continuous_subtype_val.comp hγc
  have hV : {b : ℝ | ‖(γ b : Ambient n) - γ t‖ < S.δ / 2} ∈ 𝓝 t := by
    have h0 : ‖(γ t : Ambient n) - γ t‖ < S.δ / 2 := by
      rw [sub_self, norm_zero]
      exact half_pos S.hδ
    exact ((hγa.sub continuous_const).norm.continuousAt).preimage_mem_nhds (isOpen_gt' _ |>.mem_nhds h0)
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.mp hV
  have hsrc : γ t ∈ (extChartAt (𝓡 n) S.p).source := hmem.1
  have hdc : ContinuousAt (deriv (coordinateCurve S.p γ)) t :=
    ((coordinateCurve_smoothAt S.p γ hsrc).derivWithin (m := 0) (by simp)).continuousAt
  have hW : {b : ℝ | ‖deriv (coordinateCurve S.p γ) b‖ <
      ‖deriv (coordinateCurve S.p γ) t‖ + 1} ∈ 𝓝 t :=
    hdc.norm.preimage_mem_nhds (isOpen_gt' _ |>.mem_nhds (lt_add_one _))
  obtain ⟨ε₃, hε₃, hb₃⟩ := Metric.mem_nhds_iff.mp hW
  set M := ‖deriv (coordinateCurve S.p γ) t‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  set ε := min (min ε₁ ε₂) (min ε₃ (S.D.ρ / M)) / 2 with hε
  have hεpos : 0 < ε := by
    have := S.D.ρ_pos
    positivity
  have hε1 : 2 * ε ≤ ε₁ := by
    rw [hε]
    linarith [min_le_left (min ε₁ ε₂) (min ε₃ (S.D.ρ / M)), min_le_left ε₁ ε₂]
  have hε2 : 2 * ε ≤ ε₂ := by
    rw [hε]
    linarith [min_le_left (min ε₁ ε₂) (min ε₃ (S.D.ρ / M)), min_le_right ε₁ ε₂]
  have hε3 : 2 * ε ≤ ε₃ := by
    rw [hε]
    linarith [min_le_right (min ε₁ ε₂) (min ε₃ (S.D.ρ / M)), min_le_left ε₃ (S.D.ρ / M)]
  have hε4 : 2 * ε ≤ S.D.ρ / M := by
    rw [hε]
    linarith [min_le_right (min ε₁ ε₂) (min ε₃ (S.D.ρ / M)), min_le_right ε₃ (S.D.ρ / M)]
  refine ⟨ε, hεpos, S, fun a ha h hh => ?_⟩
  rw [mem_ball, Real.dist_eq] at ha
  have hball : ∀ s ∈ Icc (0 : ℝ) 1, |a + s * h - t| < 2 * ε := by
    intro s hs
    have h1 : |s * h| ≤ h := by
      rw [abs_of_nonneg (mul_nonneg hs.1 hh.1.le)]
      nlinarith [hs.2, hh.1]
    calc |a + s * h - t| = |(a - t) + s * h| := by ring_nf
      _ ≤ |a - t| + |s * h| := abs_add_le _ _
      _ < ε + ε := add_lt_add_of_lt_of_le ha (h1.trans hh.2.le)
      _ = 2 * ε := by ring
  have hin : ∀ s ∈ Icc (0 : ℝ) 1, γ (a + s * h) ∈ segDom S := fun s hs =>
    hb₁ (mem_ball.mpr (show dist (a + s * h) t < ε₁ by rw [Real.dist_eq]; linarith [hball s hs]))
  refine ⟨?_, ?_, fun s hs => (hin s hs).1, ?_⟩
  · have := hin 0 ⟨le_rfl, zero_le_one⟩
    rwa [zero_mul, add_zero] at this
  · have hb1 := hball 1 ⟨zero_le_one, le_rfl⟩
    rw [one_mul] at hb1
    have h1 : ‖(γ (a + h) : Ambient n) - γ t‖ < S.δ / 2 :=
      hb₂ (mem_ball.mpr (show dist (a + h) t < ε₂ by rw [Real.dist_eq]; linarith))
    have h2 : ‖(γ a : Ambient n) - γ t‖ < S.δ / 2 :=
      hb₂ (mem_ball.mpr (show dist a t < ε₂ by rw [Real.dist_eq]; linarith))
    calc ‖(γ (a + h) : Ambient n) - γ a‖ = ‖((γ (a + h) : Ambient n) - γ t) - ((γ a : Ambient n) - γ t)‖ := by
          congr 1
          abel
      _ ≤ ‖(γ (a + h) : Ambient n) - γ t‖ + ‖(γ a : Ambient n) - γ t‖ := norm_sub_le _ _
      _ < S.δ / 2 + S.δ / 2 := add_lt_add h1 h2
      _ = S.δ := add_halves _
  · have hd : ‖deriv (coordinateCurve S.p γ) a‖ < M :=
      hb₃ (mem_ball.mpr (by rw [Real.dist_eq]; linarith))
    rw [norm_smul, Real.norm_of_nonneg hh.1.le]
    calc h * ‖deriv (coordinateCurve S.p γ) a‖ ≤ ε * M :=
          mul_le_mul hh.2.le hd.le (norm_nonneg _) hεpos.le
      _ < S.D.ρ := by
          have : ε * M ≤ S.D.ρ / M / 2 * M := mul_le_mul_of_nonneg_right (by linarith) hMpos.le
          have h5 : S.D.ρ / M / 2 * M = S.D.ρ / 2 := by field_simp
          linarith [S.D.ρ_pos]

/-- A uniform scale below which all arcs starting in [0,1] are good. -/
theorem exists_arc_scale :
    ∃ h₀ > 0, ∀ a ∈ Icc (0 : ℝ) 1, ∀ h ∈ Ioo (0 : ℝ) h₀, ∃ S : SegChart F, ArcGood γ S a h := by
  choose ε hε S hS using fun t : ℝ => local_arc_scale (F := F) (γ := γ) t
  obtain ⟨T, hT⟩ := isCompact_Icc.elim_finite_subcover (fun t : ℝ => ball t (ε t))
    (fun _ => isOpen_ball) (fun x _ => mem_iUnion.mpr ⟨x, mem_ball_self (hε x)⟩)
  have hT0 : T.Nonempty := by
    obtain ⟨t, ht, -⟩ := mem_iUnion₂.mp (hT (left_mem_Icc.mpr zero_le_one))
    exact ⟨t, ht⟩
  refine ⟨T.inf' hT0 ε, (Finset.lt_inf'_iff hT0).mpr (fun t _ => hε t), fun a ha h hh => ?_⟩
  obtain ⟨t, ht, hat⟩ := mem_iUnion₂.mp (hT ha)
  exact ⟨S t, hS t a hat h ⟨hh.1, hh.2.trans_le (Finset.inf'_le _ ht)⟩⟩

end Scale

end

end Finsler.GeodesicArcs
