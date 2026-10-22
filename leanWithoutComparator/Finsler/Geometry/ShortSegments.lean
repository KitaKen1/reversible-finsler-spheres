module

public import Finsler.Geometry.AmbientCalibrator

/-! Short minimizing segments. For start points y in a small ball around y₀ the closed ambient
ball of a uniform radius around the start point lies in the good set of the calibrator. A path
from the start point P to a nearby endpoint Q that leaves the inner ball has energy at least
c·rIn² by the round comparison and the sampling estimate, which exceeds the minimal energy, so
near-minimizing paths stay in the inner ball and are calibrated. Hence e(P,Q) = F²(y, V(y,z))
for z = chart(Q), and the coordinate geodesic path from P to Q attains the minimum. -/

@[expose] public section

namespace Finsler.ShortSegments

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity
open Finsler.CoordinateExpInverse Finsler.EikonalChart Finsler.ShortCalibrator
open Finsler.SphereRetraction Finsler.AmbientEnergyRegularity Finsler.AmbientLagrangian
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SphereDistance
open Finsler.SobolevAffine Finsler.AmbientCalibrator
open Set Filter Metric
open scoped Topology ContDiff Manifold NNReal

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

theorem norm_sphere (x : Sphere n) : ‖(x : Ambient n)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp x.2

theorem norm_inverseAmbient (y : Coordinates n) : ‖inverseAmbient p y‖ = 1 :=
  norm_sphere _

/-- Uniform radii: for start points near y₀ the closed ambient ball of radius rOut around the
start point lies in the good set. -/
theorem exists_uniform_radius (hr : 0 < r)
    (hball : closedBall y₀ r ⊆ (extChartAt (𝓡 n) p).target) :
    ∃ r' > 0, r' ≤ r ∧ ∃ rIn rOut : ℝ, 0 < rIn ∧ rIn < rOut ∧
      ∀ y ∈ ball y₀ r', closedBall (inverseAmbient p y) rOut ⊆ goodSet D y := by
  have hy₀ : y₀ ∈ (extChartAt (𝓡 n) p).target := hball (mem_closedBall_self hr.le)
  set P₀ := inverseAmbient p y₀ with hP₀
  have hP₀0 : P₀ ≠ 0 := by
    intro h
    have h1 := norm_inverseAmbient (p := p) y₀
    rw [← hP₀, h, norm_zero] at h1
    exact zero_ne_one h1
  have hP₀s : normalize P₀ ∈ (extChartAt (𝓡 n) p).source := by
    rw [hP₀, inverseAmbient, normalize_inclusion]
    exact (extChartAt (𝓡 n) p).map_target hy₀
  have hC1 : ContDiffAt ℝ 1 (chartNormalize p) P₀ :=
    (chartNormalize_smoothAt p hP₀0 hP₀s).of_le (by simp)
  obtain ⟨K, t, ht, hK⟩ := hC1.exists_lipschitzOnWith
  have hn : ∀ᶠ q : Ambient n in 𝓝 P₀,
      q ≠ 0 ∧ SphereRetraction.normalize q ∈ (extChartAt (𝓡 n) p).source ∧ q ∈ t := by
    filter_upwards [eventually_ne_nhds hP₀0,
      (normalize_smoothAt hP₀0).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source p).mem_nhds hP₀s), ht] with q h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨η, hη, hηsub⟩ := Metric.eventually_nhds_iff_ball.mp hn
  have hc : ContinuousAt (inverseAmbient p) y₀ := (inverseAmbient_smoothAt p hy₀).continuousAt
  obtain ⟨r₁, hr₁, hr₁sub⟩ := Metric.continuousAt_iff.mp hc (η / 2) (by positivity)
  refine ⟨min r₁ r, lt_min hr₁ hr, min_le_right _ _, ?_⟩
  have hK1 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  set rOut := min (η / 4) (D.ρ / (4 * ((K : ℝ) + 1))) with hrOut
  have hrOut_pos : 0 < rOut := lt_min (by positivity) (div_pos D.ρ_pos (by positivity))
  refine ⟨rOut / 2, rOut, by positivity, by linarith, ?_⟩
  intro y hy q hq
  have hyr : dist y y₀ < r₁ := lt_of_lt_of_le (mem_ball.mp hy) (min_le_left _ _)
  have hy' : y ∈ closedBall y₀ r :=
    mem_closedBall.mpr ((mem_ball.mp hy).le.trans (min_le_right _ _))
  have hyt : y ∈ (extChartAt (𝓡 n) p).target := hball hy'
  have hPy : dist (inverseAmbient p y) P₀ < η / 2 := hr₁sub hyr
  have hq' : dist q (inverseAmbient p y) ≤ rOut := mem_closedBall.mp hq
  have hrη : rOut ≤ η / 4 := min_le_left _ _
  have hq₀ : q ∈ ball P₀ η := by
    rw [mem_ball]
    calc dist q P₀ ≤ dist q (inverseAmbient p y) + dist (inverseAmbient p y) P₀ :=
          dist_triangle _ _ _
      _ < η := by linarith
  have hPy₀ : inverseAmbient p y ∈ ball P₀ η := by
    rw [mem_ball]
    linarith
  obtain ⟨hq0, hqs, hqt⟩ := hηsub q hq₀
  obtain ⟨-, -, hPt⟩ := hηsub _ hPy₀
  refine ⟨hq0, hqs, ?_⟩
  rw [mem_ball]
  have hlip := hK.dist_le_mul q hqt (inverseAmbient p y) hPt
  rw [chartNormalize_inverseAmbient hyt] at hlip
  have hK0 : (0 : ℝ) ≤ K := K.coe_nonneg
  have h1 : (K : ℝ) * dist q (inverseAmbient p y) ≤ (K : ℝ) * (D.ρ / (4 * ((K : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left (hq'.trans (min_le_right _ _)) hK0
  have h2 : (K : ℝ) * (D.ρ / (4 * ((K : ℝ) + 1))) < D.ρ / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) two_pos]
    nlinarith [D.ρ_pos]
  linarith

/-- A sphere path from P that leaves the ball of radius ρ₁ around P has energy at least c·ρ₁². -/
theorem le_pathEnergy_of_exit {c : ℝ} (hc : 0 < c)
    (hlow : ∀ a b : Ambient n, (pathsBetween n a b).Nonempty → c * ‖b - a‖ ^ 2 ≤ minEnergy F a b)
    {w : Space n} (hw : w ∈ SpherePath n) {t ρ₁ : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hout : ρ₁ ≤ ‖continuousRepresentative w t - continuousRepresentative w 0‖) (hρ₁ : 0 ≤ ρ₁) :
    c * ρ₁ ^ 2 ≤ pathEnergy F w := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have hmem : restrict w h0 ht ht.1 ∈ pathsBetween n (continuousRepresentative w 0)
      (continuousRepresentative w t) :=
    ⟨restrict_mem hw h0 ht ht.1, representative_restrict_zero w h0 ht ht.1,
      representative_restrict_one w h0 ht ht.1⟩
  have h1 := hlow _ _ ⟨_, hmem⟩
  have h2 := minEnergy_sample_le F hw h0 ht ht.1
  have hE := pathEnergy_nonneg F w
  have h3 : (t - 0) * pathEnergy F w ≤ pathEnergy F w := by
    have : t - 0 ≤ 1 := by linarith [ht.2]
    nlinarith
  have h4 : c * ρ₁ ^ 2 ≤ c * ‖continuousRepresentative w t - continuousRepresentative w 0‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ₁ hout 2) hc.le
  linarith

/-- The constant path: the restriction of a path to [0,0] has energy zero. -/
theorem exists_zero_path {a b : Ambient n} (hne : (pathsBetween n a b).Nonempty) :
    ∃ w ∈ pathsBetween n a a, pathEnergy F w = 0 := by
  obtain ⟨w, hw, hw0, -⟩ := hne
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  refine ⟨restrict w h0 h0 le_rfl, ⟨restrict_mem hw h0 h0 le_rfl, ?_, ?_⟩, ?_⟩
  · rw [representative_restrict_zero, hw0]
  · rw [representative_restrict_one, hw0]
  · have h := pathEnergy_restrict_le F hw h0 h0 le_rfl
    rw [sub_self, zero_mul] at h
    exact le_antisymm h (pathEnergy_nonneg F _)

/-- A uniform scale below which the round upper bound stays under the exit threshold. -/
theorem exists_small_scale {c C ρ₁ : ℝ} (hc : 0 < c) (hC : 0 < C) (hρ₁ : 0 < ρ₁) :
    ∃ δ > 0, δ ≤ 1 ∧ δ ≤ ρ₁ ∧ ∀ x : ℝ, 0 ≤ x → x < δ → C * x ^ 2 < c * ρ₁ ^ 2 := by
  obtain ⟨s, hs0, hs1, hsc⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ s ≤ c / (2 * C) :=
    ⟨min 1 (c / (2 * C)), lt_min one_pos (by positivity), min_le_left _ _, min_le_right _ _⟩
  refine ⟨min 1 (ρ₁ * s), lt_min one_pos (by positivity), min_le_left _ _,
    (min_le_right _ _).trans (by nlinarith), ?_⟩
  intro x hx hxδ
  have hxs : x < ρ₁ * s := hxδ.trans_le (min_le_right _ _)
  have h1 : C * x ^ 2 ≤ C * (ρ₁ * s) ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx hxs.le 2) hC.le
  have hss : s ^ 2 ≤ s := by nlinarith
  have h2 : C * (ρ₁ * s) ^ 2 ≤ C * ρ₁ ^ 2 * s := by
    calc C * (ρ₁ * s) ^ 2 = C * ρ₁ ^ 2 * s ^ 2 := by ring
      _ ≤ C * ρ₁ ^ 2 * s := mul_le_mul_of_nonneg_left hss (by positivity)
  have h3 : C * ρ₁ ^ 2 * s ≤ C * ρ₁ ^ 2 * (c / (2 * C)) :=
    mul_le_mul_of_nonneg_left hsc (by positivity)
  have h4 : C * ρ₁ ^ 2 * (c / (2 * C)) = c * ρ₁ ^ 2 / 2 := by
    field_simp
  have h5 : 0 < c * ρ₁ ^ 2 := by positivity
  linarith

section Segment

variable {c : ℝ} (hc : 0 < c)
  (hlow : ∀ a b : Ambient n, (pathsBetween n a b).Nonempty → c * ‖b - a‖ ^ 2 ≤ minEnergy F a b)
  {y : Coordinates n} (hy : y ∈ closedBall y₀ r) (hyt : y ∈ (extChartAt (𝓡 n) p).target)
  (χ : ContDiffBump (inverseAmbient p y))
  (hsub : closedBall (inverseAmbient p y) χ.rOut ⊆ goodSet D y)
  {Q : Sphere n}

include hc hlow hy hyt hsub in
/-- Paths below the exit threshold stay in the inner ball and are calibrated. -/
theorem ambientEnergy_le_of_lt {w : Space n} (hw : w ∈ pathsBetween n (inverseAmbient p y) Q)
    (hE : pathEnergy F w < c * χ.rIn ^ 2) : ambientEnergy D y Q ≤ pathEnergy F w := by
  have hU : ∀ t ∈ Icc (0 : ℝ) 1, continuousRepresentative w t ∈ ball (inverseAmbient p y) χ.rIn := by
    intro t ht
    rw [mem_ball, dist_eq_norm]
    by_contra hcon
    push Not at hcon
    have hout : χ.rIn ≤ ‖continuousRepresentative w t - continuousRepresentative w 0‖ := by
      rw [hw.2.1]
      exact hcon
    have := le_pathEnergy_of_exit hc hlow hw.1 ht hout χ.rIn_pos.le
    linarith
  have h := le_pathEnergy_of_bump D hy hyt (chartNormalize_inverseAmbient hyt) χ hsub hw.1 hw.2.1 hU
  rwa [hw.2.2] at h

include hc hlow hy hyt hsub in
/-- Below the threshold the calibration bound holds for the minimal energy. -/
theorem ambientEnergy_le_minEnergy (hne : (pathsBetween n (inverseAmbient p y) Q).Nonempty)
    (hsmall : minEnergy F (inverseAmbient p y) Q < c * χ.rIn ^ 2) :
    ambientEnergy D y Q ≤ minEnergy F (inverseAmbient p y) Q := by
  obtain ⟨w', hw', hw'E⟩ := exists_lt_of_lt F hne hsmall
  have hfQ : ambientEnergy D y Q < c * χ.rIn ^ 2 :=
    (ambientEnergy_le_of_lt D hc hlow hy hyt χ hsub hw' hw'E).trans_lt hw'E
  apply le_csInf (hne.image _)
  rintro _ ⟨w, hw, rfl⟩
  by_cases hE : pathEnergy F w < c * χ.rIn ^ 2
  · exact ambientEnergy_le_of_lt D hc hlow hy hyt χ hsub hw hE
  · push Not at hE
    linarith

end Segment

/-- The path realizing the transported energy: the coordinate geodesic, or the constant path
when the endpoint is the start point. -/
theorem exists_path_energy_eq {y : Coordinates n} (hy : y ∈ closedBall y₀ r)
    (hyt : y ∈ (extChartAt (𝓡 n) p).target) {Q : Sphere n}
    (hne : (pathsBetween n (inverseAmbient p y) Q).Nonempty)
    (hQgood : (Q : Ambient n) ∈ goodSet D y) :
    ∃ w ∈ pathsBetween n (inverseAmbient p y) Q, pathEnergy F w = ambientEnergy D y Q := by
  obtain ⟨-, hQsrc, hQball⟩ := hQgood
  rw [normalize_inclusion] at hQsrc
  by_cases hQP : (Q : Ambient n) = inverseAmbient p y
  · obtain ⟨w, hw, hwE⟩ := exists_zero_path (F := F) hne
    refine ⟨w, ?_, ?_⟩
    · rw [hQP]
      exact hw
    · rw [hwE]
      unfold ambientEnergy
      rw [hQP, chartNormalize_inverseAmbient hyt, energyFn_self D hy]
  · obtain ⟨z, hz⟩ : ∃ z, chartNormalize p (Q : Ambient n) = z := ⟨_, rfl⟩
    have hzQ : inverseAmbient p z = Q := by
      rw [← hz]
      exact inverseAmbient_chartNormalize hQsrc
    have hzy : z ≠ y := by
      intro h
      apply hQP
      rw [← hzQ, h]
    have hzρ : ‖z - y‖ ≤ D.ρ / 2 := by
      rw [hz] at hQball
      have h := mem_ball.mp hQball
      rw [dist_eq_norm] at h
      exact h.le
    obtain ⟨w, hw, hwE⟩ := exists_geodesic_path D hy hzρ hzy
    rw [hzQ] at hw
    refine ⟨w, hw, ?_⟩
    rw [hwE]
    unfold ambientEnergy energyFn
    rw [hz]

/-- Short segments: for start points near y₀ and endpoints within a uniform distance δ, the
minimal energy is the energy of the coordinate geodesic, F²(y, V(y, chart Q)), and it is
attained. -/
theorem short_segments (hr : 0 < r) (hball : closedBall y₀ r ⊆ (extChartAt (𝓡 n) p).target) :
    ∃ r' > 0, r' ≤ r ∧ ∃ δ > 0, ∀ y ∈ ball y₀ r', ∀ Q : Sphere n,
      ‖(Q : Ambient n) - inverseAmbient p y‖ < δ →
      minEnergy F (inverseAmbient p y) Q = ambientEnergy D y Q ∧
      ∃ w ∈ pathsBetween n (inverseAmbient p y) Q,
        pathEnergy F w = minEnergy F (inverseAmbient p y) Q := by
  obtain ⟨r', hr', hr'r, rIn, rOut, hrIn, hlt, huni⟩ := exists_uniform_radius D hr hball
  obtain ⟨c, hc, hlow⟩ := exists_minEnergy_lower F
  obtain ⟨C, hC, hup⟩ := exists_minEnergy_upper F
  obtain ⟨δ, hδ, hδ1, hδr, hδC⟩ := exists_small_scale hc hC hrIn
  refine ⟨r', hr', hr'r, δ, hδ, ?_⟩
  intro y hy Q hQ
  have hy' : y ∈ closedBall y₀ r :=
    mem_closedBall.mpr ((mem_ball.mp hy).le.trans hr'r)
  have hyt : y ∈ (extChartAt (𝓡 n) p).target := hball hy'
  obtain ⟨hne, hmin⟩ := hup _ _ (norm_inverseAmbient y) (norm_sphere Q) (hQ.le.trans hδ1)
  let χ : ContDiffBump (inverseAmbient p y) := ⟨rIn, rOut, hrIn, hlt⟩
  have hsub : closedBall (inverseAmbient p y) χ.rOut ⊆ goodSet D y := huni y hy
  have hsmall : minEnergy F (inverseAmbient p y) Q < c * χ.rIn ^ 2 :=
    hmin.trans_lt (hδC _ (norm_nonneg _) hQ)
  have hle := ambientEnergy_le_minEnergy D hc hlow hy' hyt χ hsub hne hsmall
  have hQgood : (Q : Ambient n) ∈ goodSet D y := by
    apply hsub
    rw [mem_closedBall, dist_eq_norm]
    exact (hQ.trans_le (hδr.trans hlt.le)).le
  obtain ⟨w, hw, hwE⟩ := exists_path_energy_eq D hy' hyt hne hQgood
  have hge := minEnergy_le F hw
  exact ⟨le_antisymm (hge.trans hwE.le) hle, w, hw, le_antisymm (hwE.le.trans hle) hge⟩

end

end Finsler.ShortSegments
