module

public import Finsler.Geometry.EnergyJointSmooth
public import Finsler.Geometry.SegmentContinuity

/-! Smoothness of the minimal energy on the sphere. Extended to ambient pairs by normalization,
e(P, Q) agrees near an off-diagonal pair of sphere points with the chart energy F²(y, V(y, z)) at
y = chart(P/‖P‖), z = chart(Q/‖Q‖) for a chart package containing P; the chart energy is jointly C³
off the diagonal and the normalized chart is smooth, so the extended minimal energy is C³ there. -/

@[expose] public section

namespace Finsler.EnergySphereSmooth

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.CoordinateExpInverse Finsler.SphereRetraction Finsler.AmbientEnergyRegularity
open Finsler.AmbientCalibrator Finsler.SegmentAtlas Finsler.EnergyJointSmooth
open Finsler.SegmentContinuity
open Finsler.SphereDistance (minEnergy)
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ}

/-- The minimal energy extended to ambient pairs by normalization. -/
def ambientMinEnergy (F : ReversibleMetric n) (x : Ambient n × Ambient n) : ℝ :=
  minEnergy F (normalize x.1 : Ambient n) (normalize x.2 : Ambient n)

theorem chartNormalize_normalize (p : Sphere n) (q : Ambient n) :
    chartNormalize p (normalize q : Ambient n) = chartNormalize p q := by
  unfold chartNormalize
  rw [normalize_inclusion]

theorem sphere_ne_zero (P : Sphere n) : (P : Ambient n) ≠ 0 := by
  intro h
  have h1 : ‖(P : Ambient n)‖ = 1 := mem_sphere_zero_iff_norm.mp P.2
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

/-- Near an off-diagonal pair in a chart package the extended minimal energy is C³. -/
theorem ambientMinEnergy_contDiffAt_of_package (F : ReversibleMetric n) (S : SegChart F)
    {P₀ Q₀ : Sphere n} (hP₀ : P₀ ∈ segDom S) (hQ₀ : ‖(Q₀ : Ambient n) - P₀‖ < S.δ)
    (hne : Q₀ ≠ P₀) :
    ContDiffAt ℝ 3 (ambientMinEnergy F) ((P₀ : Ambient n), (Q₀ : Ambient n)) := by
  have hP0 := sphere_ne_zero P₀
  have hQ0 := sphere_ne_zero Q₀
  have hPs : normalize (P₀ : Ambient n) ∈ (extChartAt (𝓡 n) S.p).source := by
    rw [normalize_inclusion]
    exact hP₀.1
  obtain ⟨-, hQs, -⟩ := good_of_dom S hP₀ (hQ₀.trans_le S.hδη)
  -- the coordinate map
  set Φ : Ambient n × Ambient n → Coordinates n × Coordinates n :=
    fun x => (chartNormalize S.p x.1, chartNormalize S.p x.2) with hΦ
  have hΦs : ContDiffAt ℝ 3 Φ ((P₀ : Ambient n), (Q₀ : Ambient n)) := by
    have h1 : ContDiffAt ℝ 3 (chartNormalize S.p) (P₀ : Ambient n) :=
      (chartNormalize_smoothAt S.p hP0 hPs).of_le (by simp)
    have h2 : ContDiffAt ℝ 3 (chartNormalize S.p) (Q₀ : Ambient n) :=
      (chartNormalize_smoothAt S.p hQ0 hQs).of_le (by simp)
    exact (ContDiffAt.comp (g := chartNormalize S.p) (f := fun x : Ambient n × Ambient n => x.1)
      (x := ((P₀ : Ambient n), (Q₀ : Ambient n))) h1 contDiffAt_fst).prodMk
      (ContDiffAt.comp (g := chartNormalize S.p) (f := fun x : Ambient n × Ambient n => x.2)
        (x := ((P₀ : Ambient n), (Q₀ : Ambient n))) h2 contDiffAt_snd)
  -- the chart energy at the image point
  have hy₁ : chartNormalize S.p (P₀ : Ambient n) ∈ ball S.y₀ S.r := by
    rw [← chartNormalize_normalize, normalize_inclusion, chartNormalize_sphere]
    exact ball_subset_ball S.hr'r hP₀.2
  have hz₁ : ‖chartNormalize S.p (Q₀ : Ambient n) - chartNormalize S.p (P₀ : Ambient n)‖ <
      S.D.ρ / 2 := by
    rw [chartNormalize_sphere S P₀]
    exact chart_dist_lt S hP₀ hQ₀
  have hne₁ : chartNormalize S.p (Q₀ : Ambient n) ≠ chartNormalize S.p (P₀ : Ambient n) := by
    intro h
    apply hne
    have hQz : inverseAmbient S.p (chartNormalize S.p (Q₀ : Ambient n)) = Q₀ := by
      rw [normalize_inclusion] at hQs
      exact inverseAmbient_chartNormalize hQs
    have hPz : inverseAmbient S.p (chartNormalize S.p (P₀ : Ambient n)) = P₀ := by
      rw [chartNormalize_sphere S P₀]
      exact inverseAmbient_chart_of_dom S hP₀
    apply Subtype.ext
    rw [← hQz, ← hPz, h]
  have hyt : chartNormalize S.p (P₀ : Ambient n) ∈ (extChartAt (𝓡 n) S.p).target :=
    S.hball (ball_subset_closedBall hy₁)
  have he := energy_contDiffAt_joint S.D hy₁ hz₁ hne₁ hyt
  have hcomp := he.comp ((P₀ : Ambient n), (Q₀ : Ambient n)) hΦs
  -- agreement near the point
  apply hcomp.congr_of_eventuallyEq
  have hnorm1 : ContinuousAt (fun x : Ambient n × Ambient n => normalize x.1)
      ((P₀ : Ambient n), (Q₀ : Ambient n)) :=
    ContinuousAt.comp (g := normalize) (f := fun x : Ambient n × Ambient n => x.1)
      (x := ((P₀ : Ambient n), (Q₀ : Ambient n))) (normalize_smoothAt hP0).continuousAt
      continuousAt_fst
  have hnorm2 : ContinuousAt (fun x : Ambient n × Ambient n => normalize x.2)
      ((P₀ : Ambient n), (Q₀ : Ambient n)) :=
    ContinuousAt.comp (g := normalize) (f := fun x : Ambient n × Ambient n => x.2)
      (x := ((P₀ : Ambient n), (Q₀ : Ambient n))) (normalize_smoothAt hQ0).continuousAt
      continuousAt_snd
  have hev1 : ∀ᶠ x : Ambient n × Ambient n in 𝓝 ((P₀ : Ambient n), (Q₀ : Ambient n)),
      normalize x.1 ∈ segDom S := by
    have h := hnorm1.preimage_mem_nhds ((segDom_isOpen F S).mem_nhds (by
      change normalize (P₀ : Ambient n) ∈ segDom S
      rw [normalize_inclusion]
      exact hP₀))
    exact h
  have hev2 : ∀ᶠ x : Ambient n × Ambient n in 𝓝 ((P₀ : Ambient n), (Q₀ : Ambient n)),
      ‖(normalize x.2 : Ambient n) - normalize x.1‖ < S.δ := by
    have hc : ContinuousAt (fun x : Ambient n × Ambient n =>
        ‖(normalize x.2 : Ambient n) - normalize x.1‖) ((P₀ : Ambient n), (Q₀ : Ambient n)) :=
      ((continuous_subtype_val.continuousAt.comp hnorm2).sub
        (continuous_subtype_val.continuousAt.comp hnorm1)).norm
    apply hc.eventually (gt_mem_nhds _)
    simp only [normalize_inclusion]
    exact hQ₀
  filter_upwards [hev1, hev2] with x hx1 hx2
  unfold ambientMinEnergy
  rw [minE_of_dom S hx1 hx2]
  unfold ambientEnergy Finsler.EikonalChart.energyFn
  rw [chartNormalize_normalize, ← chartNormalize_sphere, chartNormalize_normalize]
  rfl

/-- A uniform δ below which the extended minimal energy is C³ at every off-diagonal pair. -/
theorem exists_ambientMinEnergy_contDiffAt (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 3 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)) := by
  obtain ⟨δ, hδ, ι, S, hcover, hδS, -⟩ := exists_segment_atlas F
  refine ⟨δ, hδ, fun P Q hne hQ => ?_⟩
  obtain ⟨P₀, hP₀, hP⟩ := hcover P
  exact ambientMinEnergy_contDiffAt_of_package F (S P₀) hP (hQ.trans_le (hδS P₀ hP₀)) hne

end

end Finsler.EnergySphereSmooth
