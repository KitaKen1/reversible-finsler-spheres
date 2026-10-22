module

public import Finsler.Geometry.SegmentMomentum
public import Finsler.Geometry.EnergySphereSmooth

/-! The two-endpoint first variation of the actual minimal energy on the sphere. Normalization
extends the energy to ambient pairs. In a short-segment chart package it agrees on a neighborhood
with the chart energy, so the genuine derivative is the pullback of terminal minus initial
momentum. The chart atlas supplies this formula uniformly for all sufficiently short nonzero
segments. -/

@[expose] public section

namespace Finsler.EnergyMomentum

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.SphereCoordinateEuler Finsler.AmbientEnergyRegularity Finsler.AmbientCalibrator
open Finsler.SegmentAtlas Finsler.EnergySphereSmooth Finsler.SegmentMomentum
open Finsler.SegmentContinuity
open Finsler.EulerCovariance Finsler.EikonalChart Finsler.CoordinateExpInverse
open Finsler.SphereDistance (minEnergy)
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n}

/-- The boundary momentum expressed on ambient endpoint directions through the normalized chart. -/
def ambientBoundary (S : SegChart F) (P Q : Sphere n) : (Ambient n × Ambient n) →L[ℝ] ℝ :=
  (boundaryCovector S.D (chartNormalize S.p P) (chartNormalize S.p Q)).comp
    ((fderiv ℝ (chartNormalize S.p) (P : Ambient n)).prodMap
      (fderiv ℝ (chartNormalize S.p) (Q : Ambient n)))

/-- Neighborhood agreement with the chart energy, including ambient points off the sphere. -/
theorem ambientMinEnergy_eventually_eq (S : SegChart F) {P Q : Sphere n}
    (hP : P ∈ segDom S) (hQ : ‖(Q : Ambient n) - P‖ < S.δ) :
    ambientMinEnergy F =ᶠ[𝓝 ((P : Ambient n), (Q : Ambient n))]
      fun x => jointEnergy S.D (chartNormalize S.p x.1, chartNormalize S.p x.2) := by
  have hnorm1 : ContinuousAt (fun x : Ambient n × Ambient n => normalize x.1)
      ((P : Ambient n), (Q : Ambient n)) :=
    ContinuousAt.comp (g := normalize) (f := fun x : Ambient n × Ambient n => x.1)
      (x := ((P : Ambient n), (Q : Ambient n)))
      (normalize_smoothAt (sphere_ne_zero P)).continuousAt continuousAt_fst
  have hnorm2 : ContinuousAt (fun x : Ambient n × Ambient n => normalize x.2)
      ((P : Ambient n), (Q : Ambient n)) :=
    ContinuousAt.comp (g := normalize) (f := fun x : Ambient n × Ambient n => x.2)
      (x := ((P : Ambient n), (Q : Ambient n)))
      (normalize_smoothAt (sphere_ne_zero Q)).continuousAt continuousAt_snd
  have hev1 : ∀ᶠ x : Ambient n × Ambient n in 𝓝 ((P : Ambient n), (Q : Ambient n)),
      normalize x.1 ∈ segDom S :=
    hnorm1.preimage_mem_nhds ((segDom_isOpen F S).mem_nhds (by
      simpa only [normalize_inclusion] using hP))
  have hev2 : ∀ᶠ x : Ambient n × Ambient n in 𝓝 ((P : Ambient n), (Q : Ambient n)),
      ‖(normalize x.2 : Ambient n) - normalize x.1‖ < S.δ := by
    have hc : ContinuousAt (fun x : Ambient n × Ambient n =>
        ‖(normalize x.2 : Ambient n) - normalize x.1‖) ((P : Ambient n), (Q : Ambient n)) :=
      ((continuous_subtype_val.continuousAt.comp hnorm2).sub
        (continuous_subtype_val.continuousAt.comp hnorm1)).norm
    apply hc.eventually (gt_mem_nhds _)
    simpa only [normalize_inclusion] using hQ
  filter_upwards [hev1, hev2] with x hx1 hx2
  unfold ambientMinEnergy
  rw [minE_of_dom S hx1 hx2]
  unfold ambientEnergy jointEnergy energyFn
  rw [chartNormalize_normalize, ← chartNormalize_sphere, chartNormalize_normalize]

/-- The genuine derivative of the actual minimal sphere energy is terminal momentum minus initial
momentum, pulled back through the endpoint charts. -/
theorem ambientMinEnergy_hasFDerivAt_of_package (S : SegChart F) {P Q : Sphere n}
    (hP : P ∈ segDom S) (hQ : ‖(Q : Ambient n) - P‖ < S.δ) (hne : Q ≠ P) :
    HasFDerivAt (ambientMinEnergy F) (ambientBoundary S P Q)
      ((P : Ambient n), (Q : Ambient n)) := by
  have hPs : normalize (P : Ambient n) ∈ (extChartAt (𝓡 n) S.p).source := by
    rw [normalize_inclusion]
    exact hP.1
  obtain ⟨-, hQs, -⟩ := good_of_dom S hP (hQ.trans_le S.hδη)
  have h1 := ((chartNormalize_smoothAt S.p (sphere_ne_zero P) hPs).of_le
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).differentiableAt (by norm_num)
  have h2 := ((chartNormalize_smoothAt S.p (sphere_ne_zero Q) hQs).of_le
    (by simp : (1 : WithTop ℕ∞) ≤ ∞)).differentiableAt (by norm_num)
  have hΦ : HasFDerivAt
      (fun x : Ambient n × Ambient n => (chartNormalize S.p x.1, chartNormalize S.p x.2))
      ((fderiv ℝ (chartNormalize S.p) (P : Ambient n)).prodMap
        (fderiv ℝ (chartNormalize S.p) (Q : Ambient n)))
      ((P : Ambient n), (Q : Ambient n)) :=
    HasFDerivAt.prodMap ((P : Ambient n), (Q : Ambient n)) h1.hasFDerivAt h2.hasFDerivAt
  have hy : chartNormalize S.p (P : Ambient n) ∈ ball S.y₀ S.r := by
    rw [chartNormalize_sphere]
    exact ball_subset_ball S.hr'r hP.2
  have hz : ‖chartNormalize S.p (Q : Ambient n) - chartNormalize S.p (P : Ambient n)‖ <
      S.D.ρ / 2 := by
    rw [chartNormalize_sphere S P]
    exact chart_dist_lt S hP hQ
  have hn : chartNormalize S.p (Q : Ambient n) ≠ chartNormalize S.p (P : Ambient n) := by
    intro h
    apply hne
    have hQz : inverseAmbient S.p (chartNormalize S.p (Q : Ambient n)) = Q := by
      rw [normalize_inclusion] at hQs
      exact inverseAmbient_chartNormalize hQs
    have hPz : inverseAmbient S.p (chartNormalize S.p (P : Ambient n)) = P := by
      rw [chartNormalize_sphere S P]
      exact inverseAmbient_chart_of_dom S hP
    apply Subtype.ext
    rw [← hQz, ← hPz, h]
  have hd := (jointEnergy_hasFDerivAt S.D hy hz hn).comp
    ((P : Ambient n), (Q : Ambient n)) hΦ
  exact hd.congr_of_eventuallyEq (ambientMinEnergy_eventually_eq S hP hQ)

/-- Along genuine differentiable sphere endpoint curves the energy derivative is the boundary
momentum applied to their actual ambient velocities. -/
theorem minEnergy_hasDerivAt_endpoints (S : SegChart F) {P Q : Sphere n}
    (hP : P ∈ segDom S) (hQ : ‖(Q : Ambient n) - P‖ < S.δ) (hne : Q ≠ P)
    {a b : ℝ → Sphere n} {η ζ : Ambient n} {s : ℝ}
    (ha : HasDerivAt (fun t => (a t : Ambient n)) η s)
    (hb : HasDerivAt (fun t => (b t : Ambient n)) ζ s) (hay : a s = P) (hbq : b s = Q) :
    HasDerivAt (fun t => minEnergy F (a t : Ambient n) (b t : Ambient n))
      (ambientBoundary S P Q (η, ζ)) s := by
  have h := (ambientMinEnergy_hasFDerivAt_of_package S hP hQ hne).comp_hasDerivAt_of_eq
    s (ha.prodMk hb) (by simp [hay, hbq])
  simpa only [Function.comp_def, ambientMinEnergy, normalize_inclusion] using h

/-- A uniform radius supplies a chart package and the first-variation formula for every
sufficiently short nonconstant segment on the sphere. -/
theorem exists_ambientMinEnergy_hasFDerivAt (F : ReversibleMetric n) :
    ∃ δ > 0, ∀ P Q : Sphere n, Q ≠ P → ‖(Q : Ambient n) - P‖ < δ →
      ∃ S : SegChart F, P ∈ segDom S ∧ ‖(Q : Ambient n) - P‖ < S.δ ∧
        HasFDerivAt (ambientMinEnergy F) (ambientBoundary S P Q)
          ((P : Ambient n), (Q : Ambient n)) := by
  obtain ⟨δ, hδ, ι, S, hcover, hδS, -⟩ := exists_segment_atlas F
  refine ⟨δ, hδ, fun P Q hne hQ => ?_⟩
  obtain ⟨P₀, hP₀, hP⟩ := hcover P
  have hQS := hQ.trans_le (hδS P₀ hP₀)
  exact ⟨S P₀, hP, hQS, ambientMinEnergy_hasFDerivAt_of_package (S P₀) hP hQS hne⟩

end

end Finsler.EnergyMomentum
