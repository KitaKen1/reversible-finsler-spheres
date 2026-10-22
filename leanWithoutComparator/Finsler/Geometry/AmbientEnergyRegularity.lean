module

public import Finsler.Geometry.CoordinateEnergyRegularity

/-! Actual ambient F² density is C¹ away from zero positions, including
velocities annihilated by normalization. A local sphere chart supplies the
C¹ pullback; nonzero ambient velocity is not a slit-bundle hypothesis. -/

@[expose] public section

namespace Finsler.AmbientEnergyRegularity

open Finsler.SphereGeometry Finsler.SphereCoordinateEuler Finsler.Geometry
open Finsler.SphereRetraction Finsler.AmbientLagrangian Finsler.EulerCovariance
open Finsler.CoordinateEnergyRegularity Function Filter Set
open scoped Manifold ContDiff Topology

noncomputable section

variable {n : ℕ}

def chartNormalize (p : Sphere n) (q : Ambient n) : Coordinates n :=
  extChartAt (𝓡 n) p (normalize q)

theorem chartNormalize_mem_target (p : Sphere n) {q : Ambient n}
    (hs : normalize q ∈ (extChartAt (𝓡 n) p).source) :
    chartNormalize p q ∈ (extChartAt (𝓡 n) p).target :=
  (extChartAt (𝓡 n) p).map_source hs

theorem chartNormalize_smoothAt (p : Sphere n) {q : Ambient n}
    (hq : q ≠ 0) (hs : normalize q ∈ (extChartAt (𝓡 n) p).source) :
    ContDiffAt ℝ ∞ (chartNormalize p) q := by
  have hs' : normalize q ∈ (chartAt (Coordinates n) p).source := by
    simpa only [extChartAt_source] using hs
  exact ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hs').comp q
    (normalize_smoothAt hq)).contDiffAt

theorem chartNormalize_fderiv (p : Sphere n) {q : Ambient n}
    (hq : q ≠ 0) (hs : normalize q ∈ (extChartAt (𝓡 n) p).source) :
    fderiv ℝ (chartNormalize p) q =
      (mfderiv (𝓡 n) 𝓘(ℝ, Coordinates n) (extChartAt (𝓡 n) p) (normalize q)).comp
        (mfderiv 𝓘(ℝ, Ambient n) (𝓡 n) normalize q) := by
  have hs' : normalize q ∈ (chartAt (Coordinates n) p).source := by
    simpa only [extChartAt_source] using hs
  have h := mvfderiv_comp q
    ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hs').mdifferentiableAt (by simp))
    ((normalize_smoothAt hq).mdifferentiableAt (by simp))
  rw [mvfderiv_eq_fderiv] at h
  exact h

theorem inverse_chart_velocity (p : Sphere n) {q : Ambient n}
    (hq : q ≠ 0) (hs : normalize q ∈ (extChartAt (𝓡 n) p).source) (v : Ambient n) :
    mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) (chartNormalize p q)
      (fderiv ℝ (chartNormalize p) q v) =
        mfderiv 𝓘(ℝ, Ambient n) (𝓡 n) normalize q v := by
  rw [chartNormalize_fderiv p hq hs]
  change mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) (chartNormalize p q)
    (mfderiv (𝓡 n) 𝓘(ℝ, Coordinates n) (extChartAt (𝓡 n) p) (normalize q)
      (mfderiv 𝓘(ℝ, Ambient n) (𝓡 n) normalize q v)) = _
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := 𝓡 n) hs
  rw [show Set.range (𝓡 n) = Set.univ by simp, mfderivWithin_univ] at h
  have h' := congrArg (fun D : Coordinates n →L[ℝ] Coordinates n =>
    D (mfderiv 𝓘(ℝ, Ambient n) (𝓡 n) normalize q v)) h
  change mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) (chartNormalize p q)
    (mfderiv (𝓡 n) 𝓘(ℝ, Coordinates n) (extChartAt (𝓡 n) p) (normalize q)
      (mfderiv 𝓘(ℝ, Ambient n) (𝓡 n) normalize q v)) = _ at h'
  exact h'

theorem lagrangian_eq_coordinateJet (F : ReversibleMetric n) (p : Sphere n)
    {q : Ambient n} (hq : q ≠ 0)
    (hs : normalize q ∈ (extChartAt (𝓡 n) p).source) (v : Ambient n) :
    lagrangian F (q, v) = coordinateLagrangian F p (jetMap (chartNormalize p) (q, v)) := by
  change lagrangian F (q, v) = coordinateLagrangian F p
    (chartNormalize p q, fderiv ℝ (chartNormalize p) q v)
  rw [coordinateLagrangian_eq F p (chartNormalize_mem_target p hs),
    inverse_chart_velocity p hq hs v]
  have hp : inverseSphere p (chartNormalize p q) = normalize q :=
    (extChartAt (𝓡 n) p).left_inv hs
  rw [hp]
  rfl

theorem chartNormalize_jet_smoothAt (p : Sphere n) {z : Ambient n × Ambient n}
    (hq : z.1 ≠ 0) (hs : normalize z.1 ∈ (extChartAt (𝓡 n) p).source) :
    ContDiffAt ℝ ∞ (jetMap (chartNormalize p)) z := by
  have h := chartNormalize_smoothAt p hq hs
  exact (h.comp z contDiffAt_fst).prodMk
    (((h.fderiv_right (m := ∞) (by simp)).comp z contDiffAt_fst).clm_apply contDiffAt_snd)

theorem lagrangian_contDiffAt_one (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z.1 ≠ 0) : ContDiffAt ℝ 1 (lagrangian F) z := by
  let p := normalize z.1
  have hs : normalize z.1 ∈ (extChartAt (𝓡 n) p).source := mem_extChartAt_source p
  have hq : ∀ᶠ a : Ambient n × Ambient n in 𝓝 z, a.1 ≠ 0 :=
    (isOpen_ne_fun continuous_fst continuous_const).mem_nhds hz
  have hc : ContinuousAt (fun a : Ambient n × Ambient n => normalize a.1) z :=
    (normalize_smoothAt hz).continuousAt.comp continuousAt_fst
  have hsrc : ∀ᶠ a : Ambient n × Ambient n in 𝓝 z,
      normalize a.1 ∈ (extChartAt (𝓡 n) p).source :=
    hc.preimage_mem_nhds (extChartAt_source_mem_nhds' (I := 𝓡 n) hs)
  have he : lagrangian F =ᶠ[𝓝 z] fun a =>
      coordinateLagrangian F p (jetMap (chartNormalize p) a) := by
    filter_upwards [hq, hsrc] with a ha hb
    exact lagrangian_eq_coordinateJet F p ha hb a.2
  have hbase : (jetMap (chartNormalize p) z).1 ∈ (extChartAt (𝓡 n) p).target :=
    chartNormalize_mem_target p hs
  have h := (coordinateLagrangian_contDiffAt_one F p
    (z := jetMap (chartNormalize p) z) hbase).comp z
      ((chartNormalize_jet_smoothAt p hz hs).of_le (by simp))
  exact h.congr_of_eventuallyEq he

theorem lagrangian_hasFDerivAt (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z.1 ≠ 0) : HasFDerivAt (lagrangian F) (fderiv ℝ (lagrangian F) z) z :=
  ((lagrangian_contDiffAt_one F hz).differentiableAt (by norm_num)).hasFDerivAt

theorem lagrangian_fderiv_continuousAt (F : ReversibleMetric n)
    {z : Ambient n × Ambient n} (hz : z.1 ≠ 0) :
    ContinuousAt (fderiv ℝ (lagrangian F)) z :=
  (lagrangian_contDiffAt_one F hz).continuousAt_fderiv (by norm_num)

end

end Finsler.AmbientEnergyRegularity
