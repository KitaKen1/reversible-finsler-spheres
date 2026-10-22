module

public import Finsler.Geometry.PolygonTwist

/-! Differentiability of the points of short segments in the endpoints. In a chart package, the
point at a fixed time of the coordinate geodesic from y to z is C³ in (y, z) away from the
diagonal: it is the flow of the geodesic spray at the unit jet of the segment and the time
‖V(y, z)‖ t, where V is the local inverse of the exponential map. Hence, for distinct points P₀
and Q₀ of the sphere, P₀ in the domain of a package and Q₀ within its radius, the point at a
time t in [0, 1] of the segment between the points with coordinates u and u' in the charts
centred at P₀ and Q₀ is differentiable in (u, u') at the centres. -/

@[expose] public section

namespace Finsler.SegmentSmooth

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.SphereCoordinateEuler Finsler.AmbientEnergyRegularity Finsler.AmbientCalibrator
open Finsler.SegmentAtlas Finsler.SegmentContinuity Finsler.CoordinateExpInverse
open Finsler.ChartTransfer Finsler.EnergyJointSmooth Finsler.PolygonTwist
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n}

section Package

variable {p : Sphere n} {y₀ : Coordinates n} {r : ℝ} (D : ExpData F p y₀ r)

/-- The point at a fixed time of the coordinate geodesic is C³ in the two endpoints, away from
the diagonal. -/
theorem geo_contDiffAt_joint {y₁ z₁ : Coordinates n} (hy₁ : y₁ ∈ ball y₀ r)
    (hz₁ : ‖z₁ - y₁‖ < D.ρ / 2) (hne : z₁ ≠ y₁) (t : ℝ) :
    ContDiffAt ℝ 3 (fun q : Coordinates n × Coordinates n => geo F D q.1 q.2 t) (y₁, z₁) := by
  have hV := expInv_contDiffAt_joint D hy₁ hz₁ hne
  have hV0 : expInv D y₁ z₁ ≠ 0 := expInv_ne_zero D (ball_subset_closedBall hy₁) hz₁.le hne
  have hnorm : ContDiffAt ℝ 3 (fun q : Coordinates n × Coordinates n => ‖expInv D q.1 q.2‖)
      (y₁, z₁) :=
    ContDiffAt.comp (g := fun v : Coordinates n => ‖v‖)
      (f := fun q : Coordinates n × Coordinates n => expInv D q.1 q.2) (y₁, z₁)
      (contDiffAt_norm ℝ hV0) hV
  have hinv : ContDiffAt ℝ 3 (fun q : Coordinates n × Coordinates n => ‖expInv D q.1 q.2‖⁻¹)
      (y₁, z₁) := hnorm.inv (norm_ne_zero_iff.mpr hV0)
  have hjet : ContDiffAt ℝ 3 (fun q : Coordinates n × Coordinates n =>
      (jetOf D q.1 q.2, ‖expInv D q.1 q.2‖ * t)) (y₁, z₁) :=
    (contDiffAt_fst.prodMk (hinv.smul hV)).prodMk (hnorm.mul contDiffAt_const)
  have hflow : ContDiffAt ℝ 3 (fun q : Coordinates n × Coordinates n =>
      flowMap D (jetOf D q.1 q.2, ‖expInv D q.1 q.2‖ * t)) (y₁, z₁) :=
    ContDiffAt.comp (g := flowMap D)
      (f := fun q : Coordinates n × Coordinates n => (jetOf D q.1 q.2, ‖expInv D q.1 q.2‖ * t))
      (y₁, z₁) (flowMap_contDiff D).contDiffAt hjet
  exact contDiffAt_fst.comp (y₁, z₁) hflow

end Package

/-- **Segment points are differentiable in the endpoints.** For distinct points P₀, Q₀ with P₀ in
the domain of a package and Q₀ within its radius, the point at a time t in [0, 1] of the
segment between the points with coordinates u, u' in the charts centred at P₀, Q₀ is
differentiable in (u, u') at the centres. -/
theorem segCurve_differentiableAt (T : SegChart F) {P₀ Q₀ : Sphere n} (hP : P₀ ∈ segDom T)
    (hQ : ‖(Q₀ : Ambient n) - P₀‖ < T.δ) (hne : Q₀ ≠ P₀) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun w : Coordinates n × Coordinates n =>
      segCurve T (inverseSphere P₀ w.1) (inverseSphere Q₀ w.2) t) (ctr P₀, ctr Q₀) := by
  obtain ⟨-, hQs, -⟩ := good_of_dom T hP (hQ.trans_le T.hδη)
  rw [normalize_inclusion] at hQs
  have hfun : (fun w : Coordinates n × Coordinates n =>
      segCurve T (inverseSphere P₀ w.1) (inverseSphere Q₀ w.2) t) =
      fun w => inverseAmbient T.p (geo F T.D (trans T P₀ w.1) (trans T Q₀ w.2) t) := by
    funext w
    unfold segCurve
    rw [← chartNormalize_sphere T (inverseSphere P₀ w.1)]
    rfl
  rw [hfun]
  -- the two transition maps
  have ht1 : ContDiffAt ℝ 3 (trans T P₀) (ctr P₀) := (trans_contDiffAt T hP.1).of_le (by simp)
  have ht2 : ContDiffAt ℝ 3 (trans T Q₀) (ctr Q₀) := (trans_contDiffAt T hQs).of_le (by simp)
  have h1 : ContDiffAt ℝ 3 (fun w : Coordinates n × Coordinates n => trans T P₀ w.1)
      (ctr P₀, ctr Q₀) :=
    ContDiffAt.comp (g := trans T P₀) (f := fun w : Coordinates n × Coordinates n => w.1)
      (ctr P₀, ctr Q₀) ht1 contDiffAt_fst
  have h2 : ContDiffAt ℝ 3 (fun w : Coordinates n × Coordinates n => trans T Q₀ w.2)
      (ctr P₀, ctr Q₀) :=
    ContDiffAt.comp (g := trans T Q₀) (f := fun w : Coordinates n × Coordinates n => w.2)
      (ctr P₀, ctr Q₀) ht2 contDiffAt_snd
  have hpair : ContDiffAt ℝ 3 (fun w : Coordinates n × Coordinates n =>
      (trans T P₀ w.1, trans T Q₀ w.2)) (ctr P₀, ctr Q₀) := h1.prodMk h2
  -- the base values
  have hy : trans T P₀ (ctr P₀) = extChartAt (𝓡 n) T.p P₀ := by
    rw [trans_ctr, chartNormalize_sphere]
  have hz : trans T Q₀ (ctr Q₀) = chartNormalize T.p (Q₀ : Ambient n) := trans_ctr T Q₀
  have hy₁ : extChartAt (𝓡 n) T.p P₀ ∈ ball T.y₀ T.r := ball_subset_ball T.hr'r hP.2
  have hz₁ := chart_dist_lt T hP hQ
  have hzy : chartNormalize T.p (Q₀ : Ambient n) ≠ extChartAt (𝓡 n) T.p P₀ := by
    intro h
    apply hne
    have h3 : inverseAmbient T.p (chartNormalize T.p (Q₀ : Ambient n)) = Q₀ :=
      inverseAmbient_chartNormalize hQs
    rw [h, inverseAmbient_chart_of_dom T hP] at h3
    exact Subtype.ext h3.symm
  have hgeo := geo_contDiffAt_joint T.D hy₁ hz₁ hzy t
  have hgeo' : ContDiffAt ℝ 3 (fun q : Coordinates n × Coordinates n => geo F T.D q.1 q.2 t)
      (trans T P₀ (ctr P₀), trans T Q₀ (ctr Q₀)) := by
    rw [hy, hz]
    exact hgeo
  have hcomp : ContDiffAt ℝ 3 (fun w : Coordinates n × Coordinates n =>
      geo F T.D (trans T P₀ w.1) (trans T Q₀ w.2) t) (ctr P₀, ctr Q₀) :=
    ContDiffAt.comp (g := fun q : Coordinates n × Coordinates n => geo F T.D q.1 q.2 t)
      (f := fun w : Coordinates n × Coordinates n => (trans T P₀ w.1, trans T Q₀ w.2))
      (ctr P₀, ctr Q₀) hgeo' hpair
  have hT : geo F T.D (trans T P₀ (ctr P₀)) (trans T Q₀ (ctr Q₀)) t ∈
      (extChartAt (𝓡 n) T.p).target := by
    rw [hy, hz]
    exact geo_mem_target T hP hQ ht
  have hinv : ContDiffAt ℝ 3 (inverseAmbient T.p)
      (geo F T.D (trans T P₀ (ctr P₀)) (trans T Q₀ (ctr Q₀)) t) :=
    (inverseAmbient_smoothAt T.p hT).of_le (by simp)
  have hall : ContDiffAt ℝ 3 (fun w : Coordinates n × Coordinates n =>
      inverseAmbient T.p (geo F T.D (trans T P₀ w.1) (trans T Q₀ w.2) t)) (ctr P₀, ctr Q₀) :=
    ContDiffAt.comp (g := inverseAmbient T.p)
      (f := fun w : Coordinates n × Coordinates n =>
        geo F T.D (trans T P₀ w.1) (trans T Q₀ w.2) t) (ctr P₀, ctr Q₀) hinv hcomp
  exact hall.differentiableAt (by norm_num)

end

end Finsler.SegmentSmooth
