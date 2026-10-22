module

public import Finsler.Geometry.ShortCalibrator
public import Finsler.Geometry.AmbientEnergyRegularity
public import Finsler.Analysis.EnergyCalibration
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! The calibrator on the sphere. The chart energy function f(z) = F²(y, V(y,z)) is transported to
the ambient space by q ↦ f(chart(q/‖q‖)); on the set where this lands in the ball of radius ρ/2
around y it is C¹, and the chart Lagrangian of the transported jet is the ambient Lagrangian, so
the eikonal inequality holds there. A bump function centred at the start point cuts it off to a
global C¹ function, and `EnergyCalibration.le_pathEnergy` shows that every H¹ sphere path from
the start point that stays in the inner ball has energy at least f(chart q) at its endpoint q. -/

@[expose] public section

namespace Finsler.AmbientCalibrator

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity
open Finsler.CoordinateExpInverse Finsler.EikonalChart Finsler.ShortCalibrator
open Finsler.SphereRetraction Finsler.AmbientEnergyRegularity Finsler.AmbientLagrangian
open Finsler.IntervalSobolev Finsler.SobolevSpherePath Finsler.SphereDistance
open Finsler.EnergyCalibration
open Set Filter Metric
open scoped Topology ContDiff Manifold RealInnerProductSpace

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

/-- The ambient energy function q ↦ F²(y, V(y, chart(q/‖q‖))). -/
def ambientEnergy (y : Coordinates n) (q : Ambient n) : ℝ :=
  energyFn D y (chartNormalize p q)

/-- The set where the ambient energy function is C¹. -/
def goodSet (y : Coordinates n) : Set (Ambient n) :=
  {q | q ≠ 0 ∧ normalize q ∈ (extChartAt (𝓡 n) p).source ∧
    chartNormalize p q ∈ ball y (D.ρ / 2)}

theorem energyFn_nonneg (y z : Coordinates n) : 0 ≤ energyFn D y z :=
  sq_nonneg _

theorem chartNormalize_inverseAmbient {y : Coordinates n}
    (hyt : y ∈ (extChartAt (𝓡 n) p).target) : chartNormalize p (inverseAmbient p y) = y := by
  unfold chartNormalize inverseAmbient
  rw [normalize_inclusion]
  exact (extChartAt (𝓡 n) p).right_inv hyt

theorem inverseAmbient_chartNormalize {q : Sphere n}
    (hs : (q : Sphere n) ∈ (extChartAt (𝓡 n) p).source) :
    inverseAmbient p (chartNormalize p (q : Ambient n)) = q := by
  unfold chartNormalize inverseAmbient inverseSphere
  rw [normalize_inclusion, (extChartAt (𝓡 n) p).left_inv hs]

section Good

variable {y : Coordinates n} (hy : y ∈ closedBall y₀ r)
  (hyt : y ∈ (extChartAt (𝓡 n) p).target)

include hy hyt in
theorem ambientEnergy_contDiffAt {q : Ambient n} (hq : q ∈ goodSet D y) :
    ContDiffAt ℝ 1 (ambientEnergy D y) q := by
  obtain ⟨hq0, hqs, hqb⟩ := hq
  have h1 : ContDiffAt ℝ 1 (energyFn D y) (chartNormalize p q) :=
    (energyFn_contDiffOn D hy hyt).contDiffAt (isOpen_ball.mem_nhds hqb)
  have h2 : ContDiffAt ℝ 1 (chartNormalize p) q :=
    (chartNormalize_smoothAt p hq0 hqs).of_le (by simp)
  exact h1.comp q h2

include hy hyt in
/-- The eikonal inequality for the transported energy function, in every ambient direction. -/
theorem ambientEnergy_eikonal {q : Ambient n} (hq : q ∈ goodSet D y) (ξ : Ambient n) :
    fderiv ℝ (ambientEnergy D y) q ξ ≤
      2 * Real.sqrt (ambientEnergy D y q) * Real.sqrt (lagrangian F (q, ξ)) := by
  obtain ⟨hq0, hqs, hqb⟩ := hq
  have h1 : DifferentiableAt ℝ (energyFn D y) (chartNormalize p q) :=
    (energyFn_hasFDerivAt_ball D hy hyt hqb).differentiableAt
  have h2 : DifferentiableAt ℝ (chartNormalize p) q :=
    (chartNormalize_smoothAt p hq0 hqs).differentiableAt (by simp)
  have hcomp : fderiv ℝ (ambientEnergy D y) q =
      (fderiv ℝ (energyFn D y) (chartNormalize p q)).comp (fderiv ℝ (chartNormalize p) q) :=
    fderiv_comp q h1 h2
  rw [hcomp, ContinuousLinearMap.comp_apply, lagrangian_eq_coordinateJet F p hq0 hqs ξ]
  exact energyFn_eikonal_ball D hy hyt hqb _

/-- The cut-off calibrator χ·f̃. -/
def calibrator (y : Coordinates n) {P : Ambient n} (χ : ContDiffBump P) (q : Ambient n) : ℝ :=
  χ q * ambientEnergy D y q

theorem calibrator_nonneg (y : Coordinates n) {P : Ambient n} (χ : ContDiffBump P)
    (q : Ambient n) : 0 ≤ calibrator D y χ q :=
  mul_nonneg χ.nonneg (energyFn_nonneg D y _)

include hy hyt in
theorem calibrator_contDiff {P : Ambient n} (χ : ContDiffBump P)
    (hsub : closedBall P χ.rOut ⊆ goodSet D y) : ContDiff ℝ 1 (calibrator D y χ) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q ∈ closedBall P χ.rOut
  · exact (χ.contDiff.contDiffAt).mul (ambientEnergy_contDiffAt D hy hyt (hsub hq))
  · have hz : (χ : Ambient n → ℝ) =ᶠ[𝓝 q] 0 := by
      rw [← χ.tsupport_eq] at hq
      exact notMem_tsupport_iff_eventuallyEq.mp hq
    have h : calibrator D y χ =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
      filter_upwards [hz] with x hx
      simp [calibrator, hx]
    exact contDiffAt_const.congr_of_eventuallyEq h

theorem calibrator_eventuallyEq (y : Coordinates n) {P : Ambient n} (χ : ContDiffBump P)
    {q : Ambient n} (hq : q ∈ ball P χ.rIn) : calibrator D y χ =ᶠ[𝓝 q] ambientEnergy D y := by
  filter_upwards [isOpen_ball.mem_nhds hq] with x hx
  simp [calibrator, χ.one_of_mem_closedBall (ball_subset_closedBall hx)]

include hy hyt in
theorem calibrator_eikonal {P : Ambient n} (χ : ContDiffBump P)
    (hsub : closedBall P χ.rOut ⊆ goodSet D y) {q : Ambient n} (hq : q ∈ ball P χ.rIn)
    (ξ : Ambient n) :
    fderiv ℝ (calibrator D y χ) q ξ ≤
      2 * Real.sqrt (calibrator D y χ q) * Real.sqrt (lagrangian F (q, ξ)) := by
  have hev := calibrator_eventuallyEq D y χ hq
  have hq' : q ∈ goodSet D y :=
    hsub ((ball_subset_closedBall.trans (closedBall_subset_closedBall χ.rIn_lt_rOut.le)) hq)
  rw [hev.fderiv_eq, hev.eq_of_nhds]
  exact ambientEnergy_eikonal D hy hyt hq' ξ

include hy hyt in
/-- Calibration: an H¹ sphere path from the start point staying in the inner ball has energy at
least the transported energy function at its endpoint. -/
theorem le_pathEnergy_of_bump {P : Ambient n} (hP : chartNormalize p P = y) (χ : ContDiffBump P)
    (hsub : closedBall P χ.rOut ⊆ goodSet D y) {w : Space n} (hw : w ∈ SpherePath n)
    (h0 : continuousRepresentative w 0 = P)
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, continuousRepresentative w t ∈ ball P χ.rIn) :
    ambientEnergy D y (continuousRepresentative w 1) ≤ pathEnergy F w := by
  have hcal := le_pathEnergy F (calibrator_contDiff D hy hyt χ hsub) (calibrator_nonneg D y χ)
    (fun x hx _ ξ _ => calibrator_eikonal D hy hyt χ hsub hx ξ) hw hU ?_
  · have h1 := hU 1 (right_mem_Icc.mpr zero_le_one)
    rwa [(calibrator_eventuallyEq D y χ h1).eq_of_nhds] at hcal
  · rw [h0, (calibrator_eventuallyEq D y χ (mem_ball_self χ.rIn_pos)).eq_of_nhds]
    unfold ambientEnergy
    rw [hP]
    exact energyFn_self D hy

end Good

end

end Finsler.AmbientCalibrator
