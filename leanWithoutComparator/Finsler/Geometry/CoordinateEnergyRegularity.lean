module

public import Finsler.Analysis.ParametricQuadratic
public import Finsler.Geometry.SphereCoordinateEuler

/-! Joint C¹ regularity of the actual F² density in every standard sphere
chart, including zero velocity. The inverse chart derivative is the genuine
manifold derivative. No second derivative at zero and no H¹ first-variation
theorem are asserted here. -/

@[expose] public section

namespace Finsler.CoordinateEnergyRegularity

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereCoordinateEuler
open Finsler.AmbientLagrangian Finsler.SphereRetraction Finsler.EulerCovariance
open Function
open scoped Manifold ContDiff Topology

noncomputable section

variable {n : ℕ}

theorem chartTarget_isOpen (p : Sphere n) :
    IsOpen (extChartAt (𝓡 n) p).target := by
  rw [extChartAt_target, show Set.range (𝓡 n) = Set.univ by simp, Set.inter_univ]
  exact (𝓡 n).continuous_symm.isOpen_preimage _ (chartAt (Coordinates n) p).open_target

theorem inverseSphere_derivative_ne_zero (p : Sphere n) {y w : Coordinates n}
    (hy : y ∈ (extChartAt (𝓡 n) p).target) (hw : w ≠ 0) :
    mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y w ≠ 0 := by
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓡 n) hy
  rw [show Set.range (𝓡 n) = Set.univ by simp, mfderivWithin_univ] at h
  intro hz
  have he := congrArg (fun D : Coordinates n →L[ℝ] Coordinates n => D w) h
  change mfderiv (𝓡 n) 𝓘(ℝ, Coordinates n) (extChartAt (𝓡 n) p)
    (inverseSphere p y) (mfderiv 𝓘(ℝ, Coordinates n) (𝓡 n) (inverseSphere p) y w) = w at he
  rw [hz, map_zero] at he
  exact hw he.symm

theorem inverseAmbient_jet_mem_slitDomain (p : Sphere n) {z : Coordinates n × Coordinates n}
    (hz : z.1 ∈ (extChartAt (𝓡 n) p).target) (hv : z.2 ≠ 0) :
    jetMap (inverseAmbient p) z ∈ slitDomain n := by
  rw [show z = (z.1, z.2) from rfl, inverseAmbient_jet p hz]
  refine ⟨ne_zero_of_mem_unit_sphere (inverseSphere p z.1), ?_⟩
  rw [lift_ambientPair]
  exact inverseSphere_derivative_ne_zero p hz hv

theorem coordinateLagrangian_velocity_smul (F : ReversibleMetric n) (p : Sphere n)
    (y : Coordinates n) (r : ℝ) (w : Coordinates n) :
    coordinateLagrangian F p (y, r • w) = r ^ 2 * coordinateLagrangian F p (y, w) := by
  change lagrangian F (inverseAmbient p y, fderiv ℝ (inverseAmbient p) y (r • w)) =
    r ^ 2 * lagrangian F (inverseAmbient p y, fderiv ℝ (inverseAmbient p) y w)
  rw [map_smul]
  exact Finsler.EnergyConservation.lagrangian_velocity_smul F _ _ r

theorem coordinateLagrangian_smoothAt_nonzero (F : ReversibleMetric n) (p : Sphere n)
    {z : Coordinates n × Coordinates n}
    (hz : z.1 ∈ (extChartAt (𝓡 n) p).target) (hv : z.2 ≠ 0) :
    ContDiffAt ℝ ∞ (coordinateLagrangian F p) z := by
  have hφ := inverseAmbient_smoothAt p hz
  have hj : ContDiffAt ℝ ∞ (jetMap (inverseAmbient p)) z :=
    (hφ.comp z contDiffAt_fst).prodMk
      (((hφ.fderiv_right (m := ∞) (by simp)).comp z contDiffAt_fst).clm_apply
        contDiffAt_snd)
  exact (lagrangian_smoothAt F (inverseAmbient_jet_mem_slitDomain p hz hv)).comp z hj

theorem coordinateLagrangian_hasFDerivAt_zero (F : ReversibleMetric n) (p : Sphere n)
    {y : Coordinates n} (hy : y ∈ (extChartAt (𝓡 n) p).target) :
    HasFDerivAt (coordinateLagrangian F p)
      (0 : Coordinates n × Coordinates n →L[ℝ] ℝ) (y, 0) :=
  Finsler.ParametricQuadratic.hasFDerivAt_zero (chartTarget_isOpen p)
    (coordinateLagrangian_velocity_smul F p)
    (fun _ hz hv => coordinateLagrangian_smoothAt_nonzero F p hz hv) hy

theorem coordinateLagrangian_contDiffAt_one (F : ReversibleMetric n) (p : Sphere n)
    {z : Coordinates n × Coordinates n} (hz : z.1 ∈ (extChartAt (𝓡 n) p).target) :
    ContDiffAt ℝ 1 (coordinateLagrangian F p) z :=
  Finsler.ParametricQuadratic.contDiffAt_one (chartTarget_isOpen p)
    (coordinateLagrangian_velocity_smul F p)
    (fun _ hy hv => coordinateLagrangian_smoothAt_nonzero F p hy hv) hz

theorem coordinateEnergy_contDiffAt_one (F : ReversibleMetric n) (p : Sphere n)
    {z : Coordinates n × Coordinates n} (hz : z.1 ∈ (extChartAt (𝓡 n) p).target) :
    ContDiffAt ℝ 1 (fun a => coordinateLagrangian F p a / 2) z :=
  (coordinateLagrangian_contDiffAt_one F p hz).div_const 2

theorem exists_coordinate_partial_bounds (F : ReversibleMetric n) (p : Sphere n)
    {y : Coordinates n} (hy : y ∈ (extChartAt (𝓡 n) p).target) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ Metric.closedBall y ε ⊆ (extChartAt (𝓡 n) p).target ∧
      ∀ x ∈ Metric.closedBall y ε, ∀ w : Coordinates n,
        ‖positionTerm (coordinateLagrangian F p) (x, w)‖ ≤ C * ‖w‖ ^ 2 ∧
        ‖velocityTerm (coordinateLagrangian F p) (x, w)‖ ≤ C * ‖w‖ :=
  Finsler.ParametricQuadratic.exists_local_partial_bounds (chartTarget_isOpen p)
    (coordinateLagrangian_velocity_smul F p)
    (fun _ hz hv => coordinateLagrangian_smoothAt_nonzero F p hz hv) hy

end

end Finsler.CoordinateEnergyRegularity
