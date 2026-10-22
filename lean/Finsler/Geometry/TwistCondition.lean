module

public import Finsler.Geometry.EnergyMomentum
public import Finsler.Geometry.CoordinateSpray

/-! The twist condition for the energy of short segments. In the coordinates of a chart package,
the derivative of the joint energy of the segment from y to z in the first endpoint is minus the
initial momentum, the velocity derivative of the Lagrangian at the initial velocity V(y, z) of
the segment. The initial velocity has injective derivative in z (the exponential map is a left
inverse), and the velocity Hessian of the Lagrangian is positive at nonzero velocity (strong
convexity). Hence the mixed second derivative of the joint energy is nondegenerate: a direction
v at the second endpoint with vanishing mixed second derivative against all directions at the
first endpoint is zero. -/

@[expose] public section

namespace Finsler.TwistCondition

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.ExpInverseRegularity
open Finsler.EikonalChart Finsler.EnergyJointSmooth Finsler.SegmentMomentum
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

/-- Near a pair off the diagonal in the inverse domain, the pairs with the same first point stay
off the diagonal in the inverse domain. -/
theorem eventually_good {y z : Coordinates n} (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) :
    ∀ᶠ z' in 𝓝 z, ‖z' - y‖ < D.ρ / 2 ∧ z' ≠ y := by
  have hc : ContinuousAt (fun z' : Coordinates n => ‖z' - y‖) z :=
    (continuous_id.sub continuous_const).norm.continuousAt
  exact (hc.eventually (gt_mem_nhds hz)).and (eventually_ne_nhds hne)

/-- The derivative of the local inverse of the exponential map in the endpoint is injective. -/
theorem expInv_fderiv_injective {y z : Coordinates n} (hy : y ∈ closedBall y₀ r)
    (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) :
    Function.Injective (fderiv ℝ (fun z' => expInv D y z') z) := by
  have hV := expInv_ne_zero D hy hz.le hne
  have hVρ : ‖expInv D y z‖ < D.ρ := by
    have h := norm_expInv_le D hy hz.le
    linarith
  obtain ⟨T, -, hT⟩ := exists_expMap_hasFDerivAt D hy hV hVρ
  have hdV : HasFDerivAt (fun z' => expInv D y z') (fderiv ℝ (fun z' => expInv D y z') z) z :=
    ((expInv_contDiffAt D hy hz hne).differentiableAt (by norm_num)).hasFDerivAt
  have hcomp : HasFDerivAt (fun z' => expMap D y (expInv D y z'))
      ((ContinuousLinearMap.id ℝ (Coordinates n) + T).comp
        (fderiv ℝ (fun z' => expInv D y z') z)) z := hT.comp z hdV
  have hid : (fun z' => expMap D y (expInv D y z')) =ᶠ[𝓝 z] fun z' => z' := by
    filter_upwards [eventually_good D hz hne] with z' hz'
    rw [expMap_eq D hy]
    exact (expInv_spec D hy hz'.1.le).2
  have h1 := hcomp.unique ((hasFDerivAt_id z).congr_of_eventuallyEq hid)
  intro a b hab
  have ha : (ContinuousLinearMap.id ℝ (Coordinates n) + T)
      (fderiv ℝ (fun z' => expInv D y z') z a) = a :=
    congrArg (fun L : Coordinates n →L[ℝ] Coordinates n => L a) h1
  have hb : (ContinuousLinearMap.id ℝ (Coordinates n) + T)
      (fderiv ℝ (fun z' => expInv D y z') z b) = b :=
    congrArg (fun L : Coordinates n →L[ℝ] Coordinates n => L b) h1
  rw [← ha, ← hb, hab]

/-- The derivative of the joint energy in the first endpoint is minus the initial momentum. -/
theorem fderiv_jointEnergy_left {y z : Coordinates n} (hy : y ∈ ball y₀ r)
    (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) (η : Coordinates n) :
    fderiv ℝ (jointEnergy D) (y, z) (η, 0) =
      -(velocityTerm (coordinateLagrangian F p) (y, expInv D y z) η) := by
  rw [(jointEnergy_hasFDerivAt D hy hz hne).fderiv]
  change (velocityTerm (coordinateLagrangian F p) (z, endVel D y z)) (0 : Coordinates n) -
    (velocityTerm (coordinateLagrangian F p) (y, expInv D y z)) η = _
  rw [map_zero, zero_sub]

/-- **The twist condition in a chart package.** A direction at the second endpoint whose mixed
second derivative of the joint energy against every direction at the first endpoint vanishes is
zero. -/
theorem joint_twist {y z : Coordinates n} (hy : y ∈ ball y₀ r)
    (hyt : y ∈ (extChartAt (𝓡 n) p).target) (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y)
    {v : Coordinates n}
    (h : ∀ η : Coordinates n,
      fderiv ℝ (fun z' => fderiv ℝ (jointEnergy D) (y, z') (η, 0)) z v = 0) : v = 0 := by
  have hy' := ball_subset_closedBall hy
  have hV := expInv_ne_zero D hy' hz.le hne
  have hLs : ContDiffAt ℝ 2 (coordinateLagrangian F p) (y, expInv D y z) :=
    (coordinateLagrangian_smoothAt_nonzero F p (z := (y, expInv D y z)) hyt hV).of_le (by simp)
  have hvt0 : DifferentiableAt ℝ (velocityTerm (coordinateLagrangian F p)) (y, expInv D y z) := by
    rw [velocityTerm_eq]
    exact restrictVel.differentiableAt.comp _
      ((hLs.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hvt : HasFDerivAt (fun w => velocityTerm (coordinateLagrangian F p) (y, w))
      (velocityHessian (coordinateLagrangian F p) (y, expInv D y z)) (expInv D y z) :=
    (hvt0.comp (expInv D y z)
      (hasFDerivAt_prodMk_right y (expInv D y z)).differentiableAt).hasFDerivAt
  have hdV : HasFDerivAt (fun z' => expInv D y z') (fderiv ℝ (fun z' => expInv D y z') z) z :=
    ((expInv_contDiffAt D hy' hz hne).differentiableAt (by norm_num)).hasFDerivAt
  have hkey : ∀ η : Coordinates n,
      velocityHessian (coordinateLagrangian F p) (y, expInv D y z)
        (fderiv ℝ (fun z' => expInv D y z') z v) η = 0 := by
    intro η
    have hev : (fun z' => fderiv ℝ (jointEnergy D) (y, z') (η, 0)) =ᶠ[𝓝 z]
        fun z' => -(velocityTerm (coordinateLagrangian F p) (y, expInv D y z') η) := by
      filter_upwards [eventually_good D hz hne] with z' hz'
      exact fderiv_jointEnergy_left D hy hz'.1 hz'.2 η
    have hd : HasFDerivAt
        (fun z' => -(velocityTerm (coordinateLagrangian F p) (y, expInv D y z') η))
        (-((ContinuousLinearMap.apply ℝ ℝ η).comp
          ((velocityHessian (coordinateLagrangian F p) (y, expInv D y z)).comp
            (fderiv ℝ (fun z' => expInv D y z') z)))) z :=
      ((ContinuousLinearMap.apply ℝ ℝ η).hasFDerivAt.comp z (hvt.comp z hdV)).neg
    have h2 := h η
    rw [hev.fderiv_eq, hd.fderiv] at h2
    have h3 : -(velocityHessian (coordinateLagrangian F p) (y, expInv D y z)
        (fderiv ℝ (fun z' => expInv D y z') z v) η) = 0 := h2
    exact neg_eq_zero.mp h3
  have hzero : fderiv ℝ (fun z' => expInv D y z') z v = 0 := by
    by_contra hcon
    have hpos := coordinate_velocityHessian_pos F p hyt hV hcon
    rw [hkey] at hpos
    exact lt_irrefl _ hpos
  exact expInv_fderiv_injective D hy' hz hne (hzero.trans (map_zero _).symm)

end

end Finsler.TwistCondition
