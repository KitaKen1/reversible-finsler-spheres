module

public import Finsler.Analysis.SphereDistance
public import Finsler.Geometry.SprayEnergy

/-! Actual H¹ sphere paths from C¹ curves and from C¹ curves in a sphere chart. A curve that is
continuous on [0,1], differentiable inside with a derivative continuous on [0,1], is the original
weak graph element with that velocity; its path energy is the integral of the ambient density.
Composing a C¹ chart curve with the inverse chart gives a sphere path whose energy is the
integral of the coordinate Lagrangian along the chart curve; along a coordinate geodesic the
density is constant, so the energy is the initial value F²(p,v). -/

@[expose] public section

namespace Finsler.ChartPath

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevOfPrimitive Finsler.SobolevSpherePath Finsler.SphereDistance
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity
open Finsler.EulerCovariance Finsler.LagrangianSpray Finsler.SprayEnergy
open MeasureTheory Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

variable {n : ℕ}

section C1

variable {c c' : ℝ → Ambient n} (hc : ContinuousOn c (Icc 0 1))
  (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt c (c' t) t) (hc' : ContinuousOn c' (Icc 0 1))

include hc hd hc' in
theorem prim_eq : ∀ t ∈ Icc (0 : ℝ) 1, c t = c 0 + ∫ s in (0 : ℝ)..t, c' s := by
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 1 := Icc_subset_Icc le_rfl ht.2
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hc.mono hsub)
    (fun x hx => hd x ⟨hx.1, hx.2.trans_le ht.2⟩)
    ((hc'.mono hsub).intervalIntegrable_of_Icc ht.1)
  rw [h]
  abel

/-- The graph element of a C¹ curve on [0,1]. -/
def ofC1 : Space n := ofPrimitive hc (memLp_of_continuousOn hc') (prim_eq hc hd hc')

theorem representative_ofC1 {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (ofC1 hc hd hc') t = c t :=
  representative_ofPrimitive _ _ _ ht

theorem velocity_ofC1_ae : velocity (ofC1 hc hd hc') =ᵐ[intervalMeasure] c' :=
  velocity_ofPrimitive_ae _ _ _

theorem pathEnergy_ofC1 (F : ReversibleMetric n) :
    pathEnergy F (ofC1 hc hd hc') = ∫ t in (0 : ℝ)..1, lagrangian F (c t, c' t) := by
  have hae : (fun t => lagrangian F (continuousRepresentative (ofC1 hc hd hc') t,
      velocity (ofC1 hc hd hc') t)) =ᵐ[intervalMeasure] fun t => lagrangian F (c t, c' t) := by
    filter_upwards [velocity_ofC1_ae hc hd hc', ae_restrict_mem measurableSet_Ioo] with t hv ht
    rw [representative_ofC1 hc hd hc' (Ioo_subset_Icc_self ht), hv]
  change (∫ t, lagrangian F (continuousRepresentative (ofC1 hc hd hc') t,
    velocity (ofC1 hc hd hc') t) ∂intervalMeasure) = _
  rw [integral_congr_ae hae]
  change (∫ t in Ioo (0 : ℝ) 1, lagrangian F (c t, c' t)) = _
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

theorem ofC1_mem (hs : ∀ t ∈ Icc (0 : ℝ) 1, ‖c t‖ = 1) :
    ofC1 hc hd hc' ∈ pathsBetween n (c 0) (c 1) := by
  refine ⟨?_, representative_ofC1 hc hd hc' (left_mem_Icc.mpr zero_le_one),
    representative_ofC1 hc hd hc' (right_mem_Icc.mpr zero_le_one)⟩
  intro t ht
  rw [representative_ofC1 hc hd hc' ht]
  exact hs t ht

end C1

section Chart

variable (p : Sphere n) {y y' : ℝ → Coordinates n}
  (hy : ∀ t ∈ Icc (0 : ℝ) 1, y t ∈ (extChartAt (𝓡 n) p).target)
  (hyc : ContinuousOn y (Icc 0 1)) (hyd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt y (y' t) t)
  (hy' : ContinuousOn y' (Icc 0 1))

/-- The sphere curve of a chart curve. -/
def sphereCurve (y : ℝ → Coordinates n) (t : ℝ) : Ambient n := inverseAmbient p (y t)

/-- Its velocity. -/
def sphereVel (y y' : ℝ → Coordinates n) (t : ℝ) : Ambient n :=
  fderiv ℝ (inverseAmbient p) (y t) (y' t)

include hy hyc in
theorem sphereCurve_continuousOn : ContinuousOn (sphereCurve p y) (Icc 0 1) := by
  intro t ht
  exact ((inverseAmbient_smoothAt p (hy t ht)).continuousAt.comp_continuousWithinAt (hyc t ht))

include hy hyd in
theorem sphereCurve_hasDerivAt {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (sphereCurve p y) (sphereVel p y y' t) t := by
  have hφ := ((inverseAmbient_smoothAt p (hy t (Ioo_subset_Icc_self ht))).differentiableAt
    (by simp)).hasFDerivAt
  exact hφ.comp_hasDerivAt t (hyd t ht)

include hy hyc hy' in
theorem sphereVel_continuousOn : ContinuousOn (sphereVel p y y') (Icc 0 1) := by
  intro t ht
  have hD : ContinuousAt (fderiv ℝ (inverseAmbient p)) (y t) :=
    ((inverseAmbient_smoothAt p (hy t ht)).fderiv_right (m := 1) (by simp)).continuousAt
  exact (hD.comp_continuousWithinAt (hyc t ht)).clm_apply (hy' t ht)

/-- The actual H¹ sphere path of a C¹ chart curve. -/
def chartPath : Space n :=
  ofC1 (sphereCurve_continuousOn p hy hyc) (fun _ ht => sphereCurve_hasDerivAt p hy hyd ht)
    (sphereVel_continuousOn p hy hyc hy')

theorem chartPath_mem :
    chartPath p hy hyc hyd hy' ∈
      pathsBetween n (inverseAmbient p (y 0)) (inverseAmbient p (y 1)) :=
  ofC1_mem _ _ _ fun t _ => by simp [sphereCurve, inverseAmbient]

/-- The energy of a chart path is the integral of the coordinate Lagrangian. -/
theorem pathEnergy_chartPath (F : ReversibleMetric n) :
    pathEnergy F (chartPath p hy hyc hyd hy') =
      ∫ t in (0 : ℝ)..1, coordinateLagrangian F p (y t, y' t) :=
  pathEnergy_ofC1 _ _ _ F

end Chart

section Geodesic

variable (F : ReversibleMetric n) (p : Sphere n) {y : ℝ → Coordinates n}
  (hC2 : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 y t)
  (hy : ∀ t ∈ Icc (0 : ℝ) 1, y t ∈ (extChartAt (𝓡 n) p).target)
  (hv : ∀ t ∈ Icc (0 : ℝ) 1, deriv y t ≠ 0)
  (hacc : ∀ t ∈ Icc (0 : ℝ) 1,
    deriv (deriv y) t = spray (coordinateLagrangian F p) (curveJet y t))

include hC2 hy hv hacc in
/-- Along a coordinate geodesic the coordinate density is constant on [0,1]. -/
theorem density_const {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    coordinateLagrangian F p (curveJet y t) = coordinateLagrangian F p (curveJet y 0) := by
  have hd : ∀ s ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r => coordinateLagrangian F p (curveJet y r)) 0 s :=
    fun s hs => coordinate_lagrangian_hasDerivAt_zero F p (hC2 s hs) (hy s hs) (hv s hs) (hacc s hs)
  have hcont : ContinuousOn (fun r => coordinateLagrangian F p (curveJet y r)) (Icc 0 1) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  exact constant_of_has_deriv_right_zero hcont
    (fun s hs => (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt) t ht

include hC2 in
theorem continuousOn_of_C2 : ContinuousOn y (Icc 0 1) :=
  fun t ht => (hC2 t ht).continuousAt.continuousWithinAt

include hC2 in
theorem hasDerivAt_of_C2 : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt y (deriv y t) t :=
  fun t ht => ((hC2 t (Ioo_subset_Icc_self ht)).differentiableAt (by norm_num)).hasDerivAt

include hC2 in
theorem deriv_continuousOn_of_C2 : ContinuousOn (deriv y) (Icc 0 1) :=
  fun t ht => ((hC2 t ht).derivWithin (m := 1) (by norm_num)).continuousAt.continuousWithinAt

include hC2 hy hv hacc in
/-- The sphere path of a coordinate geodesic has energy equal to its initial density F²(p,v). -/
theorem pathEnergy_geodesic :
    pathEnergy F (chartPath p hy (continuousOn_of_C2 hC2) (hasDerivAt_of_C2 hC2)
      (deriv_continuousOn_of_C2 hC2)) = coordinateLagrangian F p (y 0, deriv y 0) := by
  rw [pathEnergy_chartPath]
  have heq : EqOn (fun t => coordinateLagrangian F p (y t, deriv y t))
      (fun _ => coordinateLagrangian F p (y 0, deriv y 0)) (uIcc 0 1) := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    exact density_const F p hC2 hy hv hacc ht
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_const, sub_zero, one_smul]

end Geodesic

end

end Finsler.ChartPath
