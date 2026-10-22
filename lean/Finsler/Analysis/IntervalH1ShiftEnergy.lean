module

public import Finsler.Analysis.IntervalH1CircleAction

/-! Actual Finsler energy invariance for arbitrary sphere H¹ rotations.
The periodized actual weak jet gives an integrable periodic density. Shifting
its genuine graph preserves its integral and hence the actual energy cuts.
Strong-H¹ continuity of the circle action remains a separate obligation. 
Strong-H¹ rotation continuity and isometry are proved downstream in
IntervalH1RotationContinuity and IntervalH1RotationIsometry. -/

@[expose] public section

namespace Finsler.SobolevShiftEnergy

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCircleRepresentative Finsler.SobolevPeriodicVelocity
open Finsler.SobolevShift Finsler.SobolevCircleAction Finsler.AmbientLagrangian
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

def periodicDensity {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (u : SphereLoop n) (t : ℝ) : ℝ :=
  lagrangian F (realMap u.data t, periodicVelocity u.data t)

theorem periodicDensity_ae {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (u : SphereLoop n) :
    periodicDensity F u =ᵐ[intervalMeasure] fun t => lagrangian F (weakJet u t) := by
  filter_upwards [periodicVelocity_ae u.data, ae_restrict_mem measurableSet_Ioo] with t hv ht
  change lagrangian F (realMap u.data t, periodicVelocity u.data t) =
    lagrangian F (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)
  rw [realMap_eqOn u.data (Ioo_subset_Icc_self ht), hv]

theorem periodicDensity_periodic {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (u : SphereLoop n) :
    Function.Periodic (periodicDensity F u) 1 := by
  intro t
  change lagrangian F (realMap u.data (t + 1), periodicVelocity u.data (t + 1)) =
    lagrangian F (realMap u.data t, periodicVelocity u.data t)
  rw [realMap_periodic u.data t, periodicVelocity_periodic u.data t]

theorem periodicDensity_integrable {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (u : SphereLoop n) :
    Integrable (periodicDensity F u) intervalMeasure :=
  (density_integrable F u).congr (periodicDensity_ae F u).symm

theorem periodicDensity_intervalIntegrable {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (u : SphereLoop n) (a b : ℝ) : IntervalIntegrable (periodicDensity F u) volume a b := by
  have h : IntervalIntegrable (periodicDensity F u) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (periodicDensity_integrable F u)
  exact (periodicDensity_periodic F u).intervalIntegrable₀ (by norm_num) h a b

theorem energy_eq_periodicDensity {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (u : SphereLoop n) :
    energy F u = ∫ t in (0 : ℝ)..1, periodicDensity F u t := by
  change (∫ t, lagrangian F (weakJet u t) ∂intervalMeasure) = _
  rw [integral_congr_ae (periodicDensity_ae F u).symm]
  change (∫ t in Ioo (0 : ℝ) 1, periodicDensity F u t) = _
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]

theorem density_shiftSphere_ae {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (u : SphereLoop n) (a : ℝ) :
    (fun t => lagrangian F (weakJet (shiftSphere u a) t)) =ᵐ[intervalMeasure]
      fun t => periodicDensity F u (t + a) := by
  filter_upwards [velocity_shiftData_ae u.data a, ae_restrict_mem measurableSet_Ioo] with t hv ht
  change lagrangian F (continuousRepresentative (shiftData u.data a) t, velocity (shiftData u.data a) t) =
    lagrangian F (realMap u.data (t + a), periodicVelocity u.data (t + a))
  rw [representative_shiftData u.data a (Ioo_subset_Icc_self ht), hv]
  rfl

theorem energy_shiftSphere {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (u : SphereLoop n) (a : ℝ) : energy F (shiftSphere u a) = energy F u := by
  change (∫ t, lagrangian F (weakJet (shiftSphere u a) t) ∂intervalMeasure) = _
  rw [integral_congr_ae (density_shiftSphere_ae F u a)]
  have h : (∫ t, periodicDensity F u (t + a) ∂intervalMeasure) =
      ∫ t in (0 : ℝ)..1, periodicDensity F u (t + a) := by
    change (∫ t in Ioo (0 : ℝ) 1, periodicDensity F u (t + a)) = _
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  rw [h, intervalIntegral.integral_comp_add_right]
  rw [zero_add, energy_eq_periodicDensity F u]
  simpa only [zero_add, add_comm] using (periodicDensity_periodic F u).intervalIntegral_add_eq a 0

theorem energy_vadd {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n)
    (a : SobolevCircleRepresentative.Circle) (u : SphereLoop n) : energy F (a +ᵥ u) = energy F u :=
  energy_shiftSphere F u (circlePoint a)

theorem vadd_mem_energyCut_iff {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (b : ℝ)
    (a : SobolevCircleRepresentative.Circle) (u : SphereLoop n) :
    a +ᵥ u ∈ Finsler.SobolevReflectionAction.energyCut F b ↔
      u ∈ Finsler.SobolevReflectionAction.energyCut F b := by
  rw [Finsler.SobolevReflectionAction.mem_energyCut, Finsler.SobolevReflectionAction.mem_energyCut,
    energy_vadd]

instance {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (b : ℝ) :
    AddAction SobolevCircleRepresentative.Circle (Finsler.SobolevReflectionAction.energyCut F b) where
  vadd a u := ⟨a +ᵥ (u : SphereLoop n), (vadd_mem_energyCut_iff F b a u).mpr u.property⟩
  zero_vadd u := by
    apply Subtype.ext
    exact zero_vadd _ _
  add_vadd a c u := by
    apply Subtype.ext
    exact add_vadd _ _ _

theorem energyCut_vadd_val {n : ℕ} (F : Finsler.Geometry.ReversibleMetric n) (b : ℝ)
    (a : SobolevCircleRepresentative.Circle) (u : Finsler.SobolevReflectionAction.energyCut F b) :
    ((a +ᵥ u : Finsler.SobolevReflectionAction.energyCut F b) : SphereLoop n) = a +ᵥ (u : SphereLoop n) := rfl

end

end Finsler.SobolevShiftEnergy
