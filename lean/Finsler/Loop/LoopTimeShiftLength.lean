module

public import Finsler.Analysis.IntervalH1ShiftEnergy
public import Finsler.Analysis.IntervalH1Length
public import Finsler.Analysis.IntervalH1RotationContinuity

/-! Genuine time shifts preserve the actual Finsler length of H1 loops,
not only energy. This supplies length-controlled half-period homotopies. -/

@[expose] public section
namespace Finsler.LoopTimeShiftLength
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevShiftEnergy Finsler.SobolevShift Finsler.SobolevCircleAction
open Finsler.SobolevCircleRepresentative MeasureTheory Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n)

def periodicSpeed (t : ℝ) : ℝ := Real.sqrt (periodicDensity F u t)

theorem periodicSpeed_ae : periodicSpeed F u =ᵐ[intervalMeasure] SobolevLength.speed F u :=
  (periodicDensity_ae F u).fun_comp Real.sqrt


theorem periodicSpeed_periodic : Function.Periodic (periodicSpeed F u) 1 :=
  (periodicDensity_periodic F u).comp Real.sqrt


theorem periodicSpeed_integrable : Integrable (periodicSpeed F u) intervalMeasure :=
  (SobolevLength.speed_integrable F u).congr (periodicSpeed_ae F u).symm


theorem length_eq_periodicSpeed : SobolevLength.length F u = ∫ t in (0 : ℝ)..1, periodicSpeed F u t := by
  rw [SobolevLength.length, integral_congr_ae (periodicSpeed_ae F u).symm]
  change (∫ t in Ioo (0 : ℝ) 1, periodicSpeed F u t) = _
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]


theorem speed_shift_ae (a : ℝ) : SobolevLength.speed F (shiftSphere u a) =ᵐ[intervalMeasure]
    fun t => periodicSpeed F u (t + a) :=
  (density_shiftSphere_ae F u a).fun_comp Real.sqrt


theorem length_shift (a : ℝ) : SobolevLength.length F (shiftSphere u a) = SobolevLength.length F u := by
  rw [SobolevLength.length, integral_congr_ae (speed_shift_ae F u a)]
  have h : (∫ t, periodicSpeed F u (t + a) ∂intervalMeasure) = ∫ t in (0 : ℝ)..1, periodicSpeed F u (t + a) := by
    change (∫ t in Ioo (0 : ℝ) 1, periodicSpeed F u (t + a)) = _
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  rw [h, intervalIntegral.integral_comp_add_right, zero_add, length_eq_periodicSpeed F u]
  simpa only [zero_add, add_comm] using (periodicSpeed_periodic F u).intervalIntegral_add_eq a 0


theorem length_vadd (a : SobolevCircleRepresentative.Circle) : SobolevLength.length F (a +ᵥ u) = SobolevLength.length F u :=
  length_shift F u (circlePoint a)

end
end Finsler.LoopTimeShiftLength
