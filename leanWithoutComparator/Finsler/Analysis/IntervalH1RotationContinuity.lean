module

public import Finsler.Analysis.IntervalCircleLp

/-! Strong H¹ continuity of the genuine circle action. Actual L² values and
actual weak velocities rotate through measure-preserving circle translations.
The measurable section is not asserted continuous. -/

@[expose] public section

namespace Finsler.SobolevRotation

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCircleRepresentative Finsler.SobolevPeriodicVelocity
open Finsler.SobolevShift Finsler.SobolevCircleAction Finsler.CircleLpTransfer
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def rotateLpL (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (a : Phase) :
    Lp E 2 intervalMeasure →L[ℝ] Lp E 2 intervalMeasure :=
  (toIntervalL E).comp ((translateL E a).comp (toCircleL E))

theorem rotateLpL_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 intervalMeasure) (a : Phase) :
    rotateLpL E a f =ᵐ[intervalMeasure] fun t => f (sectionPoint (a + (t : Phase))) := by
  filter_upwards [toIntervalL_ae (translateL E a (toCircleL E f)),
    cover_measurePreserving.quasiMeasurePreserving.ae_eq_comp (translateL_ae (toCircleL E f) a),
    (cover_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      ((translation_measurePreserving a).quasiMeasurePreserving.ae_eq_comp (toCircleL_ae f)))]
      with t h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃)

theorem rotateLpL_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Lp E 2 intervalMeasure) (a : Phase) : ‖rotateLpL E a f‖ = ‖f‖ := by
  change ‖toIntervalL E (translateL E a (toCircleL E f))‖ = _
  rw [toIntervalL_norm, translateL_norm, toCircleL_norm]

theorem rotateLpL_joint_continuous (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (fun p : Lp E 2 intervalMeasure × Phase => rotateLpL E p.2 p.1) :=
  (toIntervalL E).continuous.comp ((translateL_joint_continuous E).comp
    (((toCircleL E).continuous.comp continuous_fst).prodMk continuous_snd))

theorem sectionPoint_mem (x : Phase) : sectionPoint x ∈ Icc (0 : ℝ) 1 := by
  have h := (AddCircle.equivIoc (1 : ℝ) 0 x).property
  change ((AddCircle.equivIoc (1 : ℝ) 0 x) : ℝ) ∈ Icc 0 1
  simpa only [zero_add] using Ioc_subset_Icc_self h

theorem value_toCircle_ae {n : ℕ} (u : periodicSubmodule n) :
    toCircleL (Ambient n) (value (u : Space n)) =ᵐ[volume] circleMap u := by
  filter_upwards [toCircleL_ae (value (u : Space n)),
    section_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (value_ae_continuousRepresentative (u : Space n))] with x hx hq
  simp only [Function.comp_apply] at hq
  exact hx.trans (hq.trans (by
    rw [← circleMap_coe u (sectionPoint_mem x), sectionPoint_coe]))

theorem rotateLpL_value_ae {n : ℕ} (u : periodicSubmodule n) (a : Phase) :
    rotateLpL (Ambient n) a (value (u : Space n)) =ᵐ[intervalMeasure]
      fun t => circleMap u (a + (t : Phase)) := by
  filter_upwards [toIntervalL_ae (translateL (Ambient n) a (toCircleL (Ambient n) (value (u : Space n)))),
    cover_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      (translateL_ae (toCircleL (Ambient n) (value (u : Space n))) a),
    cover_measurePreserving.quasiMeasurePreserving.ae_eq_comp
      ((translation_measurePreserving a).quasiMeasurePreserving.ae_eq_comp (value_toCircle_ae u))]
      with t h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃)

theorem periodicVelocity_eq_section {n : ℕ} (u : periodicSubmodule n) (t : ℝ) :
    periodicVelocity u t = velocity (u : Space n) (sectionPoint (t : Phase)) := rfl

theorem value_shiftData_eq_rotateLpL {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    value (shiftData u a) = rotateLpL (Ambient n) (a : Phase) (value (u : Space n)) := by
  rw [value_shiftData]
  apply Lp.ext
  filter_upwards [shiftValueLp_ae u a, rotateLpL_value_ae u (a : Phase)] with t h₁ h₂
  rw [h₁, h₂, realMap_apply, AddCircle.coe_add, add_comm (t : Phase)]

theorem velocity_shiftData_eq_rotateLpL {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    velocity (shiftData u a) = rotateLpL (Ambient n) (a : Phase) (velocity (u : Space n)) := by
  apply Lp.ext
  filter_upwards [velocity_shiftData_ae u a, rotateLpL_ae (velocity (u : Space n)) (a : Phase)]
    with t h₁ h₂
  rw [h₁, h₂]
  change periodicVelocity u (t + a) = _
  rw [periodicVelocity_eq_section]
  have hp : ((t + a : ℝ) : Phase) = (a : Phase) + (t : Phase) := by
    rw [AddCircle.coe_add]
    exact add_comm _ _
  exact congrArg (fun x : Phase => velocity (u : Space n) (sectionPoint x)) hp

def phaseShiftData {n : ℕ} (u : periodicSubmodule n) (a : Phase) : Space n :=
  shiftData u (circlePoint a)

theorem value_phaseShiftData {n : ℕ} (u : periodicSubmodule n) (a : Phase) :
    value (phaseShiftData u a) = rotateLpL (Ambient n) a (value (u : Space n)) := by
  change value (shiftData u (circlePoint a)) = _
  rw [value_shiftData_eq_rotateLpL, circlePoint_coe]

theorem velocity_phaseShiftData {n : ℕ} (u : periodicSubmodule n) (a : Phase) :
    velocity (phaseShiftData u a) = rotateLpL (Ambient n) a (velocity (u : Space n)) := by
  change velocity (shiftData u (circlePoint a)) = _
  rw [velocity_shiftData_eq_rotateLpL, circlePoint_coe]

theorem phaseShiftData_joint_continuous (n : ℕ) :
    Continuous (fun p : periodicSubmodule n × Phase => phaseShiftData p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_value_velocity.mpr
  constructor
  · simp_rw [value_phaseShiftData]
    exact ((rotateLpL_joint_continuous (Ambient n)).comp
      (((valueL n).continuous.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd)).continuousAt
  · simp_rw [velocity_phaseShiftData]
    exact ((rotateLpL_joint_continuous (Ambient n)).comp
      (((velocityL n).continuous.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd)).continuousAt

theorem rotateSphere_joint_continuous (n : ℕ) :
    Continuous (fun p : SphereLoop n × Phase => rotateSphere p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply sphereLoop_tendsto_iff.mpr
  have hd : Continuous (fun u : SphereLoop n => u.data) :=
    (sphereLoop_data_isometry n).continuous.subtype_mk (fun u => u.data.property)
  exact ((phaseShiftData_joint_continuous n).comp
    ((hd.comp continuous_fst).prodMk continuous_snd)).continuousAt

theorem sphere_action_continuous (n : ℕ) :
    Continuous (fun p : Phase × SphereLoop n => p.1 +ᵥ p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply sphereLoop_tendsto_iff.mpr
  have hd : Continuous (fun u : SphereLoop n => u.data) :=
    (sphereLoop_data_isometry n).continuous.subtype_mk (fun u => u.data.property)
  exact ((phaseShiftData_joint_continuous n).comp
    ((hd.comp continuous_snd).prodMk continuous_fst)).continuousAt

instance (n : ℕ) : ContinuousVAdd Phase (SphereLoop n) where
  continuous_vadd := sphere_action_continuous n

end

end Finsler.SobolevRotation
