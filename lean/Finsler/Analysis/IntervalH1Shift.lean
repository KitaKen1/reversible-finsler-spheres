module

public import Finsler.Analysis.IntervalH1PeriodicVelocity

/-! Real starting-point shifts of the actual periodic weak H¹ sphere graph.
The new L² value and derivative are certified using the genuine periodized weak
velocity and its primitive. Algebraic circle laws and energy invariance are
proved downstream. Strong-H¹ joint continuity remains an open obligation. 
Strong-H¹ rotation continuity and isometry are proved downstream in
IntervalH1RotationContinuity and IntervalH1RotationIsometry. -/

@[expose] public section

namespace Finsler.SobolevShift

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCircleRepresentative Finsler.SobolevPeriodicVelocity
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem shiftValue_memLp {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    MemLp (fun t => realMap u (t + a)) 2 intervalMeasure :=
  Finsler.SmoothSobolev.continuous_memLp_interval
    ((realMap u).continuous.comp (continuous_id.add continuous_const))

def shiftValueLp {n : ℕ} (u : periodicSubmodule n) (a : ℝ) : ValueLp n :=
  (shiftValue_memLp u a).toLp (fun t => realMap u (t + a))

theorem shiftValueLp_ae {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    shiftValueLp u a =ᵐ[intervalMeasure] fun t => realMap u (t + a) :=
  (shiftValue_memLp u a).coeFn_toLp

def shiftVelocityLp {n : ℕ} (u : periodicSubmodule n) (a : ℝ) : ValueLp n :=
  (shiftVelocity_memLp u a).toLp (shiftVelocity u a)

theorem shiftVelocityLp_ae {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    shiftVelocityLp u a =ᵐ[intervalMeasure] shiftVelocity u a :=
  (shiftVelocity_memLp u a).coeFn_toLp

def shiftDerivativeLp {n : ℕ} (u : periodicSubmodule n) (a : ℝ) : DerivativeLp n :=
  (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 intervalMeasure (shiftVelocityLp u a)

theorem shiftDerivativeLp_ae {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    shiftDerivativeLp u a =ᵐ[intervalMeasure] shiftDerivative u a := by
  let L : Ambient n →L[ℝ] (ℝ →L[ℝ] Ambient n) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.coeFn_compLpL (p := 2) (μ := intervalMeasure) (shiftVelocityLp u a)
  filter_upwards [h, shiftVelocityLp_ae u a] with t hD hv
  change (L.compLpL 2 intervalMeasure (shiftVelocityLp u a)) t = _
  rw [hD, hv]
  rfl

theorem shiftValue_hasWeakFDeriv {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    TauCeti.HasWeakFDerivOn volume unitInterval (base n (shiftValueLp u a))
      (shiftDerivativeLp u a) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have h := (TauCeti.hasWeakFDerivOn_iff.mp (shifted_realMap_hasWeakFDeriv u a)) d
  have hval : (fun t => realMap u (t + a)) =ᵐ[intervalMeasure] (base n (shiftValueLp u a)) :=
    (shiftValueLp_ae u a).symm
  have hD : (fun t => shiftDerivative u a t d) =ᵐ[intervalMeasure]
      fun t => shiftDerivativeLp u a t d := by
    filter_upwards [shiftDerivativeLp_ae u a] with t ht
    exact congrArg (fun D : ℝ →L[ℝ] Ambient n => D d) ht.symm
  exact (h.congr_ae hval).congr_ae_deriv hD

def shiftData {n : ℕ} (u : periodicSubmodule n) (a : ℝ) : Space n :=
  TauCeti.WeakDerivStep.mk (base n) (shiftValueLp u a) (shiftDerivativeLp u a)
    (shiftValue_hasWeakFDeriv u a)

theorem value_shiftData {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    value (shiftData u a) = shiftValueLp u a := by
  change TauCeti.WeakDerivStep.prevL (base n) (shiftData u a) = _
  rw [TauCeti.WeakDerivStep.prevL_apply]
  exact TauCeti.WeakDerivStep.prev_mk _ _ _ _

theorem derivative_shiftData {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    derivative (shiftData u a) = shiftDerivativeLp u a := by
  change TauCeti.WeakDerivStep.weakFDerivL (base n) (shiftData u a) = _
  rw [TauCeti.WeakDerivStep.weakFDerivL_apply]
  exact TauCeti.WeakDerivStep.weakFDeriv_mk _ _ _ _

theorem velocity_shiftData_ae {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    velocity (shiftData u a) =ᵐ[intervalMeasure] shiftVelocity u a := by
  filter_upwards [velocity_apply_ae (shiftData u a), shiftDerivativeLp_ae u a] with t hv hD
  rw [derivative_shiftData, hD, shiftDerivative_apply] at hv
  simpa only [one_smul] using hv

theorem representative_shiftData {n : ℕ} (u : periodicSubmodule n) (a : ℝ) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    continuousRepresentative (shiftData u a) t = realMap u (t + a) := by
  apply continuous_representative_unique (continuousRepresentative_continuousOn _)
    ((realMap u).continuous.comp (continuous_id.add continuous_const)).continuousOn
    (value_ae_continuousRepresentative _) _ ht
  rw [value_shiftData]
  exact shiftValueLp_ae u a

def periodicShift {n : ℕ} (u : periodicSubmodule n) (a : ℝ) : periodicSubmodule n :=
  ⟨shiftData u a, by
    rw [mem_periodicSubmodule_iff]
    change continuousRepresentative (shiftData u a) 1 = continuousRepresentative (shiftData u a) 0
    rw [representative_shiftData u a (by norm_num), representative_shiftData u a (by norm_num)]
    simpa only [zero_add, add_zero, add_comm] using realMap_periodic u a⟩

theorem periodicShift_val {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    (periodicShift u a : Space n) = shiftData u a := rfl

def shiftSphere {n : ℕ} (u : SphereLoop n) (a : ℝ) : SphereLoop n where
  data := periodicShift u.data a
  sphere_constraint t := by
    change ‖continuousRepresentative (shiftData u.data a) t‖ = 1
    rw [representative_shiftData u.data a t.property, realMap_apply]
    exact circleMap_sphere_norm u ((t : ℝ) + a)

theorem shiftSphere_data {n : ℕ} (u : SphereLoop n) (a : ℝ) :
    (shiftSphere u a).data = periodicShift u.data a := rfl

theorem sphereRepresentative_shiftSphere {n : ℕ} (u : SphereLoop n) (a : ℝ) (t : ClosedInterval) :
    sphereRepresentative (shiftSphere u a) t = shiftedSphereMap u (a : SobolevCircleRepresentative.Circle)
      ((t : ℝ) : SobolevCircleRepresentative.Circle) := by
  apply Subtype.ext
  change continuousRepresentative (shiftData u.data a) t = circleMap u.data ((a : SobolevCircleRepresentative.Circle) + (t : ℝ))
  rw [representative_shiftData u.data a t.property, realMap_apply, AddCircle.coe_add]
  congr 1
  exact add_comm _ _

theorem shiftSphere_zero {n : ℕ} (u : SphereLoop n) : shiftSphere u 0 = u := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  rw [sphereRepresentative_shiftSphere]
  change shiftedSphereMap u (0 : SobolevCircleRepresentative.Circle) (t : ℝ) = _
  rw [shiftedSphereMap_zero, sphereCircleMap_coe]

theorem circleMap_shiftSphere {n : ℕ} (u : SphereLoop n) (a : ℝ) :
    sphereCircleMap (shiftSphere u a) = shiftedSphereMap u (a : SobolevCircleRepresentative.Circle) := by
  apply ContinuousMap.ext
  intro x
  rw [← circlePoint_coe x, sphereCircleMap_coe, sphereRepresentative_shiftSphere, circlePoint_coe]

theorem sphereImage_shiftSphere {n : ℕ} (u : SphereLoop n) (a : ℝ) :
    Finsler.SobolevReverse.sphereImage (shiftSphere u a) = Finsler.SobolevReverse.sphereImage u := by
  rw [← sphereCircleMap_image, circleMap_shiftSphere, shiftedSphereMap_image]

end

end Finsler.SobolevShift
