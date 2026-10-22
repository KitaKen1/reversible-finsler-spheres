module

public import Finsler.Analysis.IntervalH1IterationEstimates

/-! The actual half-speed root of a half-period-fixed sphere H¹ loop.
The rescaled actual weak velocity and primitive certify a genuine weak graph.
Its periodic endpoint condition uses actual half-period rotation fixedness. -/

@[expose] public section

namespace Finsler.SobolevHalfRoot

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCircleRepresentative Finsler.SobolevPeriodicVelocity
open Finsler.SobolevCircleAction Finsler.SobolevIteration Finsler.IntervalPrimitive
open Finsler.CircleLpTransfer MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def halfPhase : Phase := ((1 / 2 : ℝ) : Phase)

def halfFixedSet (n : ℕ) : Set (SphereLoop n) := {u | halfPhase +ᵥ u = u}

abbrev HalfFixed (n : ℕ) := ↥(halfFixedSet n)

theorem mem_halfFixedSet {n : ℕ} (u : SphereLoop n) :
    u ∈ halfFixedSet n ↔ halfPhase +ᵥ u = u := Iff.rfl

def rootVelocity {n : ℕ} (u : periodicSubmodule n) (t : ℝ) : Ambient n :=
  (1 / 2 : ℝ) • periodicVelocity u ((1 / 2 : ℝ) * t)

theorem rootVelocity_intervalIntegrable {n : ℕ} (u : periodicSubmodule n) :
    IntervalIntegrable (rootVelocity u) volume 0 1 := by
  have h := (periodicVelocity_intervalIntegrable u 0 (1 / 2)).comp_mul_left (c := (1 / 2 : ℝ))
  have h' : IntervalIntegrable (fun t => periodicVelocity u ((1 / 2 : ℝ) * t)) volume 0 1 := by
    norm_num only [zero_div, div_self (by norm_num : (1 / 2 : ℝ) ≠ 0)] at h
    exact h
  exact h'.smul (1 / 2 : ℝ)

theorem rootVelocity_sq_intervalIntegrable {n : ℕ} (u : periodicSubmodule n) :
    IntervalIntegrable (fun t => ‖rootVelocity u t‖ ^ 2) volume 0 1 := by
  have h := (periodicVelocity_sq_intervalIntegrable u 0 (1 / 2)).comp_mul_left
    (c := (1 / 2 : ℝ))
  have h' : IntervalIntegrable (fun t => ‖periodicVelocity u ((1 / 2 : ℝ) * t)‖ ^ 2)
      volume 0 1 := by
    norm_num only [zero_div, div_self (by norm_num : (1 / 2 : ℝ) ≠ 0)] at h
    exact h
  simpa only [rootVelocity, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), mul_pow] using h'.const_mul ((1 / 2 : ℝ) ^ 2)

theorem rootVelocity_memLp {n : ℕ} (u : periodicSubmodule n) :
    MemLp (rootVelocity u) 2 intervalMeasure := by
  have h : Integrable (rootVelocity u) intervalMeasure :=
    (rootVelocity_intervalIntegrable u).1.mono_set Ioo_subset_Ioc_self
  apply (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mpr
  exact (rootVelocity_sq_intervalIntegrable u).1.mono_set Ioo_subset_Ioc_self

theorem root_primitive_identity {n : ℕ} (u : periodicSubmodule n) (t : ℝ) :
    realMap u ((1 / 2 : ℝ) * t) = continuousRepresentative (u : Space n) 0 +
      primitive (rootVelocity u) t := by
  have hi : primitive (rootVelocity u) t = primitive (periodicVelocity u) ((1 / 2 : ℝ) * t) := by
    change (∫ s in (0 : ℝ)..t, (1 / 2 : ℝ) • periodicVelocity u ((1 / 2 : ℝ) * s)) =
      ∫ s in (0 : ℝ)..(1 / 2 : ℝ) * t, periodicVelocity u s
    rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left]
    simp only [mul_zero]
  rw [hi]
  exact realMap_eq_primitive u _

theorem root_realMap_hasWeakLineDeriv {n : ℕ} (u : periodicSubmodule n) :
    TauCeti.HasWeakLineDerivOn volume unitInterval
      (fun t => realMap u ((1 / 2 : ℝ) * t)) (rootVelocity u) 1 := by
  have hp := primitive_hasWeakLineDeriv (rootVelocity_intervalIntegrable u)
  have hc : TauCeti.HasWeakLineDerivOn volume unitInterval
      (fun _ : ℝ => continuousRepresentative (u : Space n) 0)
      (fun _ => (0 : Ambient n)) 1 := TauCeti.hasWeakLineDerivOn_const _
  have h := hc.add hp
  change TauCeti.HasWeakLineDerivOn volume unitInterval
    (fun t => continuousRepresentative (u : Space n) 0 + primitive (rootVelocity u) t)
    (fun t => 0 + rootVelocity u t) 1 at h
  have hv : (fun t => continuousRepresentative (u : Space n) 0 + primitive (rootVelocity u) t) =
      (fun t => realMap u ((1 / 2 : ℝ) * t)) := funext fun t => (root_primitive_identity u t).symm
  have hw : (fun t => (0 : Ambient n) + rootVelocity u t) = rootVelocity u :=
    funext fun _ => zero_add _
  rw [hv, hw] at h
  exact h

def rootDerivative {n : ℕ} (u : periodicSubmodule n) (t : ℝ) : ℝ →L[ℝ] Ambient n :=
  ContinuousLinearMap.toSpanSingleton ℝ (rootVelocity u t)

theorem root_realMap_hasWeakFDeriv {n : ℕ} (u : periodicSubmodule n) :
    TauCeti.HasWeakFDerivOn volume unitInterval
      (fun t => realMap u ((1 / 2 : ℝ) * t)) (rootDerivative u) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have h := (root_realMap_hasWeakLineDeriv u).smul_direction d
  change TauCeti.HasWeakLineDerivOn volume unitInterval
    (fun t => realMap u ((1 / 2 : ℝ) * t)) (fun t => d • rootVelocity u t) (d • (1 : ℝ)) at h
  simp only [smul_eq_mul, mul_one] at h
  exact h.congr_ae_deriv (Eventually.of_forall fun _ => rfl)

theorem rootValue_memLp {n : ℕ} (u : periodicSubmodule n) :
    MemLp (fun t => realMap u ((1 / 2 : ℝ) * t)) 2 intervalMeasure :=
  Finsler.SmoothSobolev.continuous_memLp_interval
    ((realMap u).continuous.comp (continuous_const.mul continuous_id))

def rootValueLp {n : ℕ} (u : periodicSubmodule n) : ValueLp n :=
  (rootValue_memLp u).toLp (fun t => realMap u ((1 / 2 : ℝ) * t))

theorem rootValueLp_ae {n : ℕ} (u : periodicSubmodule n) :
    rootValueLp u =ᵐ[intervalMeasure] fun t => realMap u ((1 / 2 : ℝ) * t) :=
  (rootValue_memLp u).coeFn_toLp

def rootVelocityLp {n : ℕ} (u : periodicSubmodule n) : ValueLp n :=
  (rootVelocity_memLp u).toLp (rootVelocity u)

theorem rootVelocityLp_ae {n : ℕ} (u : periodicSubmodule n) :
    rootVelocityLp u =ᵐ[intervalMeasure] rootVelocity u := (rootVelocity_memLp u).coeFn_toLp

def rootDerivativeLp {n : ℕ} (u : periodicSubmodule n) : DerivativeLp n :=
  (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 intervalMeasure (rootVelocityLp u)

theorem rootDerivativeLp_ae {n : ℕ} (u : periodicSubmodule n) :
    rootDerivativeLp u =ᵐ[intervalMeasure] rootDerivative u := by
  let L : Ambient n →L[ℝ] (ℝ →L[ℝ] Ambient n) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.coeFn_compLpL (p := 2) (μ := intervalMeasure) (rootVelocityLp u)
  filter_upwards [h, rootVelocityLp_ae u] with t hD hv
  change (L.compLpL 2 intervalMeasure (rootVelocityLp u)) t = _
  rw [hD, hv]
  rfl

theorem rootValue_hasWeakFDeriv {n : ℕ} (u : periodicSubmodule n) :
    TauCeti.HasWeakFDerivOn volume unitInterval (base n (rootValueLp u)) (rootDerivativeLp u) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have h := (TauCeti.hasWeakFDerivOn_iff.mp (root_realMap_hasWeakFDeriv u)) d
  have hval : (fun t => realMap u ((1 / 2 : ℝ) * t)) =ᵐ[intervalMeasure]
      (base n (rootValueLp u)) := (rootValueLp_ae u).symm
  have hD : (fun t => rootDerivative u t d) =ᵐ[intervalMeasure]
      fun t => rootDerivativeLp u t d := by
    filter_upwards [rootDerivativeLp_ae u] with t ht
    exact congrArg (fun D : ℝ →L[ℝ] Ambient n => D d) ht.symm
  exact (h.congr_ae hval).congr_ae_deriv hD

def rootData {n : ℕ} (u : periodicSubmodule n) : Space n :=
  TauCeti.WeakDerivStep.mk (base n) (rootValueLp u) (rootDerivativeLp u) (rootValue_hasWeakFDeriv u)

theorem value_rootData {n : ℕ} (u : periodicSubmodule n) : value (rootData u) = rootValueLp u := by
  change TauCeti.WeakDerivStep.prevL (base n) (rootData u) = _
  rw [TauCeti.WeakDerivStep.prevL_apply]
  exact TauCeti.WeakDerivStep.prev_mk _ _ _ _

theorem derivative_rootData {n : ℕ} (u : periodicSubmodule n) :
    derivative (rootData u) = rootDerivativeLp u := by
  change TauCeti.WeakDerivStep.weakFDerivL (base n) (rootData u) = _
  rw [TauCeti.WeakDerivStep.weakFDerivL_apply]
  exact TauCeti.WeakDerivStep.weakFDeriv_mk _ _ _ _

theorem velocity_rootData_ae {n : ℕ} (u : periodicSubmodule n) :
    velocity (rootData u) =ᵐ[intervalMeasure] rootVelocity u := by
  filter_upwards [velocity_apply_ae (rootData u), rootDerivativeLp_ae u] with t hv hD
  rw [derivative_rootData, hD] at hv
  change velocity (rootData u) t = (1 : ℝ) • rootVelocity u t at hv
  simpa only [one_smul] using hv

theorem representative_rootData {n : ℕ} (u : periodicSubmodule n) {t : ℝ} (ht : t ∈ Icc 0 1) :
    continuousRepresentative (rootData u) t = realMap u ((1 / 2 : ℝ) * t) := by
  apply continuous_representative_unique (continuousRepresentative_continuousOn _)
    ((realMap u).continuous.comp (continuous_const.mul continuous_id)).continuousOn
    (value_ae_continuousRepresentative _) _ ht
  rw [value_rootData]
  exact rootValueLp_ae u

theorem halfFixed_endpoint {n : ℕ} (u : HalfFixed n) :
    realMap u.val.data (1 / 2) = realMap u.val.data 0 := by
  have h := (fixed_phase_iff_circleMap u.val halfPhase).mp u.property 0
  have hv := congrArg (fun x : Sphere n => (x : Ambient n)) h
  simpa only [halfPhase, add_zero, realMap_apply, sphereCircleMap_val,
    AddCircle.coe_zero] using hv

def periodicRoot {n : ℕ} (u : HalfFixed n) : periodicSubmodule n :=
  ⟨rootData u.val.data, by
    rw [mem_periodicSubmodule_iff]
    change continuousRepresentative (rootData u.val.data) 1 = continuousRepresentative (rootData u.val.data) 0
    rw [representative_rootData u.val.data (by norm_num), representative_rootData u.val.data (by norm_num)]
    simpa only [mul_one, mul_zero] using halfFixed_endpoint u⟩

def rootSphere {n : ℕ} (u : HalfFixed n) : SphereLoop n where
  data := periodicRoot u
  sphere_constraint t := by
    change ‖continuousRepresentative (rootData u.val.data) t‖ = 1
    rw [representative_rootData u.val.data t.property, realMap_apply]
    exact circleMap_sphere_norm u.val ((1 / 2 : ℝ) * (t : ℝ))

theorem rootSphere_data {n : ℕ} (u : HalfFixed n) :
    ((rootSphere u).data : Space n) = rootData u.val.data := rfl

theorem representative_rootSphere {n : ℕ} (u : HalfFixed n) (t : ClosedInterval) :
    (sphereRepresentative (rootSphere u) t : Ambient n) =
      realMap u.val.data ((1 / 2 : ℝ) * (t : ℝ)) := representative_rootData _ t.property

end

end Finsler.SobolevHalfRoot
