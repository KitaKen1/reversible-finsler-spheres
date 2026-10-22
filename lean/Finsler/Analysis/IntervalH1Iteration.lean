module

public import Finsler.Analysis.IntervalCircleLpIteration

/-! Positive integer iteration of the actual periodic weak H¹ sphere graph.
The actual rescaled weak velocity is certified through its primitive, then
assembled in TauCeti's genuine weak derivative graph. -/

@[expose] public section

namespace Finsler.SobolevIteration

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCircleRepresentative Finsler.SobolevPeriodicVelocity
open Finsler.IntervalPrimitive Finsler.CircleLpTransfer
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def iterateVelocity {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (t : ℝ) : Ambient n :=
  (k : ℝ) • periodicVelocity u ((k : ℝ) * t)

theorem iterateVelocity_intervalIntegrable {n : ℕ} (u : periodicSubmodule n)
    (k : ℕ) (hk : k ≠ 0) : IntervalIntegrable (iterateVelocity u k) volume 0 1 := by
  have h := (periodicVelocity_intervalIntegrable u 0 (k : ℝ)).comp_mul_left (c := (k : ℝ))
  have hc : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have h' : IntervalIntegrable (fun t => periodicVelocity u ((k : ℝ) * t)) volume 0 1 := by
    simpa only [zero_div, div_self hc] using h
  exact h'.smul (k : ℝ)

theorem iterate_primitive_identity {n : ℕ} (u : periodicSubmodule n)
    (k : ℕ) (t : ℝ) :
    realMap u ((k : ℝ) * t) = continuousRepresentative (u : Space n) 0 +
      primitive (iterateVelocity u k) t := by
  have hi : primitive (iterateVelocity u k) t = primitive (periodicVelocity u) ((k : ℝ) * t) := by
    change (∫ s in (0 : ℝ)..t, (k : ℝ) • periodicVelocity u ((k : ℝ) * s)) =
      ∫ s in (0 : ℝ)..(k : ℝ) * t, periodicVelocity u s
    rw [intervalIntegral.integral_smul, intervalIntegral.smul_integral_comp_mul_left]
    simp only [mul_zero]
  rw [hi]
  exact realMap_eq_primitive u _

theorem iterated_realMap_hasWeakLineDeriv {n : ℕ} (u : periodicSubmodule n)
    (k : ℕ) (hk : k ≠ 0) :
    TauCeti.HasWeakLineDerivOn volume unitInterval (fun t => realMap u ((k : ℝ) * t))
      (iterateVelocity u k) 1 := by
  have hp := primitive_hasWeakLineDeriv (iterateVelocity_intervalIntegrable u k hk)
  have hc : TauCeti.HasWeakLineDerivOn volume unitInterval
      (fun _ : ℝ => continuousRepresentative (u : Space n) 0)
      (fun _ => (0 : Ambient n)) 1 := TauCeti.hasWeakLineDerivOn_const _
  have h := hc.add hp
  change TauCeti.HasWeakLineDerivOn volume unitInterval
    (fun t => continuousRepresentative (u : Space n) 0 + primitive (iterateVelocity u k) t)
    (fun t => 0 + iterateVelocity u k t) 1 at h
  have hv : (fun t => continuousRepresentative (u : Space n) 0 + primitive (iterateVelocity u k) t) =
      (fun t => realMap u ((k : ℝ) * t)) := funext fun t => (iterate_primitive_identity u k t).symm
  have hw : (fun t => (0 : Ambient n) + iterateVelocity u k t) = iterateVelocity u k :=
    funext fun _ => zero_add _
  rw [hv, hw] at h
  exact h

def iterateDerivative {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (t : ℝ) : ℝ →L[ℝ] Ambient n :=
  ContinuousLinearMap.toSpanSingleton ℝ (iterateVelocity u k t)

theorem iterateDerivative_apply {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (t d : ℝ) :
    iterateDerivative u k t d = d • iterateVelocity u k t := rfl

theorem iterated_realMap_hasWeakFDeriv {n : ℕ} (u : periodicSubmodule n)
    (k : ℕ) (hk : k ≠ 0) :
    TauCeti.HasWeakFDerivOn volume unitInterval (fun t => realMap u ((k : ℝ) * t))
      (iterateDerivative u k) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have h := (iterated_realMap_hasWeakLineDeriv u k hk).smul_direction d
  change TauCeti.HasWeakLineDerivOn volume unitInterval (fun t => realMap u ((k : ℝ) * t))
    (fun t => d • iterateVelocity u k t) (d • (1 : ℝ)) at h
  simp only [smul_eq_mul, mul_one] at h
  exact h.congr_ae_deriv (Eventually.of_forall fun t => (iterateDerivative_apply u k t d).symm)

def iterateValueLp {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) : ValueLp n :=
  iterateLpL (Ambient n) k hk (value (u : Space n))

theorem iterateValueLp_ae {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    iterateValueLp u k hk =ᵐ[intervalMeasure] fun t => realMap u ((k : ℝ) * t) :=
  iterateLpL_value_ae u k hk

def iterateVelocityLp {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) : ValueLp n :=
  (k : ℝ) • iterateLpL (Ambient n) k hk (velocity (u : Space n))

theorem iterateVelocityLp_ae {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    iterateVelocityLp u k hk =ᵐ[intervalMeasure] iterateVelocity u k := by
  filter_upwards [Lp.coeFn_smul (k : ℝ) (iterateLpL (Ambient n) k hk (velocity (u : Space n))),
    iterateLpL_velocity_ae u k hk] with t h₁ h₂
  exact h₁.trans (congrArg (fun v : Ambient n => (k : ℝ) • v) h₂)

def iterateDerivativeLp {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) : DerivativeLp n :=
  (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 intervalMeasure (iterateVelocityLp u k hk)

theorem iterateDerivativeLp_ae {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    iterateDerivativeLp u k hk =ᵐ[intervalMeasure] iterateDerivative u k := by
  let L : Ambient n →L[ℝ] (ℝ →L[ℝ] Ambient n) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.coeFn_compLpL (p := 2) (μ := intervalMeasure) (iterateVelocityLp u k hk)
  filter_upwards [h, iterateVelocityLp_ae u k hk] with t hD hv
  change (L.compLpL 2 intervalMeasure (iterateVelocityLp u k hk)) t = _
  rw [hD, hv]
  rfl

theorem iterateValue_hasWeakFDeriv {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    TauCeti.HasWeakFDerivOn volume unitInterval (base n (iterateValueLp u k hk))
      (iterateDerivativeLp u k hk) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have h := (TauCeti.hasWeakFDerivOn_iff.mp (iterated_realMap_hasWeakFDeriv u k hk)) d
  have hval : (fun t => realMap u ((k : ℝ) * t)) =ᵐ[intervalMeasure]
      (base n (iterateValueLp u k hk)) := (iterateValueLp_ae u k hk).symm
  have hD : (fun t => iterateDerivative u k t d) =ᵐ[intervalMeasure]
      fun t => iterateDerivativeLp u k hk t d := by
    filter_upwards [iterateDerivativeLp_ae u k hk] with t ht
    exact congrArg (fun D : ℝ →L[ℝ] Ambient n => D d) ht.symm
  exact (h.congr_ae hval).congr_ae_deriv hD

def iterateData {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) : Space n :=
  TauCeti.WeakDerivStep.mk (base n) (iterateValueLp u k hk) (iterateDerivativeLp u k hk)
    (iterateValue_hasWeakFDeriv u k hk)

theorem value_iterateData {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    value (iterateData u k hk) = iterateValueLp u k hk := by
  change TauCeti.WeakDerivStep.prevL (base n) (iterateData u k hk) = _
  rw [TauCeti.WeakDerivStep.prevL_apply]
  exact TauCeti.WeakDerivStep.prev_mk _ _ _ _

theorem derivative_iterateData {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    derivative (iterateData u k hk) = iterateDerivativeLp u k hk := by
  change TauCeti.WeakDerivStep.weakFDerivL (base n) (iterateData u k hk) = _
  rw [TauCeti.WeakDerivStep.weakFDerivL_apply]
  exact TauCeti.WeakDerivStep.weakFDeriv_mk _ _ _ _

theorem velocity_iterateData_ae {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    velocity (iterateData u k hk) =ᵐ[intervalMeasure] iterateVelocity u k := by
  filter_upwards [velocity_apply_ae (iterateData u k hk), iterateDerivativeLp_ae u k hk] with t hv hD
  rw [derivative_iterateData, hD, iterateDerivative_apply] at hv
  simpa only [one_smul] using hv

theorem velocity_iterateData {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    velocity (iterateData u k hk) = iterateVelocityLp u k hk :=
  Lp.ext ((velocity_iterateData_ae u k hk).trans (iterateVelocityLp_ae u k hk).symm)

theorem representative_iterateData {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    continuousRepresentative (iterateData u k hk) t = realMap u ((k : ℝ) * t) := by
  apply continuous_representative_unique (continuousRepresentative_continuousOn _)
    ((realMap u).continuous.comp (continuous_const.mul continuous_id)).continuousOn
    (value_ae_continuousRepresentative _) _ ht
  rw [value_iterateData]
  exact iterateValueLp_ae u k hk

def periodicIterate {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) : periodicSubmodule n :=
  ⟨iterateData u k hk, by
    rw [mem_periodicSubmodule_iff]
    change continuousRepresentative (iterateData u k hk) 1 =
      continuousRepresentative (iterateData u k hk) 0
    rw [representative_iterateData u k hk (by norm_num), representative_iterateData u k hk (by norm_num)]
    simpa only [mul_one, mul_zero, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, zero_add] using
      (realMap_periodic u).nat_mul_eq k⟩

theorem periodicIterate_val {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    (periodicIterate u k hk : Space n) = iterateData u k hk := rfl

def iterateSphere {n : ℕ} (u : SphereLoop n) (k : ℕ) (hk : k ≠ 0) : SphereLoop n where
  data := periodicIterate u.data k hk
  sphere_constraint t := by
    change ‖continuousRepresentative (iterateData u.data k hk) t‖ = 1
    rw [representative_iterateData u.data k hk t.property, realMap_apply]
    exact circleMap_sphere_norm u ((k : ℝ) * (t : ℝ))

theorem iterateSphere_data {n : ℕ} (u : SphereLoop n) (k : ℕ) (hk : k ≠ 0) :
    (iterateSphere u k hk).data = periodicIterate u.data k hk := rfl

theorem circleMap_iterateSphere {n : ℕ} (u : SphereLoop n) (k : ℕ) (hk : k ≠ 0) (x : Phase) :
    sphereCircleMap (iterateSphere u k hk) x = sphereCircleMap u (degreeCover k x) := by
  rw [← circlePoint_coe x, sphereCircleMap_coe]
  apply Subtype.ext
  change continuousRepresentative (iterateData u.data k hk) (circlePoint x) = _
  rw [representative_iterateData u.data k hk (circlePoint x).property, realMap_apply]
  rw [← degreeCover_coe, circlePoint_coe]
  rfl

theorem iterateSphere_one {n : ℕ} (u : SphereLoop n) : iterateSphere u 1 (by norm_num) = u := by
  apply sphereCircleMap_injective
  apply ContinuousMap.ext
  intro x
  rw [circleMap_iterateSphere, degreeCover_apply, one_nsmul]

end

end Finsler.SobolevIteration
