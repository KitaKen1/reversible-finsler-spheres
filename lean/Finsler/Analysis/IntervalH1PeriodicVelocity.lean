module

public import Finsler.Analysis.IntervalH1CircleRepresentative
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Periodizing the actual weak velocity, not supplying a separate derivative.
Its zero mean gives a periodic primitive. This primitive recovers the genuine
continuous circle representative at every real time. Real shifts consequently
have certified weak Fréchet derivative and actual L² velocity on the interval.
The shifted graph is constructed in IntervalH1Shift. Strong-H¹ joint continuity
remains a separate open obligation. 
Strong-H¹ rotation continuity and isometry are proved downstream in
IntervalH1RotationContinuity and IntervalH1RotationIsometry. -/

@[expose] public section

namespace Finsler.SobolevPeriodicVelocity

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.IntervalPrimitive
open Finsler.SobolevCircleRepresentative MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

def periodicVelocity {n : ℕ} (u : periodicSubmodule n) (t : ℝ) : Ambient n :=
  AddCircle.liftIoc (1 : ℝ) 0 (velocity (u : Space n)) (t : SobolevCircleRepresentative.Circle)

theorem periodicVelocity_eqOn_Ioc {n : ℕ} (u : periodicSubmodule n) :
    EqOn (periodicVelocity u) (velocity (u : Space n)) (Ioc 0 1) := by
  intro t ht
  exact AddCircle.liftIoc_zero_coe_apply ht

theorem periodicVelocity_ae {n : ℕ} (u : periodicSubmodule n) :
    periodicVelocity u =ᵐ[intervalMeasure] velocity (u : Space n) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact periodicVelocity_eqOn_Ioc u (Ioo_subset_Ioc_self ht)

theorem periodicVelocity_memLp {n : ℕ} (u : periodicSubmodule n) :
    MemLp (periodicVelocity u) 2 intervalMeasure :=
  (Lp.memLp (velocity (u : Space n))).ae_eq (periodicVelocity_ae u).symm

theorem periodicVelocity_periodic {n : ℕ} (u : periodicSubmodule n) :
    Function.Periodic (periodicVelocity u) 1 := by
  intro t
  change AddCircle.liftIoc (1 : ℝ) 0 (velocity (u : Space n))
    ((t + 1 : ℝ) : SobolevCircleRepresentative.Circle) =
    AddCircle.liftIoc (1 : ℝ) 0 (velocity (u : Space n)) (t : SobolevCircleRepresentative.Circle)
  rw [AddCircle.coe_add_period]

theorem periodicVelocity_integral {n : ℕ} (u : periodicSubmodule n) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    (∫ x in (0 : ℝ)..t, periodicVelocity u x) = ∫ x in (0 : ℝ)..t, velocity (u : Space n) x := by
  apply intervalIntegral.integral_congr_Ioo_of_le ht.1
  intro x hx
  exact periodicVelocity_eqOn_Ioc u ⟨hx.1, (lt_of_lt_of_le hx.2 ht.2).le⟩

theorem periodicVelocity_intervalIntegrable_zero_one {n : ℕ} (u : periodicSubmodule n) :
    IntervalIntegrable (periodicVelocity u) volume 0 1 := by
  apply (intervalIntegrable_congr_uIoo (f := periodicVelocity u)
    (g := velocity (u : Space n)) ?_).mpr (velocity_intervalIntegrable (u : Space n))
  intro t ht
  rw [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
  exact periodicVelocity_eqOn_Ioc u (Ioo_subset_Ioc_self ht)

theorem periodicVelocity_intervalIntegrable {n : ℕ} (u : periodicSubmodule n) (a b : ℝ) :
    IntervalIntegrable (periodicVelocity u) volume a b :=
  (periodicVelocity_periodic u).intervalIntegrable₀ (by norm_num)
    (periodicVelocity_intervalIntegrable_zero_one u) a b

theorem periodicVelocity_mean_zero {n : ℕ} (u : periodicSubmodule n) :
    (∫ x in (0 : ℝ)..1, periodicVelocity u x) = 0 := by
  rw [periodicVelocity_integral u (by norm_num)]
  exact (mem_periodicSubmodule_iff_integral_zero (u : Space n)).mp u.property

theorem periodicVelocity_primitive_periodic {n : ℕ} (u : periodicSubmodule n) :
    Function.Periodic (primitive (periodicVelocity u)) 1 := by
  intro t
  have h := (periodicVelocity_periodic u).intervalIntegral_add_eq_add 0 t
    (periodicVelocity_intervalIntegrable u)
  change (∫ x in (0 : ℝ)..t + 1, periodicVelocity u x) =
    ∫ x in (0 : ℝ)..t, periodicVelocity u x
  simpa only [zero_add, periodicVelocity_mean_zero u, add_zero] using h

theorem realMap_eq_primitive {n : ℕ} (u : periodicSubmodule n) (t : ℝ) :
    realMap u t = continuousRepresentative (u : Space n) 0 + primitive (periodicVelocity u) t := by
  let r : ClosedInterval := ⟨Int.fract t, Int.fract_nonneg t, (Int.fract_lt_one t).le⟩
  have hq : realMap u (Int.fract t) = realMap u t := by
    simpa only [Int.fract, mul_one] using (realMap_periodic u).sub_int_mul_eq (x := t) ⌊t⌋
  have hp : primitive (periodicVelocity u) (Int.fract t) = primitive (periodicVelocity u) t := by
    simpa only [Int.fract, mul_one] using
      (periodicVelocity_primitive_periodic u).sub_int_mul_eq (x := t) ⌊t⌋
  rw [← hq, ← hp, realMap_eqOn u r.property]
  have hinc := continuousRepresentative_sub (u : Space n) (s := 0) (t := Int.fract t)
    (by norm_num) r.property
  have hi := periodicVelocity_integral u r.property
  change (∫ x in (0 : ℝ)..Int.fract t, periodicVelocity u x) = _ at hi
  change continuousRepresentative (u : Space n) (Int.fract t) =
    continuousRepresentative (u : Space n) 0 + ∫ x in (0 : ℝ)..Int.fract t, periodicVelocity u x
  rw [hi]
  exact (sub_eq_iff_eq_add.mp hinc).trans (add_comm _ _)

theorem realMap_sub {n : ℕ} (u : periodicSubmodule n) (s t : ℝ) :
    realMap u t - realMap u s = ∫ x in s..t, periodicVelocity u x := by
  rw [realMap_eq_primitive, realMap_eq_primitive, add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left
    (periodicVelocity_intervalIntegrable u 0 t) (periodicVelocity_intervalIntegrable u 0 s)

def shiftVelocity {n : ℕ} (u : periodicSubmodule n) (a t : ℝ) : Ambient n :=
  periodicVelocity u (t + a)

theorem shiftVelocity_intervalIntegrable {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    IntervalIntegrable (shiftVelocity u a) volume 0 1 := by
  change IntervalIntegrable (fun x => periodicVelocity u (x + a)) volume 0 1
  simpa only [sub_self, add_sub_cancel_right] using
    (periodicVelocity_intervalIntegrable u a (1 + a)).comp_add_right a

theorem shift_primitive_identity {n : ℕ} (u : periodicSubmodule n) (a t : ℝ) :
    realMap u (t + a) = realMap u a + primitive (shiftVelocity u a) t := by
  have hi : primitive (shiftVelocity u a) t = ∫ x in a..t + a, periodicVelocity u x := by
    change (∫ x in (0 : ℝ)..t, periodicVelocity u (x + a)) = _
    rw [intervalIntegral.integral_comp_add_right]
    simp only [zero_add]
  rw [hi]
  exact (sub_eq_iff_eq_add.mp (realMap_sub u a (t + a))).trans (add_comm _ _)

theorem shifted_realMap_hasWeakLineDeriv {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    TauCeti.HasWeakLineDerivOn volume unitInterval (fun t => realMap u (t + a))
      (shiftVelocity u a) 1 := by
  have hp := primitive_hasWeakLineDeriv (shiftVelocity_intervalIntegrable u a)
  have hc : TauCeti.HasWeakLineDerivOn volume unitInterval (fun _ : ℝ => realMap u a)
      (fun _ => (0 : Ambient n)) 1 := TauCeti.hasWeakLineDerivOn_const _
  have h := hc.add hp
  change TauCeti.HasWeakLineDerivOn volume unitInterval
    (fun t => realMap u a + primitive (shiftVelocity u a) t)
    (fun t => 0 + shiftVelocity u a t) 1 at h
  have hval : (fun t => realMap u a + primitive (shiftVelocity u a) t) =
      (fun t => realMap u (t + a)) := by
    funext t
    exact (shift_primitive_identity u a t).symm
  have hvel : (fun t => (0 : Ambient n) + shiftVelocity u a t) = shiftVelocity u a := by
    funext t
    exact zero_add _
  rw [hval, hvel] at h
  exact h

theorem periodicVelocity_sq_periodic {n : ℕ} (u : periodicSubmodule n) :
    Function.Periodic (fun t => ‖periodicVelocity u t‖ ^ 2) 1 := by
  intro t
  change ‖periodicVelocity u (t + 1)‖ ^ 2 = ‖periodicVelocity u t‖ ^ 2
  rw [periodicVelocity_periodic u t]

theorem periodicVelocity_sq_intervalIntegrable {n : ℕ} (u : periodicSubmodule n) (a b : ℝ) :
    IntervalIntegrable (fun t => ‖periodicVelocity u t‖ ^ 2) volume a b := by
  have h : IntervalIntegrable (fun t => ‖periodicVelocity u t‖ ^ 2) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    exact (memLp_two_iff_integrable_sq_norm (periodicVelocity_memLp u).aestronglyMeasurable).mp
      (periodicVelocity_memLp u)
  exact (periodicVelocity_sq_periodic u).intervalIntegrable₀ (by norm_num) h a b

theorem shiftVelocity_sq_intervalIntegrable {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    IntervalIntegrable (fun t => ‖shiftVelocity u a t‖ ^ 2) volume 0 1 := by
  change IntervalIntegrable (fun t => ‖periodicVelocity u (t + a)‖ ^ 2) volume 0 1
  simpa only [sub_self, add_sub_cancel_right] using
    (periodicVelocity_sq_intervalIntegrable u a (1 + a)).comp_add_right a

theorem shiftVelocity_memLp {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    MemLp (shiftVelocity u a) 2 intervalMeasure := by
  have h : Integrable (shiftVelocity u a) intervalMeasure :=
    (shiftVelocity_intervalIntegrable u a).1.mono_set Ioo_subset_Ioc_self
  apply (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mpr
  exact (shiftVelocity_sq_intervalIntegrable u a).1.mono_set Ioo_subset_Ioc_self

def shiftDerivative {n : ℕ} (u : periodicSubmodule n) (a t : ℝ) : ℝ →L[ℝ] Ambient n :=
  ContinuousLinearMap.toSpanSingleton ℝ (shiftVelocity u a t)

theorem shiftDerivative_apply {n : ℕ} (u : periodicSubmodule n) (a t d : ℝ) :
    shiftDerivative u a t d = d • shiftVelocity u a t := rfl

theorem shifted_realMap_hasWeakFDeriv {n : ℕ} (u : periodicSubmodule n) (a : ℝ) :
    TauCeti.HasWeakFDerivOn volume unitInterval (fun t => realMap u (t + a))
      (shiftDerivative u a) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have h := (shifted_realMap_hasWeakLineDeriv u a).smul_direction d
  change TauCeti.HasWeakLineDerivOn volume unitInterval (fun t => realMap u (t + a))
    (fun t => d • shiftVelocity u a t) (d • (1 : ℝ)) at h
  simp only [smul_eq_mul, mul_one] at h
  exact h.congr_ae_deriv (Eventually.of_forall fun t => (shiftDerivative_apply u a t d).symm)

end

end Finsler.SobolevPeriodicVelocity
