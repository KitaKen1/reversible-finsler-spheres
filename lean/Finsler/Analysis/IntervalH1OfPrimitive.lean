module

public import Finsler.Analysis.IntervalH1Trace

/-! Generic constructor of the original weak H¹ graph from a primitive. A function
continuous on [0,1] that equals its value at 0 plus the primitive of an L² velocity is a
graph element whose value and velocity are these functions almost everywhere and whose
continuous representative is the function itself on [0,1]. -/

@[expose] public section

namespace Finsler.SobolevOfPrimitive

open Finsler.SphereGeometry Finsler.IntervalSobolev
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

set_option maxHeartbeats 400000

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

theorem memLp_of_continuousOn {f : ℝ → Ambient n} (hf : ContinuousOn f (Icc 0 1)) :
    MemLp f 2 intervalMeasure := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine MemLp.of_bound ((hf.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo)
    C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hC t (Ioo_subset_Icc_self ht)

theorem intervalIntegrable_of_memLp {v : ℝ → Ambient n} (hv : MemLp v 2 intervalMeasure) :
    IntervalIntegrable v volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact hv.integrable (by norm_num)

theorem hasWeakLineDeriv_of_primitive {q v : ℝ → Ambient n} (hv : MemLp v 2 intervalMeasure)
    (hprim : ∀ t ∈ Icc (0 : ℝ) 1, q t = q 0 + ∫ s in (0 : ℝ)..t, v s) :
    TauCeti.HasWeakLineDerivOn volume unitInterval q v 1 := by
  have hP := Finsler.IntervalPrimitive.primitive_hasWeakLineDeriv (intervalIntegrable_of_memLp hv)
  have hc := TauCeti.hasWeakLineDerivOn_const (μ := volume)
    (Ω := Finsler.IntervalSobolev.unitInterval) (v := (1 : ℝ)) (q 0)
  have hs := hc.add hP
  have hval : (fun _ => q 0) + Finsler.IntervalPrimitive.primitive v
      =ᵐ[volume.restrict (Finsler.IntervalSobolev.unitInterval : Set ℝ)] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hprim t (Ioo_subset_Icc_self ht)).symm
  have hd : (fun _ : ℝ => (0 : Ambient n)) + v
      =ᵐ[volume.restrict (Finsler.IntervalSobolev.unitInterval : Set ℝ)] v :=
    Eventually.of_forall fun t => zero_add _
  exact (hs.congr_ae hval).congr_ae_deriv hd

section Construction

variable {q v : ℝ → Ambient n} (hq : ContinuousOn q (Icc 0 1))
  (hv : MemLp v 2 intervalMeasure)

def valueLp : ValueLp n := (memLp_of_continuousOn hq).toLp q

def velocityLp : ValueLp n := hv.toLp v

def derivativeLp : DerivativeLp n :=
  (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 intervalMeasure (velocityLp hv)

theorem valueLp_ae : valueLp hq =ᵐ[intervalMeasure] q := (memLp_of_continuousOn hq).coeFn_toLp

theorem velocityLp_ae : velocityLp hv =ᵐ[intervalMeasure] v := hv.coeFn_toLp

theorem derivativeLp_apply_ae (d : ℝ) :
    (fun t => derivativeLp hv t d) =ᵐ[intervalMeasure] fun t => d • v t := by
  let L : Ambient n →L[ℝ] (ℝ →L[ℝ] Ambient n) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap
  have hL := L.coeFn_compLpL (p := 2) (μ := intervalMeasure) (velocityLp hv)
  filter_upwards [hL, velocityLp_ae hv] with t hD hvt
  change (L.compLpL 2 intervalMeasure (velocityLp hv)) t d = _
  rw [hD, hvt]
  rfl

variable (hprim : ∀ t ∈ Icc (0 : ℝ) 1, q t = q 0 + ∫ s in (0 : ℝ)..t, v s)

include hprim in
theorem value_hasWeakFDeriv :
    TauCeti.HasWeakFDerivOn volume unitInterval (base n (valueLp hq)) (derivativeLp hv) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have hs := (hasWeakLineDeriv_of_primitive hv hprim).smul_direction d
  change TauCeti.HasWeakLineDerivOn volume unitInterval q (fun t => d • v t) (d • (1 : ℝ)) at hs
  have hs' : TauCeti.HasWeakLineDerivOn volume unitInterval q (fun t => d • v t) d := by
    simpa only [smul_eq_mul, mul_one] using hs
  exact (hs'.congr_ae (valueLp_ae hq).symm).congr_ae_deriv (derivativeLp_apply_ae hv d).symm

/-- The graph element with continuous value q and weak velocity v. -/
def ofPrimitive : Space n :=
  TauCeti.WeakDerivStep.mk (base n) (valueLp hq) (derivativeLp hv) (value_hasWeakFDeriv hq hv hprim)

theorem value_ofPrimitive : value (ofPrimitive hq hv hprim) = valueLp hq := by
  change TauCeti.WeakDerivStep.prevL (base n) (ofPrimitive hq hv hprim) = _
  rw [TauCeti.WeakDerivStep.prevL_apply]
  exact TauCeti.WeakDerivStep.prev_mk _ _ _ _

theorem derivative_ofPrimitive : derivative (ofPrimitive hq hv hprim) = derivativeLp hv := by
  change TauCeti.WeakDerivStep.weakFDerivL (base n) (ofPrimitive hq hv hprim) = _
  rw [TauCeti.WeakDerivStep.weakFDerivL_apply]
  exact TauCeti.WeakDerivStep.weakFDeriv_mk _ _ _ _

theorem value_ofPrimitive_ae : value (ofPrimitive hq hv hprim) =ᵐ[intervalMeasure] q := by
  rw [value_ofPrimitive]
  exact valueLp_ae hq

theorem velocity_ofPrimitive_ae : velocity (ofPrimitive hq hv hprim) =ᵐ[intervalMeasure] v := by
  have hD := derivativeLp_apply_ae hv 1
  rw [← derivative_ofPrimitive hq hv hprim] at hD
  filter_upwards [velocity_apply_ae (ofPrimitive hq hv hprim), hD] with t h1 h2
  rw [h1, h2, one_smul]

theorem representative_ofPrimitive {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (ofPrimitive hq hv hprim) t = q t :=
  continuous_representative_unique (continuousRepresentative_continuousOn _) hq
    (value_ae_continuousRepresentative _) (value_ofPrimitive_ae hq hv hprim) ht

theorem ofPrimitive_periodic (hper : q 1 = q 0) : ofPrimitive hq hv hprim ∈ periodicSubmodule n := by
  rw [mem_periodicSubmodule_iff]
  change continuousRepresentative _ 1 = continuousRepresentative _ 0
  rw [representative_ofPrimitive hq hv hprim (by norm_num),
    representative_ofPrimitive hq hv hprim (by norm_num), hper]

end Construction

end

end Finsler.SobolevOfPrimitive
