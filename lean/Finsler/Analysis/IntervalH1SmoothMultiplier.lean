module

public import Finsler.Analysis.IntervalH1Trace
public import TauCeti.Analysis.Sobolev.Leibniz
public import Mathlib.Analysis.Normed.Group.Bounded

/-! Smooth scalar factors and fixed ambient linear maps on the original H¹ graph.
The velocity is certified by the distributional product rule and then packaged
in the same weak-derivative graph. Continuous representatives and periodic
traces are compared explicitly. This does not assert general H¹ multiplication
or nonlinear normalization. -/

@[expose] public section

namespace Finsler.SobolevSmoothMultiplier

open Finsler.SphereGeometry Finsler.IntervalSobolev
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem continuous_smul_memLp {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {p : ℝ≥0∞} {f : ℝ → H} {ψ : ℝ → ℝ}
    (hf : MemLp f p intervalMeasure) (hψ : Continuous ψ) :
    MemLp (fun t => ψ t • f t) p intervalMeasure := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hψ.continuousOn : ContinuousOn ψ (Icc (0 : ℝ) 1))
  apply hf.of_le_mul (c := C) (hψ.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  change ‖ψ t • f t‖ ≤ C * ‖f t‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC t (Ioo_subset_Icc_self ht)) (norm_nonneg _)

def fieldValueFun (ψ : ℝ → ℝ) (A : Ambient n →L[ℝ] Ambient n) (u : Space n)
    (t : ℝ) : Ambient n := ψ t • A (value u t)

def fieldVelocityFun (ψ : ℝ → ℝ) (A : Ambient n →L[ℝ] Ambient n) (u : Space n)
    (t : ℝ) : Ambient n :=
  ψ t • A (velocity u t) + fderiv ℝ ψ t 1 • A (value u t)

theorem fieldValue_memLp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    MemLp (fieldValueFun ψ A u) 2 intervalMeasure :=
  continuous_smul_memLp (A.comp_memLp (value u)) hψ.continuous

theorem fieldVelocity_memLp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    MemLp (fieldVelocityFun ψ A u) 2 intervalMeasure :=
  (continuous_smul_memLp (A.comp_memLp (velocity u)) hψ.continuous).add
    (continuous_smul_memLp (A.comp_memLp (value u))
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const))

theorem fieldValue_hasWeakLineVelocity {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    TauCeti.HasWeakLineDerivOn volume unitInterval
      (fieldValueFun ψ A u) (fieldVelocityFun ψ A u) 1 :=
  ((value_hasWeakLineVelocity u).clm_comp A).contDiff_smul hψ

def fieldValueLp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) : ValueLp n :=
  (fieldValue_memLp hψ A u).toLp (fieldValueFun ψ A u)

def fieldVelocityLp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) : ValueLp n :=
  (fieldVelocity_memLp hψ A u).toLp (fieldVelocityFun ψ A u)

theorem fieldValueLp_ae {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    fieldValueLp hψ A u =ᵐ[intervalMeasure] fieldValueFun ψ A u :=
  (fieldValue_memLp hψ A u).coeFn_toLp

theorem fieldVelocityLp_ae {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    fieldVelocityLp hψ A u =ᵐ[intervalMeasure] fieldVelocityFun ψ A u :=
  (fieldVelocity_memLp hψ A u).coeFn_toLp

def fieldDerivativeLp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) : DerivativeLp n :=
  (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap.compLpL
    2 intervalMeasure (fieldVelocityLp hψ A u)

theorem fieldDerivativeLp_apply_ae {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) (d : ℝ) :
    (fun t => fieldDerivativeLp hψ A u t d) =ᵐ[intervalMeasure]
      fun t => d • fieldVelocityFun ψ A u t := by
  let L : Ambient n →L[ℝ] (ℝ →L[ℝ] Ambient n) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ (Ambient n)).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.coeFn_compLpL (p := 2) (μ := intervalMeasure) (fieldVelocityLp hψ A u)
  filter_upwards [h, fieldVelocityLp_ae hψ A u] with t hD hv
  change (L.compLpL 2 intervalMeasure (fieldVelocityLp hψ A u)) t d = _
  rw [hD, hv]
  rfl

theorem fieldValue_hasWeakFDeriv {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    TauCeti.HasWeakFDerivOn volume unitInterval (base n (fieldValueLp hψ A u))
      (fieldDerivativeLp hψ A u) := by
  apply TauCeti.hasWeakFDerivOn_iff.mpr
  intro d
  have hs := (fieldValue_hasWeakLineVelocity hψ A u).smul_direction d
  change TauCeti.HasWeakLineDerivOn volume unitInterval (fieldValueFun ψ A u)
    (fun t => d • fieldVelocityFun ψ A u t) (d • (1 : ℝ)) at hs
  have hs' : TauCeti.HasWeakLineDerivOn volume unitInterval (fieldValueFun ψ A u)
      (fun t => d • fieldVelocityFun ψ A u t) d := by
    simpa only [smul_eq_mul, mul_one] using hs
  exact (hs'.congr_ae (fieldValueLp_ae hψ A u).symm).congr_ae_deriv
    (fieldDerivativeLp_apply_ae hψ A u d).symm

def fieldData {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) : Space n :=
  TauCeti.WeakDerivStep.mk (base n) (fieldValueLp hψ A u) (fieldDerivativeLp hψ A u)
    (fieldValue_hasWeakFDeriv hψ A u)

theorem value_fieldData {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    value (fieldData hψ A u) = fieldValueLp hψ A u := by
  change TauCeti.WeakDerivStep.prevL (base n) (fieldData hψ A u) = _
  rw [TauCeti.WeakDerivStep.prevL_apply]
  exact TauCeti.WeakDerivStep.prev_mk _ _ _ _

theorem derivative_fieldData {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    derivative (fieldData hψ A u) = fieldDerivativeLp hψ A u := by
  change TauCeti.WeakDerivStep.weakFDerivL (base n) (fieldData hψ A u) = _
  rw [TauCeti.WeakDerivStep.weakFDerivL_apply]
  exact TauCeti.WeakDerivStep.weakFDeriv_mk _ _ _ _

theorem value_fieldData_ae {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    value (fieldData hψ A u) =ᵐ[intervalMeasure]
      fun t => ψ t • A (continuousRepresentative u t) := by
  rw [value_fieldData]
  filter_upwards [fieldValueLp_ae hψ A u, value_ae_continuousRepresentative u] with t h hv
  exact h.trans (by rw [fieldValueFun, hv])

theorem velocity_fieldData_ae {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) :
    velocity (fieldData hψ A u) =ᵐ[intervalMeasure]
      fun t => ψ t • A (velocity u t) + fderiv ℝ ψ t 1 • A (continuousRepresentative u t) := by
  have hD := fieldDerivativeLp_apply_ae hψ A u 1
  rw [← derivative_fieldData] at hD
  filter_upwards [velocity_apply_ae (fieldData hψ A u), hD,
    value_ae_continuousRepresentative u] with t hv h ht
  rw [hv, h, one_smul, fieldVelocityFun, ht]

theorem representative_fieldData {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : Space n) {t : ℝ} (ht : t ∈ Icc 0 1) :
    continuousRepresentative (fieldData hψ A u) t = ψ t • A (continuousRepresentative u t) := by
  exact continuous_representative_unique (continuousRepresentative_continuousOn _)
    (hψ.continuous.continuousOn.smul
      (A.continuous.comp_continuousOn (continuousRepresentative_continuousOn u)))
    (value_ae_continuousRepresentative _) (value_fieldData_ae hψ A u) ht

theorem fieldData_periodic {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (A : Ambient n →L[ℝ] Ambient n) (u : periodicSubmodule n) (hp : ψ 1 = ψ 0) :
    fieldData hψ A (u : Space n) ∈ periodicSubmodule n := by
  rw [mem_periodicSubmodule_iff]
  change continuousRepresentative _ 1 = continuousRepresentative _ 0
  rw [representative_fieldData hψ A _ (by norm_num),
    representative_fieldData hψ A _ (by norm_num), hp]
  rw [← traceOne, ← traceZero, (mem_periodicSubmodule_iff _).mp u.property]

end

end Finsler.SobolevSmoothMultiplier
