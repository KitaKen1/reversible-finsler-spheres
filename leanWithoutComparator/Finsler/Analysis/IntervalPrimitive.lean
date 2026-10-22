module

public import Finsler.Analysis.IntervalWeakConstant
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.Normed.Module.Dual

/-! Primitive of an integrable velocity on [0,1], and its genuine weak derivative.
The scalar integration-by-parts theorem uses absolute continuity; a.e. classical
differentiability alone is not substituted for weak differentiability. -/

@[expose] public section

namespace Finsler.IntervalPrimitive

open MeasureTheory Set Filter TopologicalSpace intervalIntegral
open scoped Topology ContDiff

noncomputable section

def primitive {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : ℝ → F) (t : ℝ) : F := ∫ s in (0 : ℝ)..t, v s

theorem scalar_primitive_ibp {v ψ : ℝ → ℝ}
    (hv : IntervalIntegrable v volume 0 1) (hψ : ContDiff ℝ ∞ ψ)
    (_hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ Ioo 0 1) :
    (∫ t, deriv ψ t * primitive v t) = -(∫ t, ψ t * v t) := by
  have hP := hv.absolutelyContinuousOnInterval_intervalIntegral
    (show (0 : ℝ) ∈ uIcc 0 1 by norm_num)
  have hψAC := (hψ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).contDiffOn.absolutelyContinuousOnInterval
    (a := (0 : ℝ)) (b := 1)
  have he := hP.integral_mul_deriv_eq_deriv_mul hψAC
  have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun hx => by
    have h0 := (hψs hx).1
    exact lt_irrefl _ h0)
  have hψ1 : ψ 1 = 0 := image_eq_zero_of_notMem_tsupport (fun hx => by
    have h1 := (hψs hx).2
    exact lt_irrefl _ h1)
  rw [hψ0, hψ1, mul_zero, mul_zero, sub_self, zero_sub] at he
  have hderiv : (∫ t in (0 : ℝ)..1, deriv (primitive v) t * ψ t) =
      ∫ t in (0 : ℝ)..1, v t * ψ t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hv.ae_hasDerivAt_integral] with t ht hmem
    have hd := ht (uIoc_subset_uIcc hmem) 0 (show (0 : ℝ) ∈ uIcc 0 1 by norm_num)
    exact congrArg (fun r : ℝ => r * ψ t) hd.deriv
  change (∫ t in (0 : ℝ)..1, primitive v t * deriv ψ t) =
    -(∫ t in (0 : ℝ)..1, deriv (primitive v) t * ψ t) at he
  rw [hderiv] at he
  have hleft : (∫ t in (0 : ℝ)..1, primitive v t * deriv ψ t) =
      ∫ t, deriv ψ t * primitive v t := by
    rw [integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply MeasureTheory.integral_congr_ae
      exact Eventually.of_forall fun t => mul_comm _ _
    · intro t ht
      have hz : deriv ψ t = 0 := by
        have hts : t ∉ tsupport ψ := fun hx => ht (hψs hx)
        have heq : ψ =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
          have hev := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hts
          filter_upwards [hev] with s hs
          exact image_eq_zero_of_notMem_tsupport hs
        exact (heq.deriv_eq).trans (deriv_const t 0)
      rw [hz, mul_zero]
  have hright : (∫ t in (0 : ℝ)..1, v t * ψ t) = ∫ t, ψ t * v t := by
    rw [integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply MeasureTheory.integral_congr_ae
      exact Eventually.of_forall fun t => mul_comm _ _
    · intro t ht
      rw [image_eq_zero_of_notMem_tsupport (fun hx => ht (hψs hx)), mul_zero]
  rwa [hleft, hright] at he

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem primitive_continuousOn {v : ℝ → F} (hv : IntervalIntegrable v volume 0 1) :
    ContinuousOn (primitive v) (Icc 0 1) := by
  change ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, v s) (Icc 0 1)
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    continuousOn_primitive_interval' hv (show (0 : ℝ) ∈ uIcc 0 1 by norm_num)

theorem primitive_hasWeakLineDeriv {v : ℝ → F} (hv : IntervalIntegrable v volume 0 1) :
    TauCeti.HasWeakLineDerivOn volume ⟨Ioo 0 1, isOpen_Ioo⟩ (primitive v) v 1 := by
  have hp : LocallyIntegrableOn (primitive v) (Ioo 0 1) volume :=
    ((primitive_continuousOn hv).mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  have hvl : LocallyIntegrableOn v (Ioo 0 1) volume :=
    (hv.1.mono_set Ioo_subset_Ioc_self).locallyIntegrableOn
  apply (TauCeti.hasWeakLineDerivOn_iff hp hvl).mpr
  intro ψ hψ hψc hψs
  have hd (t : ℝ) : lineDeriv ℝ ψ t 1 = deriv ψ t := by
    rw [(hψ.differentiable (by simp) t).lineDeriv_eq_fderiv, fderiv_apply_one_eq_deriv]
  simp only [hd]
  have hiP : Integrable (fun t => deriv ψ t • primitive v t) := by
    have hi := TauCeti.integrable_lineDeriv_smul_of_locallyIntegrableOn
      (Ω := ⟨Ioo 0 1, isOpen_Ioo⟩) hp ⟨ψ, hψ, hψc, hψs⟩ 1
    change Integrable (fun t => lineDeriv ℝ ψ t 1 • primitive v t) at hi
    simpa only [hd] using hi
  have hiv : Integrable (fun t => ψ t • v t) :=
    TauCeti.integrable_smul_of_locallyIntegrableOn
      (Ω := ⟨Ioo 0 1, isOpen_Ioo⟩) hvl ⟨ψ, hψ, hψc, hψs⟩
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  rw [← L.integral_comp_comm hiP, map_neg, ← L.integral_comp_comm hiv]
  simp only [map_smul, smul_eq_mul]
  have hLv : IntervalIntegrable (fun t => L (v t)) volume 0 1 :=
    ⟨L.integrable_comp hv.1, L.integrable_comp hv.2⟩
  have hLP : (∫ t, deriv ψ t * L (primitive v t)) =
      ∫ t, deriv ψ t * primitive (fun t => L (v t)) t := by
    apply MeasureTheory.integral_congr_ae
    apply Eventually.of_forall
    intro t
    by_cases ht : t ∈ Ioo 0 1
    · have hvt : IntervalIntegrable v volume 0 t := by
        refine ⟨hv.1.mono_set (Ioc_subset_Ioc le_rfl ht.2.le), ?_⟩
        simp only [Ioc_eq_empty (not_lt.mpr ht.1.le), integrableOn_empty]
      change deriv ψ t * L (∫ s in (0 : ℝ)..t, v s) =
        deriv ψ t * (∫ s in (0 : ℝ)..t, L (v s))
      rw [L.intervalIntegral_comp_comm hvt]
    · have hts : t ∉ tsupport ψ := fun hx => ht (hψs hx)
      change deriv ψ t * L (primitive v t) =
        deriv ψ t * primitive (fun t => L (v t)) t
      rw [deriv_of_notMem_tsupport hts, zero_mul, zero_mul]
  rw [hLP]
  exact scalar_primitive_ibp hLv hψ hψc hψs

end

end Finsler.IntervalPrimitive
