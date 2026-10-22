module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! C¹ regularity across zero for quadratically homogeneous functions.
The quadratic estimate proves the derivative at zero. Compactness of the
unit sphere and degree-one homogeneity of the derivative prove its continuity.
No twice differentiable extension at zero is asserted. -/

@[expose] public section

namespace Finsler.QuadraticHomogeneous

open Asymptotics Filter
open scoped Topology ContDiff

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ}

theorem quadratic_bound_hasFDerivAt_zero (hf : f 0 = 0) (K : ℝ)
    (hK : ∀ v, ‖f v‖ ≤ K * ‖v‖ ^ 2) :
    HasFDerivAt f (0 : V →L[ℝ] ℝ) 0 := by
  have hbig : f =O[𝓝 0] (fun v : V => ‖v‖ ^ 2) :=
    IsBigO.of_bound K (Eventually.of_forall fun v => by simpa using hK v)
  have hlittle : f =o[𝓝 0] (fun v : V => v) :=
    hbig.trans_isLittleO (isLittleO_norm_pow_id (by norm_num : 1 < 2))
  apply HasFDerivAt.of_isLittleO
  simpa only [hf, zero_apply, sub_zero] using hlittle

theorem differentiable_of_quadratic_bound (hf : f 0 = 0) (K : ℝ)
    (hK : ∀ v, ‖f v‖ ≤ K * ‖v‖ ^ 2)
    (hs : ∀ v, v ≠ 0 → ContDiffAt ℝ ∞ f v) : Differentiable ℝ f := by
  intro v
  by_cases hv : v = 0
  · subst v
    exact (quadratic_bound_hasFDerivAt_zero hf K hK).differentiableAt
  · exact (hs v hv).differentiableAt (by simp)

theorem fderiv_smul (hd : Differentiable ℝ f)
    (hh : ∀ (r : ℝ) v, f (r • v) = r ^ 2 * f v) (r : ℝ) (hr : r ≠ 0) (v : V) :
    fderiv ℝ f (r • v) = r • fderiv ℝ f v := by
  have hleft := (hd (r • v)).hasFDerivAt.comp v ((hasFDerivAt_id v).const_smul r)
  have hright := (hd v).hasFDerivAt.const_smul (r ^ 2)
  have he : (f ∘ fun w : V => r • w) = fun w => r ^ 2 • f w :=
    funext fun w => by simpa only [Function.comp_apply, smul_eq_mul] using hh r w
  rw [he] at hleft
  have h := hleft.unique hright
  apply ContinuousLinearMap.ext
  intro w
  have hw := congrArg (fun L : V →L[ℝ] ℝ => L w) h
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hw ⊢
  apply mul_left_cancel₀ hr
  simpa only [pow_two, mul_assoc] using hw

theorem exists_fderiv_bound [FiniteDimensional ℝ V]
    (hd : Differentiable ℝ f) (hzero : fderiv ℝ f 0 = 0)
    (hs : ∀ v, v ≠ 0 → ContDiffAt ℝ ∞ f v)
    (hh : ∀ (r : ℝ) v, f (r • v) = r ^ 2 * f v) :
    ∃ K : ℝ, 0 < K ∧ ∀ v, ‖fderiv ℝ f v‖ ≤ K * ‖v‖ := by
  have hc : ContinuousOn (fun v : V => ‖fderiv ℝ f v‖) (Metric.sphere 0 1) := by
    intro v hv
    have hv' : v ≠ 0 := by
      intro h
      simp [h] at hv
    exact ((hs v hv').continuousAt_fderiv (by simp)).norm.continuousWithinAt
  obtain ⟨K, hK⟩ := (isCompact_sphere (0 : V) 1).bddAbove_image hc
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right K 1), ?_⟩
  intro v
  by_cases hv : v = 0
  · simp [hv, hzero]
  · have hn := norm_ne_zero_iff.mpr hv
    let w : V := ‖v‖⁻¹ • v
    have hw : w ∈ Metric.sphere (0 : V) 1 := by
      simp [w, norm_smul, inv_mul_cancel₀ hn]
    have hscale : ‖v‖ • w = v := by
      simp [w, smul_smul, mul_inv_cancel₀ hn]
    have he : fderiv ℝ f v = ‖v‖ • fderiv ℝ f w := by
      convert fderiv_smul hd hh ‖v‖ hn w using 1
      exact congrArg (fderiv ℝ f) hscale.symm
    calc
      ‖fderiv ℝ f v‖ = ‖v‖ * ‖fderiv ℝ f w‖ := by
        rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg v)]
      _ ≤ ‖v‖ * max K 1 := mul_le_mul_of_nonneg_left
        ((hK ⟨w, hw, rfl⟩).trans (le_max_left K 1)) (norm_nonneg v)
      _ = max K 1 * ‖v‖ := mul_comm _ _

theorem continuous_fderiv [FiniteDimensional ℝ V]
    (hd : Differentiable ℝ f) (hzero : fderiv ℝ f 0 = 0)
    (hs : ∀ v, v ≠ 0 → ContDiffAt ℝ ∞ f v)
    (hh : ∀ (r : ℝ) v, f (r • v) = r ^ 2 * f v) : Continuous (fderiv ℝ f) := by
  obtain ⟨K, _hK, hb⟩ := exists_fderiv_bound hd hzero hs hh
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    change Tendsto (fderiv ℝ f) (𝓝 0) (𝓝 (fderiv ℝ f 0))
    rw [hzero, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun w : V => norm_nonneg (fderiv ℝ f w)) hb
    have ht : Continuous (fun w : V => K * ‖w‖) := continuous_const.mul continuous_norm
    simpa using (ht.continuousAt (x := (0 : V))).tendsto
  · exact (hs v hv).continuousAt_fderiv (by simp)

theorem contDiff_one [FiniteDimensional ℝ V] (hf : f 0 = 0) (K : ℝ)
    (hK : ∀ v, ‖f v‖ ≤ K * ‖v‖ ^ 2)
    (hs : ∀ v, v ≠ 0 → ContDiffAt ℝ ∞ f v)
    (hh : ∀ (r : ℝ) v, f (r • v) = r ^ 2 * f v) : ContDiff ℝ 1 f := by
  have hd := differentiable_of_quadratic_bound hf K hK hs
  have hz := (quadratic_bound_hasFDerivAt_zero hf K hK).fderiv
  exact contDiff_one_iff_fderiv.mpr ⟨hd, continuous_fderiv hd hz hs hh⟩

end

end Finsler.QuadraticHomogeneous
