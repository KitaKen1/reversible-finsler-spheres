module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! One-dimensional chain rule for a C¹ map of a primitive on [0,1]. Every
continuous linear functional of the composition is dominated by the absolutely
continuous primitive of the velocity norm, so mathlib's fundamental theorem of
calculus for absolutely continuous functions applies; the dual separates points.
Only a finite-dimensional source and a complete target are assumed. -/

@[expose] public section

namespace Finsler.IntervalChainRule

open MeasureTheory Set Filter
open scoped Topology Interval

noncomputable section

/-- Domination by an absolutely continuous scalar function gives absolute continuity. -/
theorem absolutelyContinuous_of_dist_le {g N : ℝ → ℝ} {a b K : ℝ} (hK : 0 ≤ K)
    (hN : AbsolutelyContinuousOnInterval N a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (g x) (g y) ≤ K * dist (N x) (N y)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hN ⊢
  intro ε hε
  obtain ⟨δ, hδ, hN'⟩ := hN (ε / (K + 1)) (by positivity)
  refine ⟨δ, hδ, fun E hE hsum => ?_⟩
  have hlt := hN' E hE hsum
  have hnn : 0 ≤ ∑ i ∈ Finset.range E.1, dist (N (E.2 i).1) (N (E.2 i).2) :=
    Finset.sum_nonneg fun _ _ => dist_nonneg
  calc
    ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2)
        ≤ ∑ i ∈ Finset.range E.1, K * dist (N (E.2 i).1) (N (E.2 i).2) :=
      Finset.sum_le_sum fun i hi => h _ (hE.1 i hi).1 _ (hE.1 i hi).2
    _ = K * ∑ i ∈ Finset.range E.1, dist (N (E.2 i).1) (N (E.2 i).2) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (K + 1) * ∑ i ∈ Finset.range E.1, dist (N (E.2 i).1) (N (E.2 i).2) := by
      gcongr
      linarith
    _ < (K + 1) * (ε / (K + 1)) := by gcongr
    _ = ε := by field_simp

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] in
theorem dist_le_dist_normPrimitive {w w' : ℝ → E} (hw' : IntervalIntegrable w' volume 0 1)
    (hprim : ∀ t ∈ Icc (0 : ℝ) 1, w t = w 0 + ∫ s in (0 : ℝ)..t, w' s)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    dist (w x) (w y) ≤
      dist (∫ s in (0 : ℝ)..x, ‖w' s‖) (∫ s in (0 : ℝ)..y, ‖w' s‖) := by
  have hsub (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : uIcc (0 : ℝ) z ⊆ uIcc 0 1 := by
    rw [uIcc_of_le hz.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hz.2
  have hix := hw'.mono_set (hsub x hx)
  have hiy := hw'.mono_set (hsub y hy)
  have hw : w x - w y = ∫ s in y..x, w' s := by
    rw [hprim x hx, hprim y hy, add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left hix hiy]
  have hN : (∫ s in (0 : ℝ)..x, ‖w' s‖) - ∫ s in (0 : ℝ)..y, ‖w' s‖ = ∫ s in y..x, ‖w' s‖ :=
    intervalIntegral.integral_interval_sub_left hix.norm hiy.norm
  rw [dist_eq_norm, hw, Real.dist_eq, hN]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- One-dimensional chain rule for a C¹ map of a primitive with integrable velocity. -/
theorem comp_sub_eq_integral {w w' : ℝ → E} {Γ : E → F} (hΓ : ContDiff ℝ 1 Γ)
    (hw' : IntervalIntegrable w' volume 0 1)
    (hprim : ∀ t ∈ Icc (0 : ℝ) 1, w t = w 0 + ∫ s in (0 : ℝ)..t, w' s)
    (hd : ∀ᵐ s ∂(volume.restrict (Ioo (0 : ℝ) 1)), HasDerivAt w (w' s) s)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Γ (w t) - Γ (w 0) = ∫ s in (0 : ℝ)..t, fderiv ℝ Γ (w s) (w' s) := by
  have hcont : ContinuousOn w (Icc 0 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hw' (show (0 : ℝ) ∈ uIcc 0 1 by simp)
    rw [uIcc_of_le zero_le_one] at h
    exact (continuousOn_const.add h).congr fun s hs => hprim s hs
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hmaps : MapsTo w (Icc (0 : ℝ) 1) (Metric.closedBall (0 : E) R) := fun s hs =>
    mem_closedBall_zero_iff.mpr (hR s hs)
  obtain ⟨K, hK⟩ := (hΓ.contDiffOn (s := Metric.closedBall (0 : E) R)).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hNac : AbsolutelyContinuousOnInterval (fun x => ∫ s in (0 : ℝ)..x, ‖w' s‖) 0 1 :=
    hw'.norm.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hdiffΓ : Differentiable ℝ Γ := hΓ.differentiable (by norm_num)
  -- integrability of the chain-rule integrand on [0,1]
  have hDcont : ContinuousOn (fun s => fderiv ℝ Γ (w s)) (Icc 0 1) :=
    (hΓ.continuous_fderiv (by norm_num)).comp_continuousOn hcont
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hDcont
  have hint01 : IntervalIntegrable (fun s => fderiv ℝ Γ (w s) (w' s)) volume 0 1 := by
    have hmeas : AEStronglyMeasurable (fun s => fderiv ℝ Γ (w s) (w' s))
        (volume.restrict (Ι (0 : ℝ) 1)) := by
      have he : Continuous (fun p : (E →L[ℝ] F) × E => p.1 p.2) :=
        continuous_fst.clm_apply continuous_snd
      have hD : AEStronglyMeasurable (fun s => fderiv ℝ Γ (w s)) (volume.restrict (Ι (0 : ℝ) 1)) := by
        rw [uIoc_of_le zero_le_one]
        exact (hDcont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
      exact he.comp_aestronglyMeasurable (hD.prodMk hw'.def'.aestronglyMeasurable)
    refine (hw'.norm.const_mul C).mono_fun' hmeas ?_
    rw [uIoc_of_le zero_le_one]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact ((fderiv ℝ Γ (w s)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hC s (Ioc_subset_Icc_self hs)) (norm_nonneg _))
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ht.2
  have hint : IntervalIntegrable (fun s => fderiv ℝ Γ (w s) (w' s)) volume 0 t :=
    hint01.mono_set hsub
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro ℓ
  have hgac : AbsolutelyContinuousOnInterval (fun x => ℓ (Γ (w x))) 0 1 := by
    apply absolutelyContinuous_of_dist_le (K := ‖ℓ‖ * K) (by positivity) hNac
    intro x hx y hy
    rw [uIcc_of_le zero_le_one] at hx hy
    calc
      dist (ℓ (Γ (w x))) (ℓ (Γ (w y))) ≤ ‖ℓ‖ * dist (Γ (w x)) (Γ (w y)) := by
        rw [dist_eq_norm, dist_eq_norm, ← map_sub]
        exact ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * (K * dist (w x) (w y)) :=
        mul_le_mul_of_nonneg_left (hK.dist_le_mul _ (hmaps hx) _ (hmaps hy)) (norm_nonneg _)
      _ ≤ ‖ℓ‖ * (K * dist (∫ s in (0 : ℝ)..x, ‖w' s‖) (∫ s in (0 : ℝ)..y, ‖w' s‖)) := by
        gcongr
        exact dist_le_dist_normPrimitive hw' hprim hx hy
      _ = ‖ℓ‖ * K * dist (∫ s in (0 : ℝ)..x, ‖w' s‖) (∫ s in (0 : ℝ)..y, ‖w' s‖) := by ring
  have hftc := (hgac.mono hsub).integral_deriv_eq_sub
  have hderiv : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) t →
      deriv (fun x => ℓ (Γ (w x))) s = ℓ (fderiv ℝ Γ (w s) (w' s)) := by
    have h1 := hd
    rw [restrict_Ioo_eq_restrict_Icc] at h1
    have hsub' : Ι (0 : ℝ) t ⊆ Icc 0 1 := by
      rw [uIoc_of_le ht.1]
      exact fun x hx => ⟨hx.1.le, hx.2.trans ht.2⟩
    have h2 := ae_restrict_of_ae_restrict_of_subset hsub' h1
    filter_upwards [(ae_restrict_iff' measurableSet_uIoc).mp h2] with s hs hsI
    have hws := hs hsI
    have hc := ((hdiffΓ (w s)).hasFDerivAt.comp_hasDerivAt s hws)
    exact (ℓ.hasFDerivAt.comp_hasDerivAt s hc).deriv
  rw [map_sub, ← hftc, intervalIntegral.integral_congr_ae hderiv,
    ℓ.intervalIntegral_comp_comm hint]

end

end Finsler.IntervalChainRule
