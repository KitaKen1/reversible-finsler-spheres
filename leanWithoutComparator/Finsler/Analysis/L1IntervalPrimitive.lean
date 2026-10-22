module

public import Finsler.Analysis.IntervalH1WeakLimit
public import Mathlib.MeasureTheory.Function.Holder

/-! A bounded primitive map for L1 on the existing unit-interval measure.
This will control moving-endpoint restrictions of actual H1 paths. -/

@[expose] public section

namespace Finsler.L1IntervalPrimitive

open Finsler.IntervalSobolev MeasureTheory Set Filter
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

abbrev ScalarL1 := Lp ℝ 1 intervalMeasure

theorem integrable (f : ScalarL1) : Integrable f intervalMeasure :=
  memLp_one_iff_integrable.mp (Lp.memLp f)

def primitive (f : ScalarL1) : C(ClosedInterval, ℝ) :=
  ⟨fun t => ∫ x in (0 : ℝ)..t, f x ∂intervalMeasure, by
    have hc := intervalIntegral.continuousOn_primitive_interval'
      ((integrable f).intervalIntegrable (a := 0) (b := 1))
      (show (0 : ℝ) ∈ uIcc (0 : ℝ) 1 by norm_num)
    rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hc
    exact hc.domRestrict⟩

theorem primitive_bound (f : ScalarL1) (t : ClosedInterval) : |primitive f t| ≤ ‖f‖ := by
  change ‖∫ x in (0 : ℝ)..t, f x ∂intervalMeasure‖ ≤ ‖f‖
  exact intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
    ((setIntegral_le_integral (integrable f).norm (Eventually.of_forall fun _ => norm_nonneg _)).trans_eq
      (L1.norm_eq_integral_norm f).symm)

theorem primitive_norm_le (f : ScalarL1) : ‖primitive f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  exact primitive_bound f t

theorem primitive_add (f g : ScalarL1) : primitive (f + g) = primitive f + primitive g := by
  apply ContinuousMap.ext
  intro t
  change (∫ x in (0 : ℝ)..t, (f + g) x ∂intervalMeasure) = _
  rw [intervalIntegral.integral_congr_ae ((Lp.coeFn_add f g).mono (fun _ hx _ => hx))]
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add ((integrable f).intervalIntegrable) ((integrable g).intervalIntegrable)]
  rfl

theorem primitive_smul (c : ℝ) (f : ScalarL1) : primitive (c • f) = c • primitive f := by
  apply ContinuousMap.ext
  intro t
  change (∫ x in (0 : ℝ)..t, (c • f) x ∂intervalMeasure) = _
  rw [intervalIntegral.integral_congr_ae ((Lp.coeFn_smul c f).mono (fun _ hx _ => hx))]
  simp only [Pi.smul_apply]
  rw [intervalIntegral.integral_smul]
  rfl

def primitiveL : ScalarL1 →L[ℝ] C(ClosedInterval, ℝ) :=
  ({toFun := primitive, map_add' := primitive_add, map_smul' := primitive_smul} :
    ScalarL1 →ₗ[ℝ] C(ClosedInterval, ℝ)).mkContinuous 1 (by intro f; simpa using primitive_norm_le f)

theorem integral_eq_sub (f : ScalarL1) (s t : ClosedInterval) :
    (∫ x in (s : ℝ)..t, f x ∂intervalMeasure) = primitive f t - primitive f s :=
  (intervalIntegral.integral_interval_sub_left (integrable f).intervalIntegrable
    (integrable f).intervalIntegrable).symm

theorem continuous_integral :
    Continuous (fun z : ScalarL1 × (ClosedInterval × ClosedInterval) =>
      ∫ x in (z.2.1 : ℝ)..z.2.2, z.1 x ∂intervalMeasure) := by
  have hp : Continuous (fun z : ScalarL1 × (ClosedInterval × ClosedInterval) => primitiveL z.1) :=
    primitiveL.continuous.comp continuous_fst
  have ht := continuous_eval.comp (hp.prodMk (continuous_snd.comp continuous_snd))
  have hs := continuous_eval.comp (hp.prodMk (continuous_fst.comp continuous_snd))
  exact (ht.sub hs).congr (fun z => (integral_eq_sub z.1 z.2.1 z.2.2).symm)

end
end Finsler.L1IntervalPrimitive
