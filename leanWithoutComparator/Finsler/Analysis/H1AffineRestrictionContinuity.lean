module

public import Finsler.Analysis.L1IntervalPrimitive
public import Finsler.Analysis.IntervalH1AffineRestrict

/-! Joint strong-H1 continuity of actual affine restriction, including collapsed intervals.
Use the existing Radon-Riesz criterion and a bounded L1 primitive of squared velocity. -/

@[expose] public section

namespace Finsler.H1AffineRestrictionContinuity

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevAffine
open Finsler.L1IntervalPrimitive Finsler.SobolevEnergyDifferential MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ENNReal

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def squareVelocity {n : ℕ} (u : Space n) : ScalarL1 :=
  ((innerSL ℝ : Ambient n →L[ℝ] Ambient n →L[ℝ] ℝ).holderL intervalMeasure 2 2 1)
    (velocity u) (velocity u)

theorem squareVelocity_ae {n : ℕ} (u : Space n) :
    squareVelocity u =ᵐ[intervalMeasure] fun t => ‖velocity u t‖ ^ 2 := by
  have he := (innerSL ℝ : Ambient n →L[ℝ] Ambient n →L[ℝ] ℝ).coeFn_holder
    (r := 1) (velocity u) (velocity u)
  filter_upwards [he] with t ht
  change (((innerSL ℝ : Ambient n →L[ℝ] Ambient n →L[ℝ] ℝ).holderL intervalMeasure 2 2 1)
    (velocity u) (velocity u)) t = _
  rw [ContinuousLinearMap.holderL_apply_apply]
  exact ht.trans ((innerSL_apply_apply ℝ _ _).trans (real_inner_self_eq_norm_sq _))

theorem continuous_squareVelocity (n : ℕ) : Continuous (squareVelocity (n := n)) := by
  let B := (innerSL ℝ : Ambient n →L[ℝ] Ambient n →L[ℝ] ℝ).holderL intervalMeasure 2 2 1
  exact (B.continuous.comp (velocityL n).continuous).clm_apply (velocityL n).continuous

theorem integral_norm_sq {n : ℕ} (u : Space n) (s t : ClosedInterval) (hst : (s : ℝ) ≤ t) :
    (∫ x in (s : ℝ)..t, ‖velocity u x‖ ^ 2) =
      primitiveL (squareVelocity u) t - primitiveL (squareVelocity u) s := by
  have hm : (∫ x in (s : ℝ)..t, ‖velocity u x‖ ^ 2) =
      ∫ x in (s : ℝ)..t, ‖velocity u x‖ ^ 2 ∂intervalMeasure := by
    rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    change (∫ x in Ioo (s : ℝ) t, ‖velocity u x‖ ^ 2) =
      ∫ x, ‖velocity u x‖ ^ 2 ∂((volume.restrict (Ioo (0 : ℝ) 1)).restrict (Ioo (s : ℝ) t))
    rw [Measure.restrict_restrict_of_subset (Ioo_subset_Ioo s.property.1 t.property.2)]
  rw [hm, ← intervalIntegral.integral_congr_ae ((squareVelocity_ae u).mono (fun _ hx _ => hx))]
  exact integral_eq_sub (squareVelocity u) s t

theorem restriction_velocity_norm_sq {n : ℕ} (u : Space n) (s t : ClosedInterval)
    (hst : (s : ℝ) ≤ t) :
    ‖velocity (restrict u s.property t.property hst)‖ ^ 2 =
      ((t : ℝ) - s) * (primitiveL (squareVelocity u) t - primitiveL (squareVelocity u) s) := by
  rw [lp_two_norm_eq_sqrt_integral_norm_sq, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
  have he := integral_restrict_of_quadratic u s.property t.property hst
    (fun z : Ambient n × Ambient n => ‖z.2‖ ^ 2)
    (fun _ v r => by simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs])
  exact he.trans (congrArg (fun x : ℝ => ((t : ℝ) - s) * x) (integral_norm_sq u s t hst))

abbrev Intervals := {z : ClosedInterval × ClosedInterval // (z.1 : ℝ) ≤ z.2}

def restriction {n : ℕ} (z : Intervals × Space n) : Space n :=
  restrict z.2 z.1.val.1.property z.1.val.2.property z.1.property

theorem continuous_representative {n : ℕ} (τ : ClosedInterval) :
    Continuous (fun z : Intervals × Space n => continuousRepresentative (restriction z) τ) := by
  have hu : Continuous (fun z : Intervals × Space n => representativeL n z.2) :=
    (representativeL n).continuous.comp continuous_snd
  have hs : Continuous (fun z : Intervals × Space n => (z.1.val.1 : ℝ)) :=
    continuous_subtype_val.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  have ht : Continuous (fun z : Intervals × Space n => (z.1.val.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_fst))
  have htime : Continuous (fun z : Intervals × Space n =>
      (⟨aff z.1.val.1 z.1.val.2 τ,
        aff_mem_Icc z.1.val.1.property z.1.val.2.property τ.property⟩ : ClosedInterval)) := by
    apply Continuous.subtype_mk
    exact hs.add ((ht.sub hs).mul continuous_const)
  have he := continuous_eval.comp (hu.prodMk htime)
  exact he.congr (fun z =>
    (representative_restrict z.2 z.1.val.1.property z.1.val.2.property z.1.property τ.property).symm)

theorem continuous_velocity_norm {n : ℕ} :
    Continuous (fun z : Intervals × Space n => ‖velocity (restriction z)‖) := by
  have hp : Continuous (fun z : Intervals × Space n => primitiveL (squareVelocity z.2)) :=
    primitiveL.continuous.comp ((continuous_squareVelocity n).comp continuous_snd)
  have hs : Continuous (fun z : Intervals × Space n => z.1.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have ht : Continuous (fun z : Intervals × Space n => z.1.val.2) :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
  have hps := continuous_eval.comp (hp.prodMk hs)
  have hpt := continuous_eval.comp (hp.prodMk ht)
  have he := Real.continuous_sqrt.comp
    (((continuous_subtype_val.comp ht).sub (continuous_subtype_val.comp hs)).mul (hpt.sub hps))
  apply he.congr
  intro z
  change Real.sqrt (((z.1.val.2 : ℝ) - z.1.val.1) *
    (primitiveL (squareVelocity z.2) z.1.val.2 - primitiveL (squareVelocity z.2) z.1.val.1)) =
      ‖velocity (restriction z)‖
  rw [← restriction_velocity_norm_sq z.2 z.1.val.1 z.1.val.2 z.1.property,
    Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem continuous_restriction {n : ℕ} : Continuous (restriction (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply SobolevWeakLimit.tendsto_of_representative_norm
  · intro τ hτ
    exact (continuous_representative (n := n) ⟨τ, hτ⟩).continuousAt
  · exact (continuous_velocity_norm (n := n)).continuousAt

end
end Finsler.H1AffineRestrictionContinuity
