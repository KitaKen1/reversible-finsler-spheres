module

public import Finsler.Topology.VariableJoinContinuity

/-! Joint strong H1 continuity for variable-split concatenation of actual
matching sphere paths. The individual pieces need not be closed loops. -/

@[expose] public section
namespace Finsler.VariablePathConcat

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevConcat Finsler.SobolevSpherePath Finsler.SobolevEnergy
open Finsler.SobolevEnergyDifferential Finsler.AmbientLagrangian
open Finsler.VariableJoinContinuity MeasureTheory Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

variable {n : ℕ}

def Pairs (n : ℕ) : Set (Space n × Space n) := {p | p.1 ∈ SpherePath n ∧ p.2 ∈ SpherePath n ∧
  continuousRepresentative p.1 1 = continuousRepresentative p.2 0}

def value (z : Splits × Pairs n) : Space n :=
  concat z.2.val.1 z.2.val.2 z.1.property.1 z.1.property.2

theorem value_mem (z : Splits × Pairs n) : value z ∈ SpherePath n :=
  concat_mem z.2.val.1 z.2.val.2 z.1.property.1 z.1.property.2
    z.2.property.1 z.2.property.2.1 z.2.property.2.2

theorem round_pathEnergy_norm (w : Space n) (hw : w ∈ SpherePath n) :
    pathEnergy (roundMetric n) w = ‖velocity w‖ ^ 2 := by
  have he : (fun t => lagrangian (roundMetric n) (continuousRepresentative w t, velocity w t)) =ᵐ[intervalMeasure]
      fun t => ‖velocity w t‖ ^ 2 := by
    filter_upwards [jet_has_tangent_ae hw] with t ht
    obtain ⟨p, hp⟩ := ht
    have hv : ambientVector n p = velocity w t := congrArg Prod.snd hp
    rw [← hp, lagrangian_ambientPair]
    change ‖ambientVector n p‖ ^ 2 = _
    rw [hv]
  rw [pathEnergy, integral_congr_ae he, lp_two_norm_eq_sqrt_integral_norm_sq,
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]

theorem representative_value (z : Splits × Pairs n) (t : ClosedInterval) :
    continuousRepresentative (value z) t =
      continuousRepresentative z.2.val.1 (leftTime z.1 t) +
      continuousRepresentative z.2.val.2 (rightTime z.1 t) -
      continuousRepresentative z.2.val.2 0 := by
  change continuousRepresentative
    (concat z.2.val.1 z.2.val.2
      z.1.property.1 z.1.property.2) t = _
  have hm := z.2.property.2.2
  by_cases ht : (t : ℝ) ≤ z.1
  · have hl : leftTime z.1 t = (z.1 : ℝ)⁻¹ * t :=
      min_eq_right (H1ConcatContinuity.left_time_mem z.1.property.1 t.property ht).2
    have hr : rightTime z.1 t = 0 := by
      apply max_eq_left
      rw [rightMap_eq]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr z.1.property.2).le
    calc
      _ = continuousRepresentative z.2.val.1 ((z.1 : ℝ)⁻¹ * t) :=
        representative_concat_left _ _ z.1.property.1 z.1.property.2 ⟨t.property.1, ht⟩
      _ = _ := by rw [hl, hr]; abel
  · have hge : (z.1 : ℝ) ≤ t := (lt_of_not_ge ht).le
    have hl : leftTime z.1 t = 1 := by
      apply min_eq_left
      calc
        1 = (z.1 : ℝ)⁻¹ * z.1 := (inv_mul_cancel₀ z.1.property.1.ne').symm
        _ ≤ (z.1 : ℝ)⁻¹ * t := mul_le_mul_of_nonneg_left hge (inv_nonneg.mpr z.1.property.1.le)
    have hr : rightTime z.1 t = rightMap z.1 t :=
      max_eq_right (H1ConcatContinuity.right_time_mem z.1.property.2 t.property hge).1
    calc
      _ = continuousRepresentative z.2.val.2 (rightMap z.1 t) :=
        representative_concat_right _ _ z.1.property.1 z.1.property.2
          hm ⟨hge, t.property.2⟩
      _ = _ := by
        have hleft := (congrArg (fun τ : ℝ =>
          continuousRepresentative z.2.val.1 τ) hl).trans hm
        have hright := congrArg (fun τ : ℝ =>
          continuousRepresentative z.2.val.2 τ) hr
        apply Eq.symm
        calc
          _ = continuousRepresentative z.2.val.2 0 +
              continuousRepresentative z.2.val.2 (rightMap z.1 t) -
              continuousRepresentative z.2.val.2 0 :=
            congrArg₂ (fun x y : Ambient n =>
              x + y - continuousRepresentative z.2.val.2 0) hleft hright
          _ = _ := by abel

theorem continuous_representative (t : ClosedInterval) :
    Continuous (fun z : Splits × Pairs n => continuousRepresentative (value z) t) := by
  have ha : Continuous (fun z : Splits × Pairs n => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun z : Splits × Pairs n => representativeL n z.2.val.1) :=
    (representativeL n).continuous.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
  have hv : Continuous (fun z : Splits × Pairs n => representativeL n z.2.val.2) :=
    (representativeL n).continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
  have hl : Continuous (fun z : Splits × Pairs n =>
      (⟨leftTime z.1 t, leftTime_mem z.1 t⟩ : ClosedInterval)) := by
    apply Continuous.subtype_mk
    exact continuous_const.min ((ha.inv₀ (fun z => z.1.property.1.ne')).mul continuous_const)
  have hr : Continuous (fun z : Splits × Pairs n =>
      (⟨rightTime z.1 t, rightTime_mem z.1 t⟩ : ClosedInterval)) := by
    apply Continuous.subtype_mk
    have he : Continuous (fun z : Splits × Pairs n =>
        max (0 : ℝ) (((t : ℝ) - z.1) / (1 - (z.1 : ℝ)))) :=
      continuous_const.max ((continuous_const.sub ha).div
      (continuous_const.sub ha) (fun z => (sub_pos.mpr z.1.property.2).ne'))
    exact he.congr (fun z => congrArg (max 0) (rightMap_eq z.1 t).symm)
  have h0 : Continuous (fun _ : Splits × Pairs n => (⟨0, by norm_num⟩ : ClosedInterval)) :=
    continuous_const
  have he := ((continuous_eval.comp (hu.prodMk hl)).add
    (continuous_eval.comp (hv.prodMk hr))).sub (continuous_eval.comp (hv.prodMk h0))
  exact he.congr (fun z => (representative_value z t).symm)

theorem velocity_norm_sq (z : Splits × Pairs n) :
    ‖velocity (value z)‖ ^ 2 =
      ‖velocity z.2.val.1‖ ^ 2 / (z.1 : ℝ) + ‖velocity z.2.val.2‖ ^ 2 / (1 - (z.1 : ℝ)) := by
  rw [← round_pathEnergy_norm (value z) (value_mem z)]
  change pathEnergy (roundMetric n) (concat z.2.val.1 z.2.val.2 z.1.property.1 z.1.property.2) = _
  rw [pathEnergy_concat (u := z.2.val.1) (w := z.2.val.2) z.1.property.1 z.1.property.2 (roundMetric n)
      z.2.property.1 z.2.property.2.1 z.2.property.2.2,
    round_pathEnergy_norm z.2.val.1 z.2.property.1,
    round_pathEnergy_norm z.2.val.2 z.2.property.2.1]

theorem continuous_velocity_norm :
    Continuous (fun z : Splits × Pairs n => ‖velocity (value z)‖) := by
  have ha : Continuous (fun z : Splits × Pairs n => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun z : Splits × Pairs n => velocity z.2.val.1) :=
    (velocityL n).continuous.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_snd))
  have hv : Continuous (fun z : Splits × Pairs n => velocity z.2.val.2) :=
    (velocityL n).continuous.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_snd))
  have he := Real.continuous_sqrt.comp ((hu.norm.pow 2).div ha (fun z => z.1.property.1.ne') |>.add
    ((hv.norm.pow 2).div (continuous_const.sub ha) (fun z => (sub_pos.mpr z.1.property.2).ne')))
  exact he.congr (fun z => (congrArg Real.sqrt (velocity_norm_sq z)).symm.trans
    (Real.sqrt_sq (norm_nonneg _)))

theorem continuous_value : Continuous (value (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply SobolevWeakLimit.tendsto_of_representative_norm
  · intro t ht
    exact (continuous_representative (n := n) ⟨t, ht⟩).continuousAt
  · exact (continuous_velocity_norm (n := n)).continuousAt

theorem length_value (F : ReversibleMetric n) (z : Splits × Pairs n) :
    H1PathLength.length F (value z) =
      H1PathLength.length F z.2.val.1 + H1PathLength.length F z.2.val.2 :=
  H1PathLength.length_concat F z.2.val.1 z.2.val.2 z.1.property.1 z.1.property.2
    z.2.property.1 z.2.property.2.1 z.2.property.2.2

end
end Finsler.VariablePathConcat
