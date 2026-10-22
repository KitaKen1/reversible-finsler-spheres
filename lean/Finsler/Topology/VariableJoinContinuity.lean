module

public import Finsler.Analysis.H1JoinContinuity
public import Finsler.Analysis.H1PaddingContinuity
public import Finsler.Analysis.H1PathLength

/-! Joint strong-H1 continuity of the actual concatenation when its split
varies in (0,1). Clamped times remove the moving branch from the continuity
argument. The round metric supplies the exact weak-velocity norm. -/

@[expose] public section
namespace Finsler.VariableJoinContinuity

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1LoopJoin Finsler.H1JoinContinuity
open Finsler.SobolevConcat Finsler.SobolevEnergy Finsler.SobolevEnergyDifferential
open Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

variable {n : ℕ}
abbrev Splits := Ioo (0 : ℝ) 1

def leftTime (a : Splits) (t : ClosedInterval) : ℝ := min 1 ((a : ℝ)⁻¹ * t)
def rightTime (a : Splits) (t : ClosedInterval) : ℝ := max 0 (rightMap a t)

theorem rightMap_eq (a t : ℝ) : rightMap a t = (t - a) / (1 - a) := by
  unfold rightMap
  rw [div_eq_mul_inv]
  ring

theorem leftTime_mem (a : Splits) (t : ClosedInterval) : leftTime a t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (mul_nonneg (inv_nonneg.mpr a.property.1.le) t.property.1), min_le_left _ _⟩

theorem rightTime_mem (a : Splits) (t : ClosedInterval) : rightTime a t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
  rw [rightMap_eq]
  exact (div_le_one (sub_pos.mpr a.property.2)).mpr (by linarith [t.property.2])

def value (z : Splits × composable n) : SphereLoop n :=
  join z.1 z.1.property.1 z.1.property.2 z.2.val.1 z.2.val.2 z.2.property

theorem representative_value (z : Splits × composable n) (t : ClosedInterval) :
    continuousRepresentative ((value z).data : Space n) t =
      continuousRepresentative (z.2.val.1.data : Space n) (leftTime z.1 t) +
      continuousRepresentative (z.2.val.2.data : Space n) (rightTime z.1 t) -
      continuousRepresentative (z.2.val.2.data : Space n) 0 := by
  change continuousRepresentative
    (concat (z.2.val.1.data : Space n) (z.2.val.2.data : Space n)
      z.1.property.1 z.1.property.2) t = _
  have hm := end_match z.2.val.1 z.2.val.2 z.2.property
  by_cases ht : (t : ℝ) ≤ z.1
  · have hl : leftTime z.1 t = (z.1 : ℝ)⁻¹ * t :=
      min_eq_right (H1ConcatContinuity.left_time_mem z.1.property.1 t.property ht).2
    have hr : rightTime z.1 t = 0 := by
      apply max_eq_left
      rw [rightMap_eq]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr z.1.property.2).le
    calc
      _ = continuousRepresentative (z.2.val.1.data : Space n) ((z.1 : ℝ)⁻¹ * t) :=
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
      _ = continuousRepresentative (z.2.val.2.data : Space n) (rightMap z.1 t) :=
        representative_concat_right _ _ z.1.property.1 z.1.property.2
          hm ⟨hge, t.property.2⟩
      _ = _ := by
        have hleft := (congrArg (fun τ : ℝ =>
          continuousRepresentative (z.2.val.1.data : Space n) τ) hl).trans hm
        have hright := congrArg (fun τ : ℝ =>
          continuousRepresentative (z.2.val.2.data : Space n) τ) hr
        apply Eq.symm
        calc
          _ = continuousRepresentative (z.2.val.2.data : Space n) 0 +
              continuousRepresentative (z.2.val.2.data : Space n) (rightMap z.1 t) -
              continuousRepresentative (z.2.val.2.data : Space n) 0 :=
            congrArg₂ (fun x y : Ambient n =>
              x + y - continuousRepresentative (z.2.val.2.data : Space n) 0) hleft hright
          _ = _ := by abel

theorem continuous_representative (t : ClosedInterval) :
    Continuous (fun z : Splits × composable n =>
      continuousRepresentative ((value z).data : Space n) t) := by
  have ha : Continuous (fun z : Splits × composable n => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun z : Splits × composable n => representativeL n (z.2.val.1.data : Space n)) :=
    (representativeL n).continuous.comp ((sphereLoop_data_isometry n).continuous.comp
      (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))
  have hv : Continuous (fun z : Splits × composable n => representativeL n (z.2.val.2.data : Space n)) :=
    (representativeL n).continuous.comp ((sphereLoop_data_isometry n).continuous.comp
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))
  have hl : Continuous (fun z : Splits × composable n =>
      (⟨leftTime z.1 t, leftTime_mem z.1 t⟩ : ClosedInterval)) := by
    apply Continuous.subtype_mk
    exact continuous_const.min ((ha.inv₀ (fun z => z.1.property.1.ne')).mul continuous_const)
  have hr : Continuous (fun z : Splits × composable n =>
      (⟨rightTime z.1 t, rightTime_mem z.1 t⟩ : ClosedInterval)) := by
    apply Continuous.subtype_mk
    have he : Continuous (fun z : Splits × composable n =>
        max (0 : ℝ) (((t : ℝ) - z.1) / (1 - (z.1 : ℝ)))) :=
      continuous_const.max ((continuous_const.sub ha).div
      (continuous_const.sub ha) (fun z => (sub_pos.mpr z.1.property.2).ne'))
    exact he.congr (fun z => congrArg (max 0) (rightMap_eq z.1 t).symm)
  have h0 : Continuous (fun _ : Splits × composable n => (⟨0, by norm_num⟩ : ClosedInterval)) :=
    continuous_const
  have he := ((continuous_eval.comp (hu.prodMk hl)).add
    (continuous_eval.comp (hv.prodMk hr))).sub (continuous_eval.comp (hv.prodMk h0))
  exact he.congr (fun z => (representative_value z t).symm)

theorem velocity_norm_sq (z : Splits × composable n) :
    ‖velocity ((value z).data : Space n)‖ ^ 2 =
      ‖velocity (z.2.val.1.data : Space n)‖ ^ 2 / (z.1 : ℝ) +
      ‖velocity (z.2.val.2.data : Space n)‖ ^ 2 / (1 - (z.1 : ℝ)) := by
  rw [← H1PaddingContinuity.round_energy_norm]
  change energy (roundMetric n) (join z.1 z.1.property.1 z.1.property.2
    z.2.val.1 z.2.val.2 z.2.property) = _
  rw [energy_join, H1PaddingContinuity.round_energy_norm, H1PaddingContinuity.round_energy_norm]

theorem continuous_velocity_norm :
    Continuous (fun z : Splits × composable n => ‖velocity ((value z).data : Space n)‖) := by
  have ha : Continuous (fun z : Splits × composable n => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun z : Splits × composable n => velocity (z.2.val.1.data : Space n)) :=
    (velocityL n).continuous.comp ((sphereLoop_data_isometry n).continuous.comp
      (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))
  have hv : Continuous (fun z : Splits × composable n => velocity (z.2.val.2.data : Space n)) :=
    (velocityL n).continuous.comp ((sphereLoop_data_isometry n).continuous.comp
      (continuous_snd.comp (continuous_subtype_val.comp continuous_snd)))
  have he := Real.continuous_sqrt.comp ((hu.norm.pow 2).div ha (fun z => z.1.property.1.ne') |>.add
    ((hv.norm.pow 2).div (continuous_const.sub ha) (fun z => (sub_pos.mpr z.1.property.2).ne')))
  exact he.congr (fun z => (congrArg Real.sqrt (velocity_norm_sq z)).symm.trans
    (Real.sqrt_sq (norm_nonneg _)))

theorem continuous_value : Continuous (value (n := n)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply sphereLoop_tendsto_iff.mpr
  apply SobolevWeakLimit.tendsto_of_representative_norm
  · intro t ht
    exact (continuous_representative (n := n) ⟨t, ht⟩).continuousAt
  · exact (continuous_velocity_norm (n := n)).continuousAt

end
end Finsler.VariableJoinContinuity
