module

public import Finsler.Topology.FirstHalfSplits
public import Finsler.Analysis.H1SelfCutNeighborhood

/-! Literal first-half evaluation and affine restrictions of the actual
half-time concatenation. These are equalities of H1 graph elements. -/

@[expose] public section
namespace Finsler.HalfConcatRestriction

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevConcat Finsler.SobolevAffine Finsler.VariableJoinContinuity
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {n : ℕ}

def half (t : ClosedInterval) : ClosedInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

def pointTime (t : FirstHalfSplits.Times) : ClosedInterval := ⟨t, t.property.1, t.property.2.le⟩

def tailSplit (t : FirstHalfSplits.Times) : Splits :=
  ⟨(1 - (t : ℝ)) / (2 - (t : ℝ)), by
    have hn : 0 < 1 - (t : ℝ) := sub_pos.mpr t.property.2
    have hd : 0 < 2 - (t : ℝ) := by linarith [t.property.2]
    exact ⟨div_pos hn hd, (div_lt_one hd).mpr (by linarith)⟩⟩

theorem evaluate (u v : Space n) (t : ClosedInterval) :
    continuousRepresentative (concat u v (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)) (half t) =
      continuousRepresentative u t := by
  have ht : (half t : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := by
    change 0 ≤ (t : ℝ) / 2 ∧ (t : ℝ) / 2 ≤ 1 / 2
    constructor <;> linarith [t.property.1, t.property.2]
  rw [representative_concat_left u v (by norm_num) (by norm_num) ht]
  congr 1
  change (1 / 2 : ℝ)⁻¹ * ((t : ℝ) / 2) = (t : ℝ)
  norm_num
  ring

theorem prefix_path (u v : Space n) (t : ClosedInterval) :
    restrict (concat u v (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num)) zero_mem_unit
      (half t).property (half t).property.1 = restrict u zero_mem_unit t.property t.property.1 := by
  apply eq_of_representative_eqOn
  intro τ hτ
  rw [representative_restrict _ _ _ _ hτ, representative_restrict _ _ _ _ hτ]
  have hp := mul_le_of_le_one_right (by linarith [t.property.1] : 0 ≤ (t : ℝ) / 2) hτ.2
  have ht : aff 0 (half t) τ ∈ Icc (0 : ℝ) (1 / 2) := by
    dsimp [aff, half]
    constructor
    · nlinarith [mul_nonneg t.property.1 hτ.1]
    · nlinarith [t.property.2]
  rw [representative_concat_left u v (by norm_num) (by norm_num) ht]
  congr 1
  norm_num [aff, half]
  <;> ring

theorem suffix (u v : Space n) (t : FirstHalfSplits.Times)
    (hm : continuousRepresentative u 1 = continuousRepresentative v 0) :
    restrict (concat u v (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num))
      (half (pointTime t)).property one_mem_unit (half (pointTime t)).property.2 =
      concat (restrict u (pointTime t).property one_mem_unit (pointTime t).property.2) v
        (tailSplit t).property.1 (tailSplit t).property.2 := by
  apply eq_of_representative_eqOn
  intro τ hτ
  rw [representative_restrict _ _ _ _ hτ]
  have hd : 0 < 2 - (t : ℝ) := by linarith [t.property.2]
  have hn : 0 < 1 - (t : ℝ) := sub_pos.mpr t.property.2
  have hθ := aff_mem_Icc (half (pointTime t)).property one_mem_unit hτ
  have hms : continuousRepresentative
      (restrict u (pointTime t).property one_mem_unit (pointTime t).property.2) 1 =
      continuousRepresentative v 0 :=
    (representative_restrict_one _ _ _ _).trans hm
  by_cases hle : τ ≤ (tailSplit t : ℝ)
  · have hscaled : τ * (2 - (t : ℝ)) ≤ 1 - (t : ℝ) := (le_div_iff₀ hd).mp hle
    have ht : aff (half (pointTime t)) 1 τ ∈ Icc (0 : ℝ) (1 / 2) := by
      refine ⟨hθ.1, ?_⟩
      change (t : ℝ) / 2 + (1 - (t : ℝ) / 2) * τ ≤ 1 / 2
      nlinarith
    rw [representative_concat_left u v (by norm_num) (by norm_num) ht,
      representative_concat_left _ _ (tailSplit t).property.1 (tailSplit t).property.2 ⟨hτ.1, hle⟩,
      representative_restrict _ _ _ _ (H1ConcatContinuity.left_time_mem (tailSplit t).property.1 hτ hle)]
    congr 1
    dsimp [aff, half, pointTime, tailSplit]
    field_simp
    <;> ring
  · have hge : (tailSplit t : ℝ) ≤ τ := (lt_of_not_ge hle).le
    have hscaled : 1 - (t : ℝ) ≤ τ * (2 - (t : ℝ)) := (div_le_iff₀ hd).mp hge
    have ht : aff (half (pointTime t)) 1 τ ∈ Icc (1 / 2 : ℝ) 1 := by
      refine ⟨?_, hθ.2⟩
      change 1 / 2 ≤ (t : ℝ) / 2 + (1 - (t : ℝ) / 2) * τ
      nlinarith
    rw [representative_concat_right u v (by norm_num) (by norm_num) hm ht,
      representative_concat_right _ _ (tailSplit t).property.1 (tailSplit t).property.2 hms ⟨hge, hτ.2⟩]
    congr 1
    dsimp [rightMap, aff, half, pointTime, tailSplit]
    field_simp
    <;> ring

end
end Finsler.HalfConcatRestriction
