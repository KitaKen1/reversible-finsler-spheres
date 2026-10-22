module

public import Finsler.Topology.HalfConcatRestriction

/-! Literal rebracketing of the three actual retained H1 paths at the
first-half timings. This preserves the parametrized graph element. -/

@[expose] public section
namespace Finsler.FirstHalfRebracket

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevConcat Finsler.VariableJoinContinuity
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem concat_eq {n : ℕ} (u v w : Space n) (t : FirstHalfSplits.Times)
    (huv : continuousRepresentative u 1 = continuousRepresentative v 0)
    (hvw : continuousRepresentative v 1 = continuousRepresentative w 0) :
    concat u (concat v w (HalfConcatRestriction.tailSplit t).property.1
      (HalfConcatRestriction.tailSplit t).property.2) (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num) =
    concat (concat u v (FirstHalfSplits.inner t).property.1 (FirstHalfSplits.inner t).property.2)
      w (FirstHalfSplits.outer t).property.1 (FirstHalfSplits.outer t).property.2 := by
  let a := FirstHalfSplits.inner t
  let b := FirstHalfSplits.outer t
  let k := HalfConcatRestriction.tailSplit t
  have hn : 0 < 1 - (t : ℝ) := sub_pos.mpr t.property.2
  have hd : 0 < 2 - (t : ℝ) := by linarith [t.property.2]
  have he : 0 < 3 - 2 * (t : ℝ) := by linarith [t.property.2]
  have hab : (b : ℝ) * a = 1 / 2 := FirstHalfSplits.first_duration t
  have hbk : (b : ℝ) = (1 + (k : ℝ)) / 2 := by
    dsimp [b, k, FirstHalfSplits.outer, HalfConcatRestriction.tailSplit]
    field_simp
    <;> ring
  have hhalf : (1 / 2 : ℝ) < b := by linarith [k.property.1]
  have hac : 1 - (a : ℝ) = (1 - (t : ℝ)) / (3 - 2 * (t : ℝ)) := by
    dsimp [a, FirstHalfSplits.inner]
    field_simp
    <;> ring
  have hbc : 1 - (b : ℝ) = 1 / (2 * (2 - (t : ℝ))) := FirstHalfSplits.third_duration t
  have hkc : 1 - (k : ℝ) = 1 / (2 - (t : ℝ)) := by
    dsimp [k, HalfConcatRestriction.tailSplit]
    field_simp
    <;> ring
  have hul : continuousRepresentative u 1 = continuousRepresentative (concat v w k.property.1 k.property.2) 0 :=
    huv.trans (representative_concat_zero v w k.property.1 k.property.2).symm
  have hwr : continuousRepresentative (concat u v a.property.1 a.property.2) 1 = continuousRepresentative w 0 :=
    (representative_concat_one u v a.property.1 a.property.2 huv).trans hvw
  apply eq_of_representative_eqOn
  intro τ hτ
  by_cases hl : τ ≤ (1 / 2 : ℝ)
  · have hτb : τ ≤ (b : ℝ) := hl.trans hhalf.le
    have hba : (b : ℝ)⁻¹ * τ ≤ a := by
      apply (mul_le_mul_iff_right₀ b.property.1).mp
      rw [← mul_assoc, mul_inv_cancel₀ b.property.1.ne', one_mul, hab]
      exact hl
    have hbτ := H1ConcatContinuity.left_time_mem b.property.1 hτ hτb
    rw [representative_concat_left u _ (by norm_num) (by norm_num) ⟨hτ.1, hl⟩,
      representative_concat_left _ w b.property.1 b.property.2 ⟨hτ.1, hτb⟩,
      representative_concat_left u v a.property.1 a.property.2 ⟨hbτ.1, hba⟩]
    congr 1
    dsimp [a, b, FirstHalfSplits.inner, FirstHalfSplits.outer]
    field_simp
    <;> ring
  · have hr : (1 / 2 : ℝ) ≤ τ := (lt_of_not_ge hl).le
    have hσ := H1ConcatContinuity.right_time_mem (by norm_num : (1 / 2 : ℝ) < 1) hτ hr
    by_cases hm : τ ≤ (b : ℝ)
    · have hσk : rightMap (1 / 2) τ ≤ (k : ℝ) := by
        norm_num [rightMap]
        linarith
      have hbτ := H1ConcatContinuity.left_time_mem b.property.1 hτ hm
      have hba : (a : ℝ) ≤ (b : ℝ)⁻¹ * τ := by
        apply (mul_le_mul_iff_right₀ b.property.1).mp
        rw [← mul_assoc, mul_inv_cancel₀ b.property.1.ne', one_mul, hab]
        exact hr
      rw [representative_concat_right u _ (by norm_num) (by norm_num) hul ⟨hr, hτ.2⟩,
        representative_concat_left v w k.property.1 k.property.2 ⟨hσ.1, hσk⟩,
        representative_concat_left _ w b.property.1 b.property.2 ⟨hτ.1, hm⟩,
        representative_concat_right u v a.property.1 a.property.2 huv ⟨hba, hbτ.2⟩]
      congr 1
      simp only [rightMap_eq, hac]
      dsimp [a, b, k, FirstHalfSplits.inner, FirstHalfSplits.outer, HalfConcatRestriction.tailSplit]
      field_simp [hn.ne', hd.ne', he.ne']
      <;> field_simp [he.ne']
      <;> ring
    · have hτb : (b : ℝ) ≤ τ := (lt_of_not_ge hm).le
      have hkσ : (k : ℝ) ≤ rightMap (1 / 2) τ := by
        norm_num [rightMap]
        linarith
      rw [representative_concat_right u _ (by norm_num) (by norm_num) hul ⟨hr, hτ.2⟩,
        representative_concat_right v w k.property.1 k.property.2 hvw ⟨hkσ, hσ.2⟩,
        representative_concat_right _ w b.property.1 b.property.2 hwr ⟨hτb, hτ.2⟩]
      congr 1
      simp only [rightMap_eq, hkc, hbc]
      dsimp [b, k, FirstHalfSplits.outer, HalfConcatRestriction.tailSplit]
      field_simp [hn.ne', hd.ne', he.ne']
      <;> ring

end
end Finsler.FirstHalfRebracket
