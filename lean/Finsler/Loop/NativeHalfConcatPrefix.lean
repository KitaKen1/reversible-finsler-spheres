module

public import Finsler.Topology.HalfConcatRestriction
public import Finsler.Loop.NativeSelfCutSegmentClocks

/-! Exact complementary half-concat restriction. Cutting the actual
half concatenation at (1+t)/2 gives the whole first path followed by
the prefix of the second, with its REAL split1/(1+t). The t=0 seam is
excluded from this positive-split formula, not silently collapsed. -/
@[expose] public section
namespace Finsler.NativeHalfConcatPrefix
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevAffine Finsler.SobolevConcat Finsler.VariableJoinContinuity
open Finsler.NativeSelfCutSegmentClocks Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

abbrev Times := Ioc (0 : ℝ) 1

def pointTime (t : Times) : ClosedInterval := ⟨t, t.property.1.le, t.property.2⟩

def frontSplit (t : Times) : Splits := ⟨1 / (1 + (t : ℝ)), by
  have hd : 0 < 1 + (t : ℝ) := by linarith [t.property.1]
  exact ⟨div_pos zero_lt_one hd, (div_lt_one hd).mpr (by linarith [t.property.1])⟩⟩

theorem continuous_frontSplit : Continuous frontSplit :=
  (continuous_const.div (continuous_const.add continuous_subtype_val)
    (fun t => by have h := t.property.1; dsimp; linarith)).subtype_mk _

theorem prefix_path {n : ℕ} (u v : Space n) (t : Times)
    (hm : continuousRepresentative u 1 = continuousRepresentative v 0) :
    restrict (concat u v (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)) (by norm_num)
      (secondHalf (pointTime t)).property (secondHalf (pointTime t)).property.1 =
      concat u (restrict v (by norm_num) (pointTime t).property (pointTime t).property.1)
        (frontSplit t).property.1 (frontSplit t).property.2 := by
  apply eq_of_representative_eqOn
  intro τ hτ
  rw [representative_restrict _ _ _ _ hτ]
  have hd : 0 < 1 + (t : ℝ) := by linarith [t.property.1]
  have ht : aff 0 (secondHalf (pointTime t)) τ ∈ Icc (0 : ℝ) 1 :=
    aff_mem_Icc (by norm_num) (secondHalf (pointTime t)).property hτ
  have hms : continuousRepresentative u 1 = continuousRepresentative
      (restrict v (by norm_num) (pointTime t).property (pointTime t).property.1) 0 :=
    hm.trans (representative_restrict_zero _ _ _ _).symm
  by_cases hle : τ ≤ (frontSplit t : ℝ)
  · have hscaled : τ * (1 + (t : ℝ)) ≤ 1 := (le_div_iff₀ hd).mp hle
    have hhalf : aff 0 (secondHalf (pointTime t)) τ ∈ Icc (0 : ℝ) (1 / 2) := by
      refine ⟨ht.1, ?_⟩
      change 0 + ((1 + (t : ℝ)) / 2 - 0) * τ ≤ 1 / 2
      nlinarith
    rw [representative_concat_left _ _ (by norm_num) (by norm_num) hhalf,
      representative_concat_left _ _ (frontSplit t).property.1 (frontSplit t).property.2 ⟨hτ.1, hle⟩]
    congr 1
    dsimp [aff, secondHalf, pointTime, frontSplit]
    field_simp
    ring
  · have hge : (frontSplit t : ℝ) ≤ τ := (lt_of_not_ge hle).le
    have hscaled : 1 ≤ τ * (1 + (t : ℝ)) := (div_le_iff₀ hd).mp hge
    have hhalf : aff 0 (secondHalf (pointTime t)) τ ∈ Icc (1 / 2 : ℝ) 1 := by
      refine ⟨?_, ht.2⟩
      change 1 / 2 ≤ 0 + ((1 + (t : ℝ)) / 2 - 0) * τ
      nlinarith
    rw [representative_concat_right _ _ (by norm_num) (by norm_num) hm hhalf,
      representative_concat_right _ _ (frontSplit t).property.1 (frontSplit t).property.2 hms ⟨hge, hτ.2⟩,
      representative_restrict _ _ _ _ (H1ConcatContinuity.right_time_mem (frontSplit t).property.2 hτ hge)]
    congr 1
    dsimp [aff, rightMap, secondHalf, pointTime, frontSplit]
    field_simp [t.property.1.ne', hd.ne']
    ring

end
end Finsler.NativeHalfConcatPrefix
