module

public import Finsler.Loop.NativeSelfCutSegmentClocks
public import Finsler.Loop.ClosedLoopVariableClocks

/-! The actual four-piece rejoining clock: prefix, two pauses at the
cut point, suffix. All formulas include the seams and degenerate cuts. -/
@[expose] public section
namespace Finsler.NativeNearCutClocks
open Finsler.IntervalSobolev Finsler.NativeSelfCutSegmentClocks
open Finsler.ClosedLoopReparametrization
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000
local notation "I" => ClosedInterval

theorem half_cases (t : I) :
    (∃ u : I, t = firstHalf u) ∨ (∃ u : I, t = secondHalf u) := by
  by_cases h : (t : ℝ) ≤ 1 / 2
  · left
    refine ⟨⟨2 * t, by constructor <;> linarith [t.property.1]⟩, ?_⟩
    apply Subtype.ext
    change (t : ℝ) = 2 * t / 2
    ring
  · right
    refine ⟨⟨2 * t - 1, by constructor <;> linarith [t.property.2]⟩, ?_⟩
    apply Subtype.ext
    change (t : ℝ) = (1 + (2 * t - 1)) / 2
    ring

theorem early_first (t : I) : early.val (firstHalf t) = t := by
  apply Subtype.ext
  change min (2 * ((t : ℝ) / 2)) 1 = t
  rw [show 2 * ((t : ℝ) / 2) = t by ring, min_eq_left t.property.2]

theorem early_second (t : I) : early.val (secondHalf t) = 1 := by
  apply Subtype.ext
  change min (2 * ((1 + (t : ℝ)) / 2)) 1 = 1
  exact min_eq_right (by linarith [t.property.1])

theorem late_first (t : I) : late.val (firstHalf t) = 0 := by
  apply Subtype.ext
  change max (2 * ((t : ℝ) / 2) - 1) 0 = 0
  exact max_eq_right (by linarith [t.property.2])

theorem late_second (t : I) : late.val (secondHalf t) = t := by
  apply Subtype.ext
  change max (2 * ((1 + (t : ℝ)) / 2) - 1) 0 = t
  rw [show 2 * ((1 + (t : ℝ)) / 2) - 1 = t by ring, max_eq_left t.property.1]

def splice (c t : I) : I :=
  mix (unitInterval.symm c) (early.val (early.val t)) (late.val (late.val t))

def clock (c : I) : clocks :=
  ⟨⟨splice c, by unfold splice mix early late; fun_prop⟩, by
    constructor <;> apply Subtype.ext <;> simp [splice, mix, early, late]
    norm_num⟩

theorem continuous_clock : Continuous clock := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : I × I => splice z.1 z.2)
  unfold splice mix early late
  fun_prop

theorem first_first (c t : I) :
    splice c (firstHalf (firstHalf t)) = prefixTime c t := by
  unfold splice
  rw [early_first, early_first, late_first, late.property.1]
  apply Subtype.ext
  change (1 - (1 - (c : ℝ))) * t + (1 - c) * 0 = c * t
  ring

theorem first_second (c t : I) : splice c (firstHalf (secondHalf t)) = c := by
  unfold splice
  rw [early_first, early_second, late_first, late.property.1]
  apply Subtype.ext
  change (1 - (1 - (c : ℝ))) * 1 + (1 - c) * 0 = c
  ring

theorem second_first (c t : I) : splice c (secondHalf (firstHalf t)) = c := by
  unfold splice
  rw [early_second, early.property.2, late_second, late_first]
  apply Subtype.ext
  change (1 - (1 - (c : ℝ))) * 1 + (1 - c) * 0 = c
  ring

theorem second_second (c t : I) :
    splice c (secondHalf (secondHalf t)) = suffixTime c t := by
  unfold splice
  rw [early_second, early.property.2, late_second, late_second]
  apply Subtype.ext
  change (1 - (1 - (c : ℝ))) * 1 + (1 - c) * t = c + (1 - c) * t
  ring

end
end Finsler.NativeNearCutClocks
