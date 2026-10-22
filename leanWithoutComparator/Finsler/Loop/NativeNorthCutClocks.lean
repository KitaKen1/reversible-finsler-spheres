module

public import Finsler.Loop.NativeNorthOrderedCharts

/-! ACTUAL chronological cut-time breakpoints for each northern
rotation quarter. There are13 segments: the two partial SAME-leg
pieces and11 full intervening quarters. The two distinct northern
quarters are always segments4 and8. All original clock widths remain. -/
@[expose] public section
namespace Finsler.NativeNorthCutClocks
open CategoryTheory Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.MeridianTripleQuarterClocks
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

def targetEnds (k : Fin 3) : Fin 12 → ℝ :=
  match k with
  | 0 => ![1/16, 1/8, 3/16, 1/4, 5/16, 3/8, 7/16, 1/2, 5/8, 3/4, 7/8, 1]
  | 1 => ![5/16, 3/8, 7/16, 1/2, 5/8, 3/4, 7/8, 1, 17/16, 9/8, 19/16, 5/4]
  | 2 => ![5/8, 3/4, 7/8, 1, 17/16, 9/8, 19/16, 5/4, 21/16, 11/8, 23/16, 3/2]

def breakValue (k : Fin 3) (s : ClosedInterval) : Fin 14 → ℝ :=
  ![0, targetEnds k 0 - clock k 0 s, targetEnds k 1 - clock k 0 s,
    targetEnds k 2 - clock k 0 s, targetEnds k 3 - clock k 0 s,
    targetEnds k 4 - clock k 0 s, targetEnds k 5 - clock k 0 s,
    targetEnds k 6 - clock k 0 s, targetEnds k 7 - clock k 0 s,
    targetEnds k 8 - clock k 0 s, targetEnds k 9 - clock k 0 s,
    targetEnds k 10 - clock k 0 s, targetEnds k 11 - clock k 0 s, 1]

theorem break_mem (k : Fin 3) (j : Fin 14) (s : ClosedInterval) : 0 ≤ breakValue k s j ∧ breakValue k s j ≤ 1 := by
  fin_cases k <;> fin_cases j <;> norm_num [breakValue, targetEnds, clock, localTime] <;>
    constructor <;> linarith [s.property.1, s.property.2]

def breakTime (k : Fin 3) (j : Fin 14) (s : ClosedInterval) : ClosedInterval := ⟨breakValue k s j, break_mem k j s⟩

theorem break_sorted (k : Fin 3) (j : Fin 13) (s : ClosedInterval) :
    (breakTime k j.castSucc s : ℝ) ≤ (breakTime k j.succ s : ℝ) := by
  fin_cases k <;> fin_cases j <;> norm_num [breakTime, breakValue, targetEnds, clock, localTime] <;>
    linarith [s.property.1, s.property.2]

theorem break_zero (k : Fin 3) (s : ClosedInterval) : breakTime k 0 s = 0 := by apply Subtype.ext; rfl
theorem break_one (k : Fin 3) (s : ClosedInterval) : breakTime k 13 s = 1 := by apply Subtype.ext; rfl

theorem continuous_break (k : Fin 3) (j : Fin 14) : Continuous (breakTime k j) := by
  have hc : Continuous (fun s : ClosedInterval => breakValue k s j) := by
    fin_cases k <;> fin_cases j <;> dsimp [breakValue, targetEnds, clock, localTime] <;> fun_prop
  exact hc.subtype_mk _

def breakClock {n : ℕ} (P : Sphere n) (k : Fin 3) (j : Fin 14) : NativeGlobalTimeSquare.rotationDomain P ⟶ TopCat.I :=
  TopCat.ofHom ⟨fun z => ULift.up (breakTime k j z.1), by
    have hc : Continuous (fun z : NativeGlobalTimeSquare.rotationDomain P => breakTime k j z.1) :=
      (continuous_break k j).comp continuous_fst
    fun_prop⟩

end
end Finsler.NativeNorthCutClocks
