module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Pointwise scalar estimate in the arc-length normalization.
This does not assert change of variables or strong H¹ continuity. -/

@[expose] public section

namespace Finsler.Normalization

theorem cleared_identity (u s : ℝ) :
    ((1 - u) * s^2 + u * s) * (1 - u + u * s) - s^2 =
      u * (1 - u) * s * (s - 1)^2 := by ring

theorem pointwise_energy_bound (u s : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hs : 0 ≤ s) :
    s^2 / (1 - u + u * s) ≤ (1 - u) * s^2 + u * s := by
  have h1 : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have hd : 0 ≤ 1 - u + u * s := by positivity
  by_cases hz : 1 - u + u * s = 0
  · rw [hz, div_zero]
    positivity
  · have hdpos : 0 < 1 - u + u * s := lt_of_le_of_ne hd (Ne.symm hz)
    apply (div_le_iff₀ hdpos).mpr
    have hprod : 0 ≤ u * (1 - u) * s * (s - 1)^2 := by positivity
    have hid := cleared_identity u s
    linarith

end Finsler.Normalization
