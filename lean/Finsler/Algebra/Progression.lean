module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith

/-! Arithmetic for the odd bottom degrees in the final contradiction.
The explicit floor witness avoids searching over degrees. No regular-cut or
cohomology assumption is used; those remain separate geometric inputs. -/

@[expose] public section

namespace Finsler.Progression

/-- An interval wider than one positive step contains a progression member.
The witness is exactly floor((L-offset)/step)+1. -/
theorem exists_member (L R offset step : ℝ) (hstep : 0 < step)
    (hL : offset ≤ L) (hwidth : step < R - L) :
    ∃ t : ℕ, L < offset + step * (t : ℝ) ∧ offset + step * (t : ℝ) < R := by
  let x := (L - offset) / step
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hL) hstep.le
  have hlo := Nat.lt_floor_add_one x
  have hhi := Nat.floor_le hx
  have hlo' := (div_lt_iff₀ hstep).mp hlo
  have hhi' := (le_div_iff₀ hstep).mp hhi
  refine ⟨Nat.floor x + 1, ?_, ?_⟩
  · simp only [Nat.cast_add, Nat.cast_one]
    dsimp [x] at hlo'
    nlinarith
  · simp only [Nat.cast_add, Nat.cast_one]
    dsimp [x] at hhi'
    nlinarith

/-- Both the degree window and a prescribed lower-degree threshold fit inside
one sufficiently large doubling of a positive interval. -/
theorem exists_odd_degree (α u v C d threshold : ℝ)
    (hα : 0 < α) (hu : 0 < u) (huv : u < v) (hd : 0 < d) :
    ∃ k t : ℕ, 1 ≤ k ∧ threshold < (4 * (t : ℝ) + 1) * d ∧
      α * 2 ^ k * u + C < (4 * (t : ℝ) + 1) * d ∧
      (4 * (t : ℝ) + 1) * d < α * 2 ^ k * v - C := by
  let bound := max 1 (max ((2 * C + 4 * d) / (α * (v - u)))
    ((max threshold d - C) / (α * u)))
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt bound (by norm_num : (1 : ℝ) < 2)
  have hOne : (1 : ℝ) < 2 ^ k := lt_of_le_of_lt (le_max_left _ _) hk
  have hkOne : 1 ≤ k := by
    cases k with
    | zero => norm_num at hOne
    | succ k => exact Nat.succ_le_succ (Nat.zero_le _)
  have hWidth : (2 * C + 4 * d) / (α * (v - u)) < 2 ^ k :=
    lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hBottom : (max threshold d - C) / (α * u) < 2 ^ k :=
    lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  have hWidth' := (div_lt_iff₀ (mul_pos hα (sub_pos.mpr huv))).mp hWidth
  have hBottom' := (div_lt_iff₀ (mul_pos hα hu)).mp hBottom
  have hThreshold : threshold < α * 2 ^ k * u + C := by
    have := le_max_left threshold d
    nlinarith
  have hStart : d ≤ α * 2 ^ k * u + C := by
    have := le_max_right threshold d
    nlinarith
  have hGap : 4 * d < (α * 2 ^ k * v - C) - (α * 2 ^ k * u + C) := by
    nlinarith
  obtain ⟨t, htL, htR⟩ := exists_member _ _ d (4 * d) (by linarith) hStart hGap
  refine ⟨k, t, hkOne, ?_, ?_, ?_⟩ <;> nlinarith

end Finsler.Progression
