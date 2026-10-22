module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! Numerical incompatibility of a quadratic contribution with a linear budget.
Deriving the contribution from actual ambient lifts remains a topological task. -/

@[expose] public section

namespace Finsler.Growth

theorem quadratic_exceeds_linear (c C a : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (ha : 1 ≤ a) (hLarge : 2 * C / c < a) :
    C * (1 + a) < c * a^2 := by
  have hca : 2 * C < a * c := (div_lt_iff₀ hc).mp hLarge
  have hapos : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hmul : 0 < a * (a * c - 2 * C) := mul_pos hapos (sub_pos.mpr hca)
  nlinarith

theorem bound_of_linear_budget (c C a : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (ha : 1 ≤ a) (hBudget : c * a^2 ≤ C * (1 + a)) :
    a ≤ 2 * C / c := by
  by_contra h
  have := quadratic_exceeds_linear c C a hc hC ha (lt_of_not_ge h)
  exact (not_lt_of_ge hBudget) this

end Finsler.Growth
