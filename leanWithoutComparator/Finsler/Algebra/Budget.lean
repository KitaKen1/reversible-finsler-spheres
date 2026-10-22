module

public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Arithmetic consequences of the actual crossing-rank formulas.
The topological rank formulas are hypotheses, not conclusions of this file. -/

@[expose] public section

namespace Finsler.Budget

/-- The preceding-degree defect is essential in the four-term potential. -/
theorem four_term_change
    (D D' Dprev Dprev' H H' t t' r rprev rcur : ℤ)
    (hD : D' - D = -(r - rcur))
    (hPrev : Dprev' - Dprev = -(r - rprev))
    (hHt : (H' + t') - (H + t) = r - rprev) :
    (D' + Dprev' + H' + t') - (D + Dprev + H + t) = -(r - rcur) := by
  linarith

theorem four_term_nonincrease
    (D D' Dprev Dprev' H H' t t' r rprev rcur : ℤ)
    (hD : D' - D = -(r - rcur))
    (hPrev : Dprev' - Dprev = -(r - rprev))
    (hHt : (H' + t') - (H + t) = r - rprev)
    (hr : rcur ≤ r) :
    D' + Dprev' + H' + t' ≤ D + Dprev + H + t := by
  have := four_term_change D D' Dprev Dprev' H H' t t' r rprev rcur hD hPrev hHt
  linarith

/-- Numerical part of the doubling inequality after subtracting image ranks. -/
theorem doubling_lower_bound (T Tdouble N J Vo Ve V : ℤ)
    (hRank : Tdouble - T = 2 * (N + J) - Vo - Ve + V)
    (hFixed : Ve - J ≤ V) :
    J + (2 * N - Vo) ≤ Tdouble - T := by linarith

theorem doubling_monotone (T Tdouble N J Vo Ve V : ℤ)
    (hRank : Tdouble - T = 2 * (N + J) - Vo - Ve + V)
    (hFixed : Ve - J ≤ V) (hJ : 0 ≤ J) (hOdd : Vo ≤ 2 * N) :
    T ≤ Tdouble := by
  have := doubling_lower_bound T Tdouble N J Vo Ve V hRank hFixed
  linarith

theorem doubling_equality (T Tdouble N J Vo Ve V : ℤ)
    (hRank : Tdouble - T = 2 * (N + J) - Vo - Ve + V)
    (hFixed : Ve - J ≤ V) (hJ : 0 ≤ J) (hOdd : Vo ≤ 2 * N)
    (hEq : Tdouble = T) : J = 0 ∧ Vo = 2 * N := by
  have := doubling_lower_bound T Tdouble N J Vo Ve V hRank hFixed
  constructor <;> linarith

/-- The equality of total odd ranks forces equality at every visible odd label. -/
theorem each_partner_of_sum_eq {ι : Type*} (s : Finset ι) (b h : ι → ℤ)
    (hle : ∀ i ∈ s, h i ≤ b i)
    (hsum : ∑ i ∈ s, (b i - h i) = 0) :
    ∀ i ∈ s, h i = b i := by
  have hn : ∀ i ∈ s, 0 ≤ b i - h i := fun i hi => sub_nonneg.mpr (hle i hi)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hsum
  intro i hi
  have := hz i hi
  linarith

/-- Removing the preceding-degree term leaves a change of r_current-r_previous,
which can be positive even when both ranks are bounded by r. -/
theorem three_term_change
    (D D' H H' t t' r rprev rcur : ℤ)
    (hD : D' - D = -(r - rcur))
    (hHt : (H' + t') - (H + t) = r - rprev) :
    (D' + H' + t') - (D + H + t) = rcur - rprev := by linarith

/-- Kernel-checked certificate for the first finite-search counterexample.
This is a counterexample to the arithmetic simplification, not to the paper. -/
theorem omitted_term_counterexample :
    (0 : ℤ) - 0 = -(1 - 1) ∧
    (0 : ℤ) - 1 = -(1 - 0) ∧
    ((1 : ℤ) + 0) - (0 + 0) = 1 - 0 ∧
    ((0 : ℤ) + 0 + 1 + 0) = (0 + 1 + 0 + 0) ∧
    ((0 : ℤ) + 0 + 0) < (0 + 1 + 0) := by decide

end Finsler.Budget
