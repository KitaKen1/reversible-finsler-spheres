module

public import Finsler.Algebra.Budget

/-! Sum the local crossing estimates before constructing their geometric data.
The exceptional indices, their cost bound and their count are explicit inputs;
the local Morse windows supplying those inputs are not constructed here. -/

@[expose] public section

namespace Finsler.EventBudget

/-- Telescoping turns one-step estimates into a bound on the entire event list. -/
theorem controlled_growth (Φ cost : ℕ → ℤ) (m : ℕ)
    (step : ∀ i, i < m → Φ (i + 1) ≤ Φ i + cost i) :
    Φ m ≤ Φ 0 + ∑ i ∈ Finset.range m, cost i := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hprev := ih (fun i hi => step i (Nat.lt_trans hi (Nat.lt_succ_self m)))
    have hnext := step m (Nat.lt_succ_self m)
    rw [Finset.sum_range_succ]
    linarith

/-- A fixed cost is paid only at the exceptional events. The estimate is
independent of the number of all the other crossings. -/
theorem exceptional_budget (Φ : ℕ → ℤ) (bad : Finset ℕ) (R : ℤ) (m : ℕ)
    (hR : 0 ≤ R)
    (good : ∀ i, i < m → i ∉ bad → Φ (i + 1) ≤ Φ i)
    (exceptional : ∀ i, i < m → i ∈ bad → Φ (i + 1) ≤ Φ i + R) :
    Φ m ≤ Φ 0 + R * (bad.card : ℤ) := by
  classical
  have hsteps : ∀ i, i < m → Φ (i + 1) ≤ Φ i + (if i ∈ bad then R else 0) := by
    intro i hi
    by_cases hb : i ∈ bad
    · simpa [hb] using exceptional i hi hb
    · simpa [hb] using good i hi hb
  have hsum := controlled_growth Φ (fun i => if i ∈ bad then R else 0) m hsteps
  have hcost : (∑ i ∈ Finset.range m, if i ∈ bad then R else 0) =
      (((Finset.range m).filter (fun i => i ∈ bad)).card : ℤ) * R := by
    rw [← Finset.sum_filter]
    simp
  have hcard : ((Finset.range m).filter (fun i => i ∈ bad)).card ≤ bad.card :=
    Finset.card_le_card (fun i hi => (Finset.mem_filter.mp hi).2)
  have hcast : (((Finset.range m).filter (fun i => i ∈ bad)).card : ℤ) ≤ bad.card := by
    exact_mod_cast hcard
  rw [hcost] at hsum
  have hmul := mul_le_mul_of_nonneg_right hcast hR
  nlinarith

/-- A linear bound on the number of exceptional windows gives a linear budget. -/
theorem linear_budget (Φ : ℕ → ℤ) (bad : Finset ℕ) (R : ℤ) (m A B c : ℕ)
    (hR : 0 ≤ R)
    (good : ∀ i, i < m → i ∉ bad → Φ (i + 1) ≤ Φ i)
    (exceptional : ∀ i, i < m → i ∈ bad → Φ (i + 1) ≤ Φ i + R)
    (count : bad.card ≤ A + B * c) :
    Φ m ≤ Φ 0 + R * ((A : ℤ) + (B : ℤ) * (c : ℤ)) := by
  have hbudget := exceptional_budget Φ bad R m hR good exceptional
  have hcast : (bad.card : ℤ) ≤ (A : ℤ) + (B : ℤ) * (c : ℤ) := by exact_mod_cast count
  have hmul := mul_le_mul_of_nonneg_left hcast hR
  linarith

end Finsler.EventBudget
