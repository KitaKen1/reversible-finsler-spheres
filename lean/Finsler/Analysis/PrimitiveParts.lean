module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Primitives from parts. If a finite monotone family of break points runs from a to b and on
every part the function differs from its value at the left break point by the integral of W, and
W is integrable on every part, then the function is a + ∫ W on the whole interval. -/

@[expose] public section

namespace Finsler.PrimitiveParts

open Set MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Primitive identity from the identities on the parts of a monotone partition. -/
theorem eq_add_integral_of_parts {V W : ℝ → E} {x : ℕ → ℝ} :
    ∀ m : ℕ, (∀ j < m, x j ≤ x (j + 1)) →
      (∀ j < m, ∀ t ∈ Icc (x j) (x (j + 1)), V t - V (x j) = ∫ s in x j..t, W s) →
      (∀ j < m, IntervalIntegrable W volume (x j) (x (j + 1))) →
      ∀ t ∈ Icc (x 0) (x m), V t - V (x 0) = ∫ s in x 0..t, W s
  | 0, _, _, _, t, ht => by
    have h : t = x 0 := le_antisymm ht.2 ht.1
    subst h
    simp
  | m + 1, hmono, hpart, hint, t, ht => by
    have hmono' : ∀ j < m, x j ≤ x (j + 1) := fun j hj => hmono j (Nat.lt_succ_of_lt hj)
    have hpart' := fun j (hj : j < m) => hpart j (Nat.lt_succ_of_lt hj)
    have hint' := fun j (hj : j < m) => hint j (Nat.lt_succ_of_lt hj)
    have hIH := eq_add_integral_of_parts m hmono' hpart' hint'
    have hx0m : x 0 ≤ x m := by
      have : ∀ j ≤ m, x 0 ≤ x j := by
        intro j hj
        induction j with
        | zero => exact le_rfl
        | succ i ih => exact (ih (Nat.le_of_succ_le hj)).trans (hmono' i (Nat.lt_of_succ_le hj))
      exact this m le_rfl
    rcases le_or_gt t (x m) with htm | htm
    · exact hIH t ⟨ht.1, htm⟩
    · have hlast := hpart m (Nat.lt_succ_self m) t ⟨htm.le, ht.2⟩
      have hprev := hIH (x m) ⟨hx0m, le_rfl⟩
      have hI0 : IntervalIntegrable W volume (x 0) (x m) := by
        have h := IntervalIntegrable.trans_iterate (a := x) (n := m) (f := W) (μ := volume) hint'
        exact h
      have hI1 : IntervalIntegrable W volume (x m) t :=
        (hint m (Nat.lt_succ_self m)).mono_set (by
          rw [uIcc_of_le htm.le, uIcc_of_le (hmono m (Nat.lt_succ_self m))]
          exact Icc_subset_Icc le_rfl ht.2)
      rw [← intervalIntegral.integral_add_adjacent_intervals hI0 hI1, ← hprev, ← hlast]
      abel

end

end Finsler.PrimitiveParts
