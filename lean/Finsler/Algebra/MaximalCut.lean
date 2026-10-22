module

public import Mathlib.Logic.Function.Iterate
public import Lean.Elab.Tactic.Omega

/-! The bounded integer defect attains its maximum, and doubling preserves that
maximum. The domain may be the subtype of positive regular cuts; proving that
the chosen doubling operation stays in that subtype is a separate input. -/

@[expose] public section

namespace Finsler.MaximalCut

theorem exists_maximizer {ι : Type*} [Nonempty ι] (T : ι → ℕ) (M : ℕ)
    (bounded : ∀ a, T a ≤ M) : ∃ a, ∀ b, T b ≤ T a := by
  induction M with
  | zero =>
    obtain ⟨a⟩ := ‹Nonempty ι›
    exact ⟨a, fun b => Nat.le_trans (bounded b) (Nat.zero_le _)⟩
  | succ M ih =>
    by_cases h : ∃ a, T a = M + 1
    · obtain ⟨a, ha⟩ := h
      exact ⟨a, fun b => by rw [ha]; exact bounded b⟩
    · apply ih
      intro a
      have hb := bounded a
      have hne : T a ≠ M + 1 := fun ha => h ⟨a, ha⟩
      omega

theorem iterate_plateau {ι : Type*} (T : ι → ℕ) (double : ι → ι)
    (monotone : ∀ a, T a ≤ T (double a))
    (a : ι) (maximum : ∀ b, T b ≤ T a) (k : ℕ) :
    T (double^[k] a) = T a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    apply Nat.le_antisymm (maximum _)
    rw [← ih]
    exact monotone _

theorem exists_doubling_plateau {ι : Type*} [Nonempty ι]
    (T : ι → ℕ) (double : ι → ι) (M : ℕ)
    (bounded : ∀ a, T a ≤ M) (monotone : ∀ a, T a ≤ T (double a)) :
    ∃ a, ∀ k, T (double^[k] a) = T a := by
  obtain ⟨a, ha⟩ := exists_maximizer T M bounded
  exact ⟨a, iterate_plateau T double monotone a ha⟩

end Finsler.MaximalCut
