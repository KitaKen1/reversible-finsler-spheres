module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-! The characteristic-two recurrence used in the global equivariant calculation.
This file proves polynomial identities; it does not construct equivariant cohomology. -/

@[expose] public section

namespace Finsler.Recurrence

variable {R : Type*} [CommRing R]

/-- Consecutive values of A₀ = 1, A₁ = w, Aᵢ₊₂ = w Aᵢ₊₁ + U Aᵢ. -/
def pair (w U : R) : ℕ → R × R
  | 0 => (1, w)
  | n + 1 => ((pair w U n).2, w * (pair w U n).2 + U * (pair w U n).1)

def A (w U : R) (n : ℕ) : R := (pair w U n).1

@[simp] theorem A_zero (w U : R) : A w U 0 = 1 := rfl
@[simp] theorem A_one (w U : R) : A w U 1 = w := rfl

theorem pair_snd (w U : R) (n : ℕ) : (pair w U n).2 = A w U (n + 1) := rfl

theorem A_succ_succ (w U : R) (n : ℕ) :
    A w U (n + 2) = w * A w U (n + 1) + U * A w U n := rfl

variable [CharP R 2]

private theorem determinant_step (w U a b : R) :
    (w * b + U * a)^2 + b * (w * (w * b + U * a) + U * b) =
      U * (b^2 + a * (w * b + U * a)) := by
  have ht : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination (w * b * (w * b + U * a)) * ht

/-- Cassini identity, with indices shifted to avoid truncated natural subtraction. -/
theorem cassini (w U : R) (n : ℕ) :
    A w U (n + 1)^2 + A w U n * A w U (n + 2) = U^(n + 1) := by
  have h : ∀ n, (pair w U n).2^2 + (pair w U n).1 *
      (w * (pair w U n).2 + U * (pair w U n).1) = U^(n + 1) := by
    intro n
    induction n with
    | zero =>
      simp only [pair, one_mul]
      have ht : (2 : R) = 0 := CharTwo.two_eq_zero
      linear_combination w^2 * ht
    | succ n ih =>
      simp only [pair]
      rw [determinant_step, ih, pow_succ]
      ring
  rw [A_succ_succ]
  exact h n

omit [CharP R 2] in
@[simp] theorem A_two (w U : R) : A w U 2 = w^2 + U := by
  rw [show 2 = 0 + 2 from rfl, A_succ_succ]
  simp [pow_two]

@[simp] theorem A_three (w U : R) : A w U 3 = w^3 := by
  rw [show 3 = 1 + 2 from rfl, A_succ_succ, A_two, A_one]
  have ht : (2 : R) = 0 := CharTwo.two_eq_zero
  linear_combination (w * U) * ht

end Finsler.Recurrence
