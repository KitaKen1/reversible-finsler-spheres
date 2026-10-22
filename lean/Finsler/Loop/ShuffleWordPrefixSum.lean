module

public import Finsler.Loop.ShuffleWords

/-! If all words without an initial horizontal block vanish, the
actual full finite shuffle sum reduces to the shorter shuffle sum. -/

@[expose] public section
namespace Finsler.ShuffleWordPrefixSum

open Finsler.ShuffleWords
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem sum_prefix {M : Type*} [AddCommMonoid M] (a p q : ℕ) (f : List Bool → M)
    (hzero : ∀ w, w.take a ≠ List.replicate a false → f w = 0) :
    ∑ w ∈ words (a + p) q, f w =
      ∑ w ∈ words p q, f (List.replicate a false ++ w) := by
  induction a generalizing p q f with
  | zero => simp
  | succ a ih =>
    have hfalse : ∀ w, w.take a ≠ List.replicate a false → f (false :: w) = 0 := by
      intro w hw
      apply hzero
      simp only [List.take_succ_cons, List.replicate_succ]
      intro he
      exact hw (List.cons.inj he).2
    have htrue : ∀ w, f (true :: w) = 0 := by
      intro w
      apply hzero
      simp only [List.take_succ_cons, List.replicate_succ]
      intro he
      have hb := (List.cons.inj he).1
      cases hb
    rw [Nat.succ_add]
    cases q with
    | zero =>
      rw [sum_succ_zero]
      simpa only [List.replicate_succ, List.cons_append] using ih p 0 (fun w => f (false :: w)) hfalse
    | succ q =>
      rw [sum_succ_succ]
      have hz : (∑ w ∈ words ((a + p) + 1) q, f (true :: w)) = 0 := by
        apply Finset.sum_eq_zero
        intro w _
        exact htrue w
      rw [hz, add_zero]
      simpa only [List.replicate_succ, List.cons_append] using ih p (q + 1) (fun w => f (false :: w)) hfalse

end Finsler.ShuffleWordPrefixSum
