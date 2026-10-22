module

public import Mathlib.Algebra.BigOperators.Fin

/-! Finite telescoping for additive path evaluations. This uses every
adjacent interval and both endpoints; no monotonicity or omitted terms
are hidden in the combinatorial sum. -/
@[expose] public section
namespace Finsler.FiniteClockTelescope
open scoped BigOperators
set_option autoImplicit false

theorem adjacent_differences {A : Type*} [AddCommGroup A] (N : ℕ) (F : Fin (N + 1) → A) :
    (∑ i : Fin N, (F i.succ - F i.castSucc)) = F (Fin.last N) - F 0 := by
  rw [Finset.sum_sub_distrib]
  apply sub_eq_sub_iff_add_eq_add.mpr
  have h := (Fin.sum_univ_succ F).symm.trans (Fin.sum_univ_castSucc F)
  simpa only [add_comm] using h

theorem additive_paths {A C : Type*} [AddCommGroup A] (E : C → C → A)
    (hE : ∀ a b c, E a c = E a b + E b c) (N : ℕ) (a : Fin (N + 1) → C) :
    E (a 0) (a (Fin.last N)) = ∑ i : Fin N, E (a i.castSucc) (a i.succ) := by
  have hz : E (a 0) (a 0) = 0 := by
    have h := hE (a 0) (a 0) (a 0)
    exact (add_left_cancel (show E (a 0) (a 0) + E (a 0) (a 0) = E (a 0) (a 0) + 0 by
      simpa only [add_zero] using h.symm))
  have hi (i : Fin N) : E (a i.castSucc) (a i.succ) = E (a 0) (a i.succ) - E (a 0) (a i.castSucc) := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [add_comm] using (hE (a 0) (a i.castSucc) (a i.succ)).symm
  simp_rw [hi]
  rw [adjacent_differences N (fun i => E (a 0) (a i)), hz, sub_zero]

end Finsler.FiniteClockTelescope
