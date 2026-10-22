module

public import Mathlib.Algebra.Group.Hom.Basic

/-! Algebraic consequences of natural exact Gysin diagrams.
Groups, maps, exactness and the stabilized ordinary image are explicit hypotheses.
No assertion that the Finsler sublevels supply those hypotheses is made here. -/

@[expose] public section

namespace Finsler.Gysin

section Step

variable {Gprev Gcur Oprev Ocur Va Vb Wb Pa Pb Qb : Type*}
  [AddCommGroup Gprev] [AddCommGroup Gcur]
  [AddCommGroup Oprev] [AddCommGroup Ocur]
  [AddCommGroup Va] [AddCommGroup Vb] [AddCommGroup Wb]
  [AddCommGroup Pa] [AddCommGroup Pb] [AddCommGroup Qb]

/-- K_b^q ⊆ w K_a^(q-1), with the transfer correction written out.
`ordinary_image` is the precise ordinary-image stabilization needed by the proof. -/
theorem kernel_descent
    (w : Gprev →+ Gcur) (forg : Gcur →+ Ocur) (transfer : Oprev →+ Gprev)
    (resPrevA : Gprev →+ Va) (resPrevB : Gprev →+ Vb) (resCurB : Gcur →+ Wb)
    (resOrdA : Oprev →+ Pa) (resOrdCurB : Ocur →+ Qb)
    (restrictBtoA : Vb →+ Va) (restrictOrdBtoA : Pb →+ Pa)
    (wB : Vb →+ Wb) (forgB : Wb →+ Qb)
    (transferA : Pa →+ Va) (transferB : Pb →+ Vb)
    (global_exact : ∀ x, forg x = 0 → ∃ y, w y = x)
    (finite_exact : ∀ y, wB y = 0 → ∃ z, transferB z = y)
    (ordinary_injective : Function.Injective resOrdCurB)
    (ordinary_image : ∀ z : Pb, ∃ zGlobal : Oprev,
      resOrdA zGlobal = restrictOrdBtoA z)
    (nat_forg : ∀ x, resOrdCurB (forg x) = forgB (resCurB x))
    (nat_w : ∀ y, wB (resPrevB y) = resCurB (w y))
    (nat_restriction : ∀ y, restrictBtoA (resPrevB y) = resPrevA y)
    (nat_transfer : ∀ z, restrictBtoA (transferB z) =
      transferA (restrictOrdBtoA z))
    (nat_global_transfer : ∀ z, resPrevA (transfer z) = transferA (resOrdA z))
    (w_transfer : ∀ z, w (transfer z) = 0)
    (x : Gcur) (hx : resCurB x = 0) :
    ∃ y : Gprev, w y = x ∧ resPrevA y = 0 := by
  have hforg : forg x = 0 := ordinary_injective (by rw [nat_forg, hx, map_zero, map_zero])
  obtain ⟨y, hy⟩ := global_exact x hforg
  have hyb : wB (resPrevB y) = 0 := by rw [nat_w, hy, hx]
  obtain ⟨z, hz⟩ := finite_exact (resPrevB y) hyb
  obtain ⟨zGlobal, hzGlobal⟩ := ordinary_image z
  refine ⟨y - transfer zGlobal, ?_, ?_⟩
  · rw [map_sub, hy, w_transfer, sub_zero]
  · rw [map_sub, nat_global_transfer, hzGlobal]
    have hya : resPrevA y = transferA (restrictOrdBtoA z) := by
      rw [← nat_restriction, ← hz, nat_transfer]
    rw [hya, sub_self]

/-- A finite transfer whose ordinary source stabilizes to a vanishing global
restriction vanishes at the lower cut. This is the downward step for ZERO. -/
theorem zero_descent
    (resBtoA : Vb →+ Va) (wB : Vb →+ Wb)
    (transferB : Pb →+ Vb) (transferA : Pa →+ Va)
    (resOrdA : Oprev →+ Pa) (resOrdBtoA : Pb →+ Pa)
    (finite_exact : ∀ y, wB y = 0 → ∃ z, transferB z = y)
    (ordinary_image : ∀ z : Pb, ∃ zGlobal : Oprev, resOrdA zGlobal = resOrdBtoA z)
    (ordinary_zero : ∀ zGlobal : Oprev, resOrdA zGlobal = 0)
    (nat_transfer : ∀ z, resBtoA (transferB z) = transferA (resOrdBtoA z))
    (y : Vb) (hy : wB y = 0) : resBtoA y = 0 := by
  obtain ⟨z, hz⟩ := finite_exact y hy
  obtain ⟨zGlobal, hzGlobal⟩ := ordinary_image z
  rw [← hz, nat_transfer, ← hzGlobal, ordinary_zero, map_zero]

end Step

section Graded

variable {V : ℕ → Type*} [∀ n, AddCommGroup (V n)]

/-- A length-n word in degree-raising maps, with no subtraction of natural degrees. -/
def word (w : ∀ n, V n →+ V (n + 1)) : ∀ n, V 0 → V n
  | 0 => id
  | n + 1 => fun x => w n (word w n x)

/-- Iterating kernel descent supplies an actual lift through the complete word. -/
theorem word_lift (w : ∀ n, V n →+ V (n + 1)) (K : ∀ n, Set (V n))
    (N : ℕ) (descent : ∀ n, n < N → ∀ (x : V (n + 1)), x ∈ K (n + 1) →
      ∃ y : V n, y ∈ K n ∧ w n y = x)
    (n : ℕ) (hn : n ≤ N) (x : V n) (hx : x ∈ K n) :
    ∃ y : V 0, y ∈ K 0 ∧ word w n y = x := by
  induction n with
  | zero => exact ⟨x, hx, rfl⟩
  | succ n ih =>
    obtain ⟨z, hz, hzx⟩ := descent n (Nat.lt_of_succ_le hn) x hx
    obtain ⟨y, hy, hyz⟩ := ih (Nat.le_of_succ_le hn) z hz
    exact ⟨y, hy, by simp only [word, hyz, hzx]⟩

/-- Nilpotence closes the iterated kernel descent. For the paper's application,
K₀ is the full group, K₁ is the kernel at a, and K_N is the kernel at a+(N-1)D. -/
theorem kernel_zero_of_nilpotent
    (w : ∀ n, V n →+ V (n + 1)) (K : ∀ n, Set (V n))
    (N : ℕ) (descent : ∀ n, n < N → ∀ (x : V (n + 1)), x ∈ K (n + 1) →
      ∃ y : V n, y ∈ K n ∧ w n y = x)
    (nilpotent : ∀ y : V 0, word w N y = 0)
    (x : V N) (hx : x ∈ K N) : x = 0 := by
  obtain ⟨y, _, hy⟩ := word_lift w K N descent N (Nat.le_refl N) x hx
  rw [← hy, nilpotent]

end Graded

end Finsler.Gysin
