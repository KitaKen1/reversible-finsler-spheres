module

public import Finsler.Topology.Gysin

/-! The complete finite ZERO iteration, with its natural diagrams as explicit inputs.
The degree-i lower cut is a+iD. The terminal degree N has cut a+ND.
Global nilpotence has length N+1, exactly the paper's (n-1) cut shifts for w^n=0. -/

@[expose] public section

namespace Finsler.Gysin

private theorem descend_to_zero (P : ℕ → Prop) (N : ℕ) (hN : P N)
    (step : ∀ i, i < N → P (i + 1) → P i) : P 0 := by
  induction N with
  | zero => exact hN
  | succ N ih =>
    apply ih (step N (Nat.lt_succ_self N) hN)
    intro i hi
    exact step i (Nat.lt_trans hi (Nat.lt_succ_self N))

section

variable {V O D L P Q : ℕ → Type*}
  [∀ n, AddCommGroup (V n)] [∀ n, AddCommGroup (O n)]
  [∀ n, AddCommGroup (D n)] [∀ n, AddCommGroup (L n)]
  [∀ n, AddCommGroup (P n)] [∀ n, AddCommGroup (Q n)]

/-- Global w^(N+1)=0 and vanishing ordinary restrictions in N+1 degrees imply
the lower equivariant restriction is zero. The upper-to-lower stabilization is
required only at the N cuts actually traversed. -/
theorem zero_of_nilpotent_word
    (w : ∀ n, V n →+ V (n + 1))
    (globalTransfer : ∀ n, O n →+ V n)
    (resLower : ∀ n, V n →+ D n) (resUpper : ∀ n, V n →+ L n)
    (wUpper : ∀ n, L n →+ D (n + 1))
    (cutRestriction : ∀ n, L n →+ D n)
    (transferUpper : ∀ n, P n →+ L n) (transferLower : ∀ n, Q n →+ D n)
    (ordinaryLower : ∀ n, O n →+ Q n)
    (ordinaryUpperToLower : ∀ n, P n →+ Q n)
    (global_exact : ∀ n (y : V n), w n y = 0 →
      ∃ z : O n, globalTransfer n z = y)
    (finite_exact : ∀ n (y : L n), wUpper n y = 0 →
      ∃ z : P n, transferUpper n z = y)
    (nat_global_transfer : ∀ n z, resLower n (globalTransfer n z) =
      transferLower n (ordinaryLower n z))
    (nat_transfer : ∀ n z, cutRestriction n (transferUpper n z) =
      transferLower n (ordinaryUpperToLower n z))
    (nat_w : ∀ n y, wUpper n (resUpper n y) = resLower (n + 1) (w n y))
    (nat_cut : ∀ n y, cutRestriction n (resUpper n y) = resLower n y)
    (N : ℕ)
    (ordinary_image : ∀ n, n < N → ∀ z : P n, ∃ zGlobal : O n,
      ordinaryLower n zGlobal = ordinaryUpperToLower n z)
    (ordinary_zero : ∀ n, n ≤ N → ∀ z : O n, ordinaryLower n z = 0)
    (x : V 0) (nilpotent : word w (N + 1) x = 0) : resLower 0 x = 0 := by
  have hw : w N (word w N x) = 0 := nilpotent
  obtain ⟨z, hz⟩ := global_exact N (word w N x) hw
  have hTop : resLower N (word w N x) = 0 := by
    rw [← hz, nat_global_transfer, ordinary_zero N (Nat.le_refl N), map_zero]
  have hBase := descend_to_zero (fun n => resLower n (word w n x) = 0) N hTop
    (fun n hn hNext => by
      have hwLocal : wUpper n (resUpper n (word w n x)) = 0 := by
        rw [nat_w]
        exact hNext
      have hCut := zero_descent
        (cutRestriction n) (wUpper n) (transferUpper n) (transferLower n)
        (ordinaryLower n) (ordinaryUpperToLower n)
        (finite_exact n) (ordinary_image n hn)
        (ordinary_zero n (Nat.le_of_lt hn)) (nat_transfer n)
        (resUpper n (word w n x)) hwLocal
      rw [nat_cut] at hCut
      exact hCut)
  exact hBase

end

end Finsler.Gysin
