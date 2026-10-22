module

public import Finsler.Topology.FilteredGysin
public import Lean.Elab.Tactic.Omega

/-! The paper's complete detection band for an abstract natural Gysin system.
Ordinary resonance, stabilized ordinary images, and global w-nilpotence are
explicit inputs. These have not yet been constructed for Finsler sublevels. -/

@[expose] public section

namespace Finsler.FilteredGysin

universe u

variable {AG BG : ℕ → Type u} {A B : ℝ → ℕ → Type u}
  [∀ q, AddCommGroup (AG q)] [∀ q, AddCommGroup (BG q)]
  [∀ a q, AddCommGroup (A a q)] [∀ a q, AddCommGroup (B a q)]

variable (s : Data AG BG A B)

/-- The final restriction is at a. Starting N cut shifts earlier produces the
exact margin C_H+αND, rather than paying that shift a second time. -/
theorem detection_injective (α D C a : ℝ) (hD : 0 ≤ D) (N j : ℕ)
    (image : ∀ a b (hgap : a + D ≤ b), ∀ q z, ∃ zGlobal,
      s.resA a q zGlobal = s.cutA a b (by linarith) q z)
    (ordinary : ∀ c q, N + 3 ≤ q → (q : ℝ) < α * c - C →
      Function.Injective (s.resA c q))
    (nilpotent : ∀ lo (x : BG lo),
      Finsler.Gysin.word (fun i => s.w (lo + i)) (N + 1) x = 0)
    (hjHigh : 2 * (N + 1) + 1 ≤ j)
    (hj : (j : ℝ) < α * a - (C + α * (N : ℝ) * D)) :
    Function.Injective (s.resB a j) := by
  let lo := j - (N + 1)
  have hdegree : lo + N + 1 = j := by dsimp [lo]; omega
  have hOrd : ∀ i, i ≤ N →
      Function.Injective (s.resA (a - (N : ℝ) * D) (lo + i + 1)) := by
    intro i hi
    have hlow : N + 3 ≤ lo + i + 1 := by omega
    have hhigh : lo + i + 1 ≤ j := by omega
    have hcast : ((lo + i + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hhigh
    apply ordinary _ _ hlow
    nlinarith
  have hCut : cut (a - (N : ℝ) * D) D N = a := by rw [cut_closed]; ring
  have h := equivariant_injective s (a - (N : ℝ) * D) D hD lo N image hOrd (nilpotent lo)
  rw [hCut, hdegree] at h
  exact h

/-- The ordinary zero band at a+ND gives zero equivariant restriction at a. -/
theorem detection_zero (α D C a : ℝ) (hD : 0 ≤ D) (N j : ℕ)
    (image : ∀ a b (hgap : a + D ≤ b), ∀ q z, ∃ zGlobal,
      s.resA a q zGlobal = s.cutA a b (by linarith) q z)
    (ordinary : ∀ c q, N + 3 ≤ q → α * c + C < (q : ℝ) →
      ∀ z, s.resA c q z = 0)
    (nilpotent : ∀ lo (x : BG lo),
      Finsler.Gysin.word (fun i => s.w (lo + i)) (N + 1) x = 0)
    (hjHigh : 2 * (N + 1) + 1 ≤ j)
    (hj : α * a + (C + α * (N : ℝ) * D) < (j : ℝ)) :
    ∀ x, s.resB a j x = 0 := by
  apply equivariant_zero s a D hD j N image
  · intro i hi
    have hlow : N + 3 ≤ j + i := by omega
    have hcast : (j : ℝ) ≤ ((j + i : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right j i
    apply ordinary _ _ hlow
    rw [cut_closed]
    nlinarith
  · exact nilpotent j

end Finsler.FilteredGysin
