module

public import Finsler.Topology.GysinZero
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! A common interface for the actual maps required by the detection argument.
This is an abstract filtered Gysin system, not a construction of Borel cohomology.
Nonpositive cut groups can be extended by zero when realizing the interface. -/

@[expose] public section

namespace Finsler.FilteredGysin

universe u

variable (AG BG : ℕ → Type u) (A B : ℝ → ℕ → Type u)
  [∀ q, AddCommGroup (AG q)] [∀ q, AddCommGroup (BG q)]
  [∀ a q, AddCommGroup (A a q)] [∀ a q, AddCommGroup (B a q)]

/-- The exactness and naturality inputs, with the ordinary image condition added
separately by the theorems below. Every map has its actual source and target. -/
structure Data where
  w : ∀ q, BG q →+ BG (q + 1)
  forget : ∀ q, BG q →+ AG q
  transfer : ∀ q, AG q →+ BG q
  wB : ∀ a q, B a q →+ B a (q + 1)
  forgetB : ∀ a q, B a q →+ A a q
  transferB : ∀ a q, A a q →+ B a q
  resA : ∀ a q, AG q →+ A a q
  resB : ∀ a q, BG q →+ B a q
  cutA : ∀ a b, a ≤ b → ∀ q, A b q →+ A a q
  cutB : ∀ a b, a ≤ b → ∀ q, B b q →+ B a q
  exact_forget : ∀ q x, forget (q + 1) x = 0 ↔ ∃ y, w q y = x
  exact_w : ∀ q y, w q y = 0 ↔ ∃ z, transfer q z = y
  exact_wB : ∀ a q y, wB a q y = 0 ↔ ∃ z, transferB a q z = y
  natural_forget : ∀ a q x, resA a q (forget q x) = forgetB a q (resB a q x)
  natural_w : ∀ a q y, wB a q (resB a q y) = resB a (q + 1) (w q y)
  natural_transfer : ∀ a q z, resB a q (transfer q z) = transferB a q (resA a q z)
  natural_cutA : ∀ a b (h : a ≤ b) q z, cutA a b h q (resA b q z) = resA a q z
  natural_cutB : ∀ a b (h : a ≤ b) q y, cutB a b h q (resB b q y) = resB a q y
  natural_cut_transfer : ∀ a b (h : a ≤ b) q z,
    cutB a b h q (transferB b q z) = transferB a q (cutA a b h q z)

variable {AG BG A B}

def cut (a D : ℝ) : ℕ → ℝ
  | 0 => a
  | i + 1 => cut a D i + D

theorem cut_closed (a D : ℝ) (i : ℕ) : cut a D i = a + (i : ℝ) * D := by
  induction i with
  | zero => simp [cut]
  | succ i ih => simp only [cut, ih, Nat.cast_add, Nat.cast_one]; ring

theorem base_le_cut (a D : ℝ) (hD : 0 ≤ D) (i : ℕ) : a ≤ cut a D i := by
  rw [cut_closed]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hD)

theorem cut_mono (a D : ℝ) (hD : 0 ≤ D) {i k : ℕ} (hik : i ≤ k) :
    cut a D i ≤ cut a D k := by
  rw [cut_closed, cut_closed]
  have hcast : (i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hik
  simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_right hcast hD) a

variable (s : Data AG BG A B)

theorem ordinary_injective_mono (a b : ℝ) (hab : a ≤ b) (q : ℕ)
    (ha : Function.Injective (s.resA a q)) : Function.Injective (s.resA b q) := by
  intro x y hxy
  apply ha
  rw [← s.natural_cutA a b hab q x, ← s.natural_cutA a b hab q y, hxy]

theorem ordinary_zero_mono (a b : ℝ) (hab : a ≤ b) (q : ℕ)
    (hb : ∀ z, s.resA b q z = 0) : ∀ z, s.resA a q z = 0 := by
  intro z
  rw [← s.natural_cutA a b hab q z, hb, map_zero]

/-- N+1 nilpotent factors require exactly N positive cut shifts.
Ordinary injectivity is needed only in degrees lo+1 through lo+N+1. -/
theorem equivariant_injective (a D : ℝ) (hD : 0 ≤ D) (lo N : ℕ)
    (image : ∀ a b (hgap : a + D ≤ b), ∀ q z, ∃ zGlobal,
      s.resA a q zGlobal = s.cutA a b (by linarith) q z)
    (ordinary : ∀ i, i ≤ N → Function.Injective (s.resA a (lo + i + 1)))
    (nilpotent : ∀ y : BG lo, Finsler.Gysin.word (fun i => s.w (lo + i)) (N + 1) y = 0) :
    Function.Injective (s.resB (cut a D N) (lo + N + 1)) := by
  let W := fun i => s.w (lo + i)
  let K : ∀ i, Set (BG (lo + i))
    | 0 => Set.univ
    | i + 1 => {x | s.resB (cut a D i) (lo + i + 1) x = 0}
  have descent : ∀ i, i < N + 1 → ∀ x : BG (lo + i + 1), x ∈ K (i + 1) →
      ∃ y : BG (lo + i), y ∈ K i ∧ W i y = x := by
    intro i hi x hx
    cases i with
    | zero =>
      change s.resB a (lo + 1) x = 0 at hx
      have hf : s.forget (lo + 1) x = 0 :=
        ordinary 0 (Nat.zero_le N) (by rw [s.natural_forget, hx, map_zero, map_zero])
      obtain ⟨y, hy⟩ := (s.exact_forget lo x).mp hf
      exact ⟨y, Set.mem_univ y, hy⟩
    | succ i =>
      have hab : cut a D i ≤ cut a D (i + 1) :=
        le_add_of_nonneg_right hD
      have ho := ordinary_injective_mono s a (cut a D (i + 1))
        (base_le_cut a D hD (i + 1)) (lo + (i + 1) + 1)
        (ordinary (i + 1) (Nat.le_of_lt_succ hi))
      obtain ⟨y, hy, hzero⟩ := Finsler.Gysin.kernel_descent
        (s.w (lo + (i + 1))) (s.forget (lo + (i + 1) + 1)) (s.transfer (lo + (i + 1)))
        (s.resB (cut a D i) (lo + (i + 1)))
        (s.resB (cut a D (i + 1)) (lo + (i + 1)))
        (s.resB (cut a D (i + 1)) (lo + (i + 1) + 1))
        (s.resA (cut a D i) (lo + (i + 1)))
        (s.resA (cut a D (i + 1)) (lo + (i + 1) + 1))
        (s.cutB _ _ hab _) (s.cutA _ _ hab _)
        (s.wB _ _) (s.forgetB _ _) (s.transferB _ _) (s.transferB _ _)
        (fun z hz => (s.exact_forget _ z).mp hz)
        (fun y hy => (s.exact_wB _ _ y).mp hy) ho
        (image _ _ (le_refl _) _)
        (s.natural_forget _ _) (s.natural_w _ _)
        (s.natural_cutB _ _ hab _) (s.natural_cut_transfer _ _ hab _)
        (s.natural_transfer _ _)
        (fun z => (s.exact_w _ _).mpr ⟨z, rfl⟩) x hx
      exact ⟨y, hzero, hy⟩
  intro x y hxy
  have hz : s.resB (cut a D N) (lo + N + 1) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzero := Finsler.Gysin.kernel_zero_of_nilpotent
    W K (N + 1) descent nilpotent (x - y) hz
  exact sub_eq_zero.mp hzero

/-- The ordinary zero band at the largest cut yields equivariant zero at a. -/
theorem equivariant_zero (a D : ℝ) (hD : 0 ≤ D) (lo N : ℕ)
    (image : ∀ a b (hgap : a + D ≤ b), ∀ q z, ∃ zGlobal,
      s.resA a q zGlobal = s.cutA a b (by linarith) q z)
    (ordinary : ∀ i, i ≤ N → ∀ z, s.resA (cut a D N) (lo + i) z = 0)
    (nilpotent : ∀ y : BG lo, Finsler.Gysin.word (fun i => s.w (lo + i)) (N + 1) y = 0) :
    ∀ x, s.resB a lo x = 0 := by
  intro x
  exact Finsler.Gysin.zero_of_nilpotent_word
    (fun i => s.w (lo + i)) (fun i => s.transfer (lo + i))
    (fun i => s.resB (cut a D i) (lo + i))
    (fun i => s.resB (cut a D (i + 1)) (lo + i))
    (fun i => s.wB (cut a D (i + 1)) (lo + i))
    (fun i => s.cutB (cut a D i) (cut a D (i + 1)) (le_add_of_nonneg_right hD) (lo + i))
    (fun i => s.transferB (cut a D (i + 1)) (lo + i))
    (fun i => s.transferB (cut a D i) (lo + i))
    (fun i => s.resA (cut a D i) (lo + i))
    (fun i => s.cutA (cut a D i) (cut a D (i + 1)) (le_add_of_nonneg_right hD) (lo + i))
    (fun i y hy => (s.exact_w _ y).mp hy)
    (fun i y hy => (s.exact_wB _ _ y).mp hy)
    (fun i => s.natural_transfer _ _) (fun i => s.natural_cut_transfer _ _ _ _)
    (fun i => s.natural_w _ _) (fun i => s.natural_cutB _ _ _ _)
    N (fun i _ => image _ _ (le_refl _) _)
    (fun i hi => ordinary_zero_mono s _ _ (cut_mono a D hD hi) _ (ordinary i hi))
    x (nilpotent x)

end Finsler.FilteredGysin
