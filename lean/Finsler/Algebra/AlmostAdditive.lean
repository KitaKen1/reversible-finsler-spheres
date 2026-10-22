module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! Sequences that are additive up to a bounded error. If a sequence I of natural numbers
satisfies |I(m + k) - I(m) - I(k)| ≤ c for all m, k ≥ 1, there is a mean Δ ≥ 0 with
|I(m) - m Δ| ≤ c for all m ≥ 1. The proof compares multiples: j I(m) + c ≤ I(j m) + j c and
I(j m) + c ≤ j (I(m) + c), so (I(m) - c)/m ≤ (I(k) + c)/k for all m and k, and Δ is the infimum
of the numbers (I(k) + c)/k. This is the elementary form of the estimate for the indices of the
iterates of a closed geodesic. -/

@[expose] public section

namespace Finsler.AlmostAdditive

variable {I : ℕ → ℕ} {c : ℕ}

/-- The upper bound for multiples: I(j m) + c ≤ j (I(m) + c). -/
theorem mul_le (h₁ : ∀ m k, 1 ≤ m → 1 ≤ k → I (m + k) ≤ I m + I k + c) {m : ℕ} (hm : 1 ≤ m)
    {j : ℕ} (hj : 1 ≤ j) : I (j * m) + c ≤ j * (I m + c) := by
  induction j, hj using Nat.le_induction with
  | base => rw [Nat.one_mul, Nat.one_mul]
  | succ j hj ih =>
    have hjm : 1 ≤ j * m := Nat.mul_pos hj hm
    have h := h₁ (j * m) m hjm hm
    rw [Nat.succ_mul, Nat.succ_mul]
    omega

/-- The lower bound for multiples: j I(m) + c ≤ I(j m) + j c. -/
theorem le_mul (h₂ : ∀ m k, 1 ≤ m → 1 ≤ k → I m + I k ≤ I (m + k) + c) {m : ℕ} (hm : 1 ≤ m)
    {j : ℕ} (hj : 1 ≤ j) : j * I m + c ≤ I (j * m) + j * c := by
  induction j, hj using Nat.le_induction with
  | base => rw [Nat.one_mul, Nat.one_mul, Nat.one_mul]
  | succ j hj ih =>
    have hjm : 1 ≤ j * m := Nat.mul_pos hj hm
    have h := h₂ (j * m) m hjm hm
    rw [Nat.succ_mul, Nat.succ_mul, Nat.succ_mul]
    omega

/-- The normalized lower bounds are below the normalized upper bounds. -/
theorem div_le_div (h₁ : ∀ m k, 1 ≤ m → 1 ≤ k → I (m + k) ≤ I m + I k + c)
    (h₂ : ∀ m k, 1 ≤ m → 1 ≤ k → I m + I k ≤ I (m + k) + c) {m k : ℕ} (hm : 1 ≤ m)
    (hk : 1 ≤ k) : ((I m : ℝ) - c) / m ≤ ((I k : ℝ) + c) / k := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  rw [div_le_div_iff₀ hmpos hkpos]
  have hB := le_mul h₂ hm hk
  have hA := mul_le h₁ hk hm
  rw [Nat.mul_comm m k] at hA
  have hBr : (k : ℝ) * I m + c ≤ I (k * m) + k * c := by exact_mod_cast hB
  have hAr : (I (k * m) : ℝ) + c ≤ m * (I k + c) := by exact_mod_cast hA
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  linarith

/-- **The mean of an almost additive sequence.** -/
theorem exists_mean (h₁ : ∀ m k, 1 ≤ m → 1 ≤ k → I (m + k) ≤ I m + I k + c)
    (h₂ : ∀ m k, 1 ≤ m → 1 ≤ k → I m + I k ≤ I (m + k) + c) :
    ∃ Δ : ℝ, 0 ≤ Δ ∧ ∀ m, 1 ≤ m → |(I m : ℝ) - m * Δ| ≤ c := by
  set s : Set ℝ := {x | ∃ k : ℕ, 1 ≤ k ∧ x = ((I k : ℝ) + c) / k} with hs
  have hne : s.Nonempty := ⟨((I 1 : ℝ) + c) / (1 : ℕ), 1, le_rfl, rfl⟩
  have hlow : ∀ m : ℕ, 1 ≤ m → ∀ x ∈ s, ((I m : ℝ) - c) / m ≤ x := by
    rintro m hm x ⟨k, hk, rfl⟩
    exact div_le_div h₁ h₂ hm hk
  have hbdd : BddBelow s := ⟨((I 1 : ℝ) - c) / (1 : ℕ), hlow 1 le_rfl⟩
  refine ⟨sInf s, ?_, fun m hm => ?_⟩
  · by_contra hneg
    rw [not_le] at hneg
    obtain ⟨m, hm⟩ := exists_nat_gt ((c : ℝ) / (-sInf s))
    have h1 : ((I (m + 1) : ℝ) - c) / ((m + 1 : ℕ) : ℝ) ≤ sInf s :=
      le_csInf hne (hlow (m + 1) (Nat.succ_le_succ (Nat.zero_le m)))
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have h2 : (I (m + 1) : ℝ) - c ≤ sInf s * ((m + 1 : ℕ) : ℝ) := (div_le_iff₀ hpos).mp h1
    have h3 : (c : ℝ) < (m : ℝ) * (-sInf s) := (div_lt_iff₀ (neg_pos.mpr hneg)).mp hm
    have hI : (0 : ℝ) ≤ I (m + 1) := Nat.cast_nonneg _
    push_cast at h2
    linarith
  · have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hle : sInf s ≤ ((I m : ℝ) + c) / m := csInf_le hbdd ⟨m, hm, rfl⟩
    have hge : ((I m : ℝ) - c) / m ≤ sInf s := le_csInf hne (hlow m hm)
    rw [le_div_iff₀ hmpos] at hle
    rw [div_le_iff₀ hmpos] at hge
    rw [abs_le]
    constructor <;> linarith

/-- With mean zero the sequence is bounded by the error. -/
theorem le_of_mean_eq_zero {Δ : ℝ} (hΔ : Δ = 0) {m : ℕ} (h : |(I m : ℝ) - m * Δ| ≤ c) :
    I m ≤ c := by
  rw [hΔ, mul_zero, sub_zero, Nat.abs_cast] at h
  exact_mod_cast h

end Finsler.AlmostAdditive
