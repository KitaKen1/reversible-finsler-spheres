module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! Discrete Fourier sums. For an integer l not divisible by N the sums Σ_{k<N} cos(2πlk/N) and
Σ_{k<N} sin(2πlk/N) vanish, as the real and imaginary parts of the geometric sum of the N-th root
of unity exp(2πil/N) ≠ 1. With the product formulas this gives the orthogonality relations of the
modes cos(2πjk/N), sin(2πjk/N) for 0 ≤ 2j < N, which make the Fourier coefficients of a polygon
explicit coordinates. -/

@[expose] public section

namespace Finsler.RoundFourier

open Finset Complex
open scoped Real

noncomputable section

/-- The geometric sum of a nontrivial N-th root of unity vanishes. -/
theorem sum_exp_eq_zero {N : ℕ} (hN : 0 < N) {l : ℤ} (hl : ¬ (N : ℤ) ∣ l) :
    ∑ k ∈ range N, Complex.exp (k * (2 * π * l / N * I)) = 0 := by
  set z := Complex.exp (2 * π * l / N * I) with hz
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpow : ∀ k : ℕ, Complex.exp (k * (2 * π * l / N * I)) = z ^ k := fun k =>
    Complex.exp_nat_mul _ k
  simp only [hpow]
  have hz1 : z ≠ 1 := by
    intro h
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h
    apply hl
    refine ⟨m, ?_⟩
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 * π * I : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, hπ]
    have h3 : (l : ℂ) / N = m := by
      have : (2 * π * I : ℂ) * ((l : ℂ) / N) = (2 * π * I) * m := by
        rw [show (2 * π * I : ℂ) * ((l : ℂ) / N) = 2 * π * l / N * I by ring, hm]
        ring
      exact mul_left_cancel₀ h2 this
    have h4 : (l : ℂ) = N * m := by
      rw [← h3]
      field_simp
    exact_mod_cast h4
  rw [geom_sum_eq hz1]
  have hzN : z ^ N = 1 := by
    rw [hz, ← Complex.exp_nat_mul]
    have : (N : ℂ) * (2 * π * l / N * I) = l * (2 * π * I) := by
      field_simp
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I l
  rw [hzN, sub_self, zero_div]

theorem arg_eq (N : ℕ) (l : ℤ) (k : ℕ) :
    (k : ℂ) * (2 * π * l / N * I) = ((2 * π * l / N * k : ℝ) : ℂ) * I := by
  push_cast
  ring

/-- The cosine sum of a nontrivial frequency vanishes. -/
theorem sum_cos_eq_zero {N : ℕ} (hN : 0 < N) {l : ℤ} (hl : ¬ (N : ℤ) ∣ l) :
    ∑ k ∈ range N, Real.cos (2 * π * l / N * k) = 0 := by
  have h := congrArg Complex.re (sum_exp_eq_zero hN hl)
  rw [Complex.re_sum, Complex.zero_re] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [arg_eq, Complex.exp_ofReal_mul_I_re]

/-- The sine sum of a nontrivial frequency vanishes. -/
theorem sum_sin_eq_zero {N : ℕ} (hN : 0 < N) {l : ℤ} (hl : ¬ (N : ℤ) ∣ l) :
    ∑ k ∈ range N, Real.sin (2 * π * l / N * k) = 0 := by
  have h := congrArg Complex.im (sum_exp_eq_zero hN hl)
  rw [Complex.im_sum, Complex.zero_im] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [arg_eq, Complex.exp_ofReal_mul_I_im]

/-- A frequency l with 0 < |l| < N is not divisible by N. -/
theorem not_dvd_of_lt {N : ℕ} {l : ℤ} (h0 : l ≠ 0) (h1 : |l| < N) : ¬ (N : ℤ) ∣ l := by
  rintro ⟨q, rfl⟩
  have hq : q ≠ 0 := by
    rintro rfl
    simp at h0
  have : (N : ℤ) ≤ |(N : ℤ) * q| := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ N)]
    have : 1 ≤ |q| := Int.one_le_abs hq
    nlinarith
  linarith

/-! ### Orthogonality of the modes -/

section Modes

variable {N : ℕ} (hN : 0 < N)
include hN

theorem cos_sum_of_ne {a : ℤ} (ha : a ≠ 0) (haN : |a| < N) :
    ∑ k ∈ range N, Real.cos (2 * π * a / N * k) = 0 :=
  sum_cos_eq_zero hN (not_dvd_of_lt ha haN)

theorem sin_sum_of_ne {a : ℤ} (ha : a ≠ 0) (haN : |a| < N) :
    ∑ k ∈ range N, Real.sin (2 * π * a / N * k) = 0 :=
  sum_sin_eq_zero hN (not_dvd_of_lt ha haN)

omit hN in
theorem sin_sum_zero_freq : ∑ k ∈ range N, Real.sin (2 * π * (0 : ℤ) / N * k) = 0 := by
  simp

omit hN in
/-- The angle 2πjk/N as the product used in the sums. -/
theorem ang_eq (j : ℕ) (k : ℕ) : 2 * π * (j : ℝ) / N * k = 2 * π * ((j : ℤ) : ℝ) / N * k := by
  push_cast
  ring

/-- Σ cos(αk) cos(α'k) over the modes 0 ≤ 2j, 2j' < N. -/
theorem sum_cos_cos {j j' : ℕ} (hj : 2 * j < N) (hj' : 2 * j' < N) :
    ∑ k ∈ range N, Real.cos (2 * π * j / N * k) * Real.cos (2 * π * j' / N * k) =
      if j = j' then (if j = 0 then (N : ℝ) else N / 2) else 0 := by
  have hprod : ∀ k : ℕ, Real.cos (2 * π * j / N * k) * Real.cos (2 * π * j' / N * k) =
      (Real.cos (2 * π * ((j : ℤ) - j' : ℤ) / N * k) +
        Real.cos (2 * π * ((j : ℤ) + j' : ℤ) / N * k)) / 2 := by
    intro k
    have h1 : 2 * π * (((j : ℤ) - j' : ℤ) : ℝ) / N * k =
        2 * π * j / N * k - 2 * π * j' / N * k := by push_cast; ring
    have h2 : 2 * π * (((j : ℤ) + j' : ℤ) : ℝ) / N * k =
        2 * π * j / N * k + 2 * π * j' / N * k := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp only [hprod]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hjj : j = j'
  · subst hjj
    simp only [sub_self, Int.cast_zero, mul_zero, zero_div, zero_mul, Real.cos_zero,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, if_true]
    by_cases h0 : j = 0
    · subst h0
      simp
    · rw [if_neg h0]
      have hs : ∑ k ∈ range N, Real.cos (2 * π * (((j : ℤ) + j : ℤ) : ℝ) / N * k) = 0 := by
        apply cos_sum_of_ne hN
        · omega
        · rw [abs_of_nonneg (by positivity)]
          omega
      rw [hs]
      ring
  · rw [if_neg hjj]
    have hs1 : ∑ k ∈ range N, Real.cos (2 * π * (((j : ℤ) - j' : ℤ) : ℝ) / N * k) = 0 := by
      apply cos_sum_of_ne hN
      · omega
      · rw [abs_lt]
        constructor <;> omega
    have hs2 : ∑ k ∈ range N, Real.cos (2 * π * (((j : ℤ) + j' : ℤ) : ℝ) / N * k) = 0 := by
      apply cos_sum_of_ne hN
      · omega
      · rw [abs_of_nonneg (by positivity)]
        omega
    rw [hs1, hs2]
    ring

/-- Σ sin(αk) sin(α'k) over the modes 0 < 2j, 2j' < N. -/
theorem sum_sin_sin {j j' : ℕ} (hj0 : 0 < j) (hj : 2 * j < N) (hj' : 2 * j' < N) :
    ∑ k ∈ range N, Real.sin (2 * π * j / N * k) * Real.sin (2 * π * j' / N * k) =
      if j = j' then (N : ℝ) / 2 else 0 := by
  have hprod : ∀ k : ℕ, Real.sin (2 * π * j / N * k) * Real.sin (2 * π * j' / N * k) =
      (Real.cos (2 * π * ((j : ℤ) - j' : ℤ) / N * k) -
        Real.cos (2 * π * ((j : ℤ) + j' : ℤ) / N * k)) / 2 := by
    intro k
    have h1 : 2 * π * (((j : ℤ) - j' : ℤ) : ℝ) / N * k =
        2 * π * j / N * k - 2 * π * j' / N * k := by push_cast; ring
    have h2 : 2 * π * (((j : ℤ) + j' : ℤ) : ℝ) / N * k =
        2 * π * j / N * k + 2 * π * j' / N * k := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp only [hprod]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have hs2 : ∑ k ∈ range N, Real.cos (2 * π * (((j : ℤ) + j' : ℤ) : ℝ) / N * k) = 0 := by
    apply cos_sum_of_ne hN
    · omega
    · rw [abs_of_nonneg (by positivity)]
      omega
  rw [hs2, sub_zero]
  by_cases hjj : j = j'
  · subst hjj
    rw [if_pos rfl]
    simp
  · rw [if_neg hjj]
    have hs1 : ∑ k ∈ range N, Real.cos (2 * π * (((j : ℤ) - j' : ℤ) : ℝ) / N * k) = 0 := by
      apply cos_sum_of_ne hN
      · omega
      · rw [abs_lt]
        constructor <;> omega
    rw [hs1]
    ring

/-- Σ cos(αk) sin(α'k) = 0 over the modes 0 ≤ 2j, 2j' < N. -/
theorem sum_cos_sin {j j' : ℕ} (hj : 2 * j < N) (hj' : 2 * j' < N) :
    ∑ k ∈ range N, Real.cos (2 * π * j / N * k) * Real.sin (2 * π * j' / N * k) = 0 := by
  have hprod : ∀ k : ℕ, Real.cos (2 * π * j / N * k) * Real.sin (2 * π * j' / N * k) =
      (Real.sin (2 * π * ((j' : ℤ) + j : ℤ) / N * k) +
        Real.sin (2 * π * ((j' : ℤ) - j : ℤ) / N * k)) / 2 := by
    intro k
    have h1 : 2 * π * (((j' : ℤ) - j : ℤ) : ℝ) / N * k =
        2 * π * j' / N * k - 2 * π * j / N * k := by push_cast; ring
    have h2 : 2 * π * (((j' : ℤ) + j : ℤ) : ℝ) / N * k =
        2 * π * j' / N * k + 2 * π * j / N * k := by push_cast; ring
    rw [h1, h2, Real.sin_sub, Real.sin_add]
    ring
  simp only [hprod]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  have hsum : ∀ a : ℤ, |a| < N → ∑ k ∈ range N, Real.sin (2 * π * (a : ℝ) / N * k) = 0 := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      simp
    · exact sin_sum_of_ne hN h0 ha
  rw [hsum _ (by rw [abs_of_nonneg (by positivity)]; omega),
    hsum _ (by rw [abs_lt]; constructor <;> omega)]
  ring

end Modes

end

end Finsler.RoundFourier
