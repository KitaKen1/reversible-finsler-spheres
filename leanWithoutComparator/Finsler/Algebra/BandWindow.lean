module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ByContra

/-! Bands and windows. Let S be a finite set of nonnegative slopes containing 0, with distinct
slopes at least γ > 0 apart, and let a be large. A degree j which is farther than c₁ + N + 3
from every line s a (s in S) either lies above all these lines, or lies in a window
[g₀, g₀ + 14 t] of natural numbers with t ≥ (γ / 30) a, such that every degree i of the extended
window, g₀ ≤ i + N and i ≤ g₀ + 14 t + N + 2, is farther than c₁ from every line and on the same
side of every line as j. This is the arithmetic of the degree gaps between the bands of the
comparison on degree gaps (source Lemma 9.2); no topology is used. -/

@[expose] public section

namespace Finsler.BandWindow

/-- Distinct elements of a finite set of real numbers are a positive distance apart. -/
theorem exists_gap (S : Finset ℝ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ σ ∈ S, ∀ τ ∈ S, σ < τ → γ ≤ τ - σ := by
  classical
  by_cases hne : (S.offDiag.filter fun p : ℝ × ℝ => p.1 < p.2).Nonempty
  · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ (fun p : ℝ × ℝ => p.2 - p.1) hne
    refine ⟨p.2 - p.1, sub_pos.mpr (Finset.mem_filter.mp hp).2, fun σ hσ τ hτ hlt => ?_⟩
    exact hmin (σ, τ) (Finset.mem_filter.mpr
      ⟨Finset.mem_offDiag.mpr ⟨hσ, hτ, hlt.ne⟩, hlt⟩)
  · refine ⟨1, one_pos, fun σ hσ τ hτ hlt => ?_⟩
    exact absurd ⟨(σ, τ), Finset.mem_filter.mpr
      ⟨Finset.mem_offDiag.mpr ⟨hσ, hτ, hlt.ne⟩, hlt⟩⟩ hne

/-- A degree far from all slope lines lies above all of them or in a long window between two
consecutive ones. -/
theorem exists_window {S : Finset ℝ} (h0 : (0 : ℝ) ∈ S) {γ : ℝ}
    (hgap : ∀ σ ∈ S, ∀ τ ∈ S, σ < τ → γ ≤ τ - σ) {c₁ : ℝ} (hc₁ : 0 ≤ c₁) (N : ℕ) {a : ℝ}
    (ha : 0 < a) (ha2 : 15 * (2 * c₁ + 2 * N + 4) ≤ γ * a) (j : ℕ)
    (hj : ∀ s ∈ S, c₁ + N + 3 < |(j : ℝ) - s * a|) :
    (∀ s ∈ S, s * a < j) ∨
    ∃ g₀ t : ℕ, γ / 30 * a ≤ t ∧ g₀ ≤ j ∧ j ≤ g₀ + 14 * t ∧ N ≤ g₀ + 1 ∧
      ∀ i : ℕ, g₀ ≤ i + N → i ≤ g₀ + 14 * t + N + 2 →
        ∀ s ∈ S, c₁ < |(i : ℝ) - s * a| ∧ (s * a < i ↔ s * a < j) := by
  classical
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  by_cases habove : ∀ s ∈ S, s * a < j
  · exact Or.inl habove
  right
  -- no slope line passes through j
  have hne : ∀ s ∈ S, s * a ≠ j := fun s hs h => by
    have h' := hj s hs
    rw [h, sub_self, abs_zero] at h'
    linarith
  -- the line just above j
  obtain ⟨σ', hσ'S, hσ'⟩ : ∃ s ∈ S, ¬ s * a < j := by
    by_contra hcon
    exact habove fun s hs => by
      by_contra hs'
      exact hcon ⟨s, hs, hs'⟩
  have hup : (S.filter fun s => (j : ℝ) < s * a).Nonempty :=
    ⟨σ', Finset.mem_filter.mpr ⟨hσ'S, lt_of_le_of_ne (not_lt.mp hσ') (hne σ' hσ'S).symm⟩⟩
  obtain ⟨s', hs'mem, hs'min⟩ := Finset.exists_min_image _ (fun s => s * a) hup
  have hs'S : s' ∈ S := (Finset.mem_filter.mp hs'mem).1
  have hjs' : (j : ℝ) < s' * a := (Finset.mem_filter.mp hs'mem).2
  -- the line just below j
  have hj0 : (0 : ℝ) < j := by
    have h := hj 0 h0
    rw [zero_mul, sub_zero, abs_of_nonneg (Nat.cast_nonneg j)] at h
    linarith
  have hlo : (S.filter fun s => s * a < (j : ℝ)).Nonempty :=
    ⟨0, Finset.mem_filter.mpr ⟨h0, by rw [zero_mul]; exact hj0⟩⟩
  obtain ⟨s, hsmem, hsmax⟩ := Finset.exists_max_image _ (fun s => s * a) hlo
  have hsS : s ∈ S := (Finset.mem_filter.mp hsmem).1
  have hsj : s * a < (j : ℝ) := (Finset.mem_filter.mp hsmem).2
  have hss' : s < s' := lt_of_mul_lt_mul_right (hsj.trans hjs') ha.le
  have hγa : γ * a ≤ s' * a - s * a := by
    have h := mul_le_mul_of_nonneg_right (hgap s hsS s' hs'S hss') ha.le
    linarith [sub_mul s' s a]
  have hsm : s * a + (c₁ + N + 3) < j := by
    have h := hj s hsS
    rw [abs_of_pos (sub_pos.mpr hsj)] at h
    linarith
  have hs'm : (j : ℝ) + (c₁ + N + 3) < s' * a := by
    have h := hj s' hs'S
    rw [abs_of_neg (sub_neg.mpr hjs')] at h
    linarith
  have hdich : ∀ σ ∈ S, σ * a ≤ s * a ∨ s' * a ≤ σ * a := fun σ hσ => by
    rcases lt_or_gt_of_ne (hne σ hσ) with h | h
    · exact Or.inl (hsmax σ (Finset.mem_filter.mpr ⟨hσ, h⟩))
    · exact Or.inr (hs'min σ (Finset.mem_filter.mpr ⟨hσ, h⟩))
  have hs0 : 0 ≤ s * a := by
    have h := hsmax 0 (Finset.mem_filter.mpr ⟨h0, by rw [zero_mul]; exact hj0⟩)
    simpa using h
  -- the length of the window
  obtain ⟨t, ht⟩ : ∃ t : ℕ, t = ⌊γ * a / 15⌋₊ := ⟨_, rfl⟩
  have hγa0 : 0 ≤ γ * a / 15 := by linarith
  have ht1 : (t : ℝ) ≤ γ * a / 15 := by
    rw [ht]
    exact Nat.floor_le hγa0
  have ht2 : γ * a / 15 < (t : ℝ) + 1 := by
    rw [ht]
    exact Nat.lt_floor_add_one _
  -- the lower end of the window
  have hlo0 : 0 ≤ s * a + c₁ + N := by linarith
  obtain ⟨l, hl⟩ : ∃ l : ℕ, l = ⌊s * a + c₁ + N⌋₊ := ⟨_, rfl⟩
  have hl1 : (l : ℝ) ≤ s * a + c₁ + N := by
    rw [hl]
    exact Nat.floor_le hlo0
  have hl2 : s * a + c₁ + N < (l : ℝ) + 1 := by
    rw [hl]
    exact Nat.lt_floor_add_one _
  have hlj : l + 1 ≤ j := by
    have h : (l : ℝ) + 1 < j := by linarith
    exact_mod_cast h.le
  refine ⟨max (l + 1) (j - 14 * t), t, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · exact max_le hlj (Nat.sub_le _ _)
  · exact Nat.sub_le_iff_le_add.mp (le_max_right _ _)
  · have h : (N : ℝ) < (l : ℝ) + 1 := by linarith
    have h' : N < l + 1 := by exact_mod_cast h
    exact (h'.le.trans (le_max_left _ _)).trans (Nat.le_succ _)
  · intro i hi1 hi2 σ hσ
    -- bounds for the ends of the window
    have hg1 : s * a + c₁ + N < ((max (l + 1) (j - 14 * t) : ℕ) : ℝ) := by
      have h : ((l + 1 : ℕ) : ℝ) ≤ ((max (l + 1) (j - 14 * t) : ℕ) : ℝ) :=
        Nat.cast_le.mpr (le_max_left _ _)
      rw [Nat.cast_add, Nat.cast_one] at h
      linarith
    have hg2 : ((max (l + 1) (j - 14 * t) : ℕ) : ℝ) + 14 * t + N + 2 < s' * a - c₁ := by
      rcases le_total (l + 1) (j - 14 * t) with hcase | hcase
      · rw [max_eq_right hcase]
        have h14 : 14 * t ≤ j := by
          by_contra hcon
          have hz : j - 14 * t = 0 := Nat.sub_eq_zero_of_le (not_le.mp hcon).le
          rw [hz] at hcase
          exact Nat.not_succ_le_zero _ hcase
        have h : ((j - 14 * t : ℕ) : ℝ) = (j : ℝ) - 14 * t := by
          rw [Nat.cast_sub h14]
          push_cast
          ring
        rw [h]
        linarith
      · rw [max_eq_left hcase]
        push_cast
        linarith
    have hi1' : ((max (l + 1) (j - 14 * t) : ℕ) : ℝ) ≤ (i : ℝ) + N := by exact_mod_cast hi1
    have hi2' : (i : ℝ) ≤ ((max (l + 1) (j - 14 * t) : ℕ) : ℝ) + 14 * t + N + 2 := by
      exact_mod_cast hi2
    have hil : s * a + c₁ < i := by linarith
    have hiu : (i : ℝ) + c₁ < s' * a := by linarith
    rcases hdich σ hσ with h | h
    · have hpos : 0 < (i : ℝ) - σ * a := by linarith
      refine ⟨by rw [abs_of_pos hpos]; linarith, ?_⟩
      exact ⟨fun _ => by linarith, fun _ => by linarith⟩
    · have hneg : (i : ℝ) - σ * a < 0 := by linarith
      refine ⟨by rw [abs_of_neg hneg]; linarith, ?_⟩
      exact ⟨fun h1 => by linarith, fun h1 => by linarith⟩

end Finsler.BandWindow
