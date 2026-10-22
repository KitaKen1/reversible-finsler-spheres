import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-!
# The arithmetic step in the two-sphere argument

This module develops the finite-spectrum obstruction used in Lemma 5.5 of
De Philippis--Marini--Mazzucchelli--Suhr, *Closed geodesics on reversible Finsler
2-spheres*, https://arxiv.org/abs/2002.00415.

The proof below avoids a rational/irrational case split: two close hits of the
same generator force an exact bounded integer relation; that relation then
forces a positive integer to be strictly smaller than one.
-/

namespace Finsler.TwoSphere.Arithmetic

/-- Convert the symmetric `k`-dense convention of DPMMS to forward bounded gaps. -/
theorem forward_dense_of_symmetric_dense (K : Set ℕ) (k : ℕ)
    (hK : ∀ N : ℕ, ∃ m ∈ K, (N : ℤ) - k < m ∧ (m : ℤ) < N + k) :
    ∀ N : ℕ, ∃ m ∈ K, N ≤ m ∧ m ≤ N + 2 * k := by
  intro N
  obtain ⟨m, hm, hlo, hhi⟩ := hK (N + k)
  refine ⟨m, hm, ?_, ?_⟩ <;> omega

private theorem finite_positive_lower_bound {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, δ ≤ f a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨δ, hδ, hbound⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    refine ⟨min (f a) δ, lt_min (hf a (Finset.mem_insert_self _ _)) hδ, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound b hb)

private theorem no_two_hits (l ε : ℝ) (C W : ℕ)
    (hl : 0 < l) (hε : 0 < ε) (hε1 : ε < 1) (hCε : (C : ℝ) * ε < 1)
    (hlarge : (W : ℝ) + 1 < (C : ℝ) * l)
    (hgap : ∀ d k : ℕ, d ≤ C → k ≤ W → (d : ℝ) * l ≠ k →
      ε < |(d : ℝ) * l - k|)
    (p q a b : ℕ) (hpq : p < q) (hpqW : q - p ≤ W)
    (ha : (p : ℝ) < (a : ℝ) * l) (ha' : (a : ℝ) * l ≤ p + ε)
    (hb : (q : ℝ) < (b : ℝ) * l) (hb' : (b : ℝ) * l ≤ q + ε) : False := by
  have hpqR : (p : ℝ) + 1 ≤ q := by exact_mod_cast hpq
  have hab : a < b := by
    by_contra! h
    have hh : (b : ℝ) ≤ a := by exact_mod_cast h
    nlinarith
  let d := b - a
  let k := q - p
  have hd : 0 < d := Nat.sub_pos_of_lt hab
  have hdR : (d : ℝ) = (b : ℝ) - a := Nat.cast_sub (Nat.le_of_lt hab)
  have hkR : (k : ℝ) = (q : ℝ) - p := Nat.cast_sub (Nat.le_of_lt hpq)
  have hkW : k ≤ W := hpqW
  have hkWR : (k : ℝ) ≤ W := by exact_mod_cast hkW
  have hdC : d ≤ C := by
    have : (d : ℝ) < C := by nlinarith
    exact Nat.le_of_lt (by exact_mod_cast this)
  have he : (d : ℝ) * l = k := by
    by_contra hne
    have h := hgap d k hdC hkW hne
    have hu : |(d : ℝ) * l - k| < ε := by
      apply abs_lt.mpr
      constructor <;> nlinarith
    linarith
  have hid : (d : ℝ) * ((a : ℝ) * l - p) = (a : ℝ) * k - p * d := by
    calc
      _ = (a : ℝ) * ((d : ℝ) * l) - p * d := by ring
      _ = _ := by rw [he]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hpos : (p : ℝ) * d < (a : ℝ) * k := by
    have := mul_pos hdpos (sub_pos.mpr ha)
    linarith
  have hint : p * d + 1 ≤ a * k := by exact_mod_cast hpos
  have hintR : (p : ℝ) * d + 1 ≤ (a : ℝ) * k := by exact_mod_cast hint
  have hsmall : (d : ℝ) * ((a : ℝ) * l - p) < 1 := by
    have h1 := mul_le_mul_of_nonneg_left (show (a : ℝ) * l - p ≤ ε by linarith)
      hdpos.le
    have h2 : (d : ℝ) * ε ≤ (C : ℝ) * ε :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hdC) hε.le
    linarith
  linarith

private theorem finite_no_two_hits (s : Finset ℝ) (hs : ∀ l ∈ s, 0 < l) (W : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ l ∈ s, ∀ p q a b : ℕ,
      p < q → q - p ≤ W →
      (p : ℝ) < (a : ℝ) * l → (a : ℝ) * l ≤ p + ε →
      (q : ℝ) < (b : ℝ) * l → (b : ℝ) * l ≤ q + ε → False := by
  classical
  obtain ⟨ρ, hρ, hlow⟩ := finite_positive_lower_bound s id hs
  obtain ⟨C, hC⟩ := exists_nat_gt (((W : ℝ) + 1) / ρ)
  have hlarge : (W : ℝ) + 1 < (C : ℝ) * ρ := (div_lt_iff₀ hρ).mp hC
  let pairs := (s.product (Finset.range (C + 1))).product (Finset.range (W + 1))
  let gap : (ℝ × ℕ) × ℕ → ℝ := fun t =>
    if (t.1.2 : ℝ) * t.1.1 = t.2 then 1 else |(t.1.2 : ℝ) * t.1.1 - t.2|
  have hgap : ∀ t ∈ pairs, 0 < gap t := by
    intro t _
    dsimp [gap]
    split_ifs with h
    · norm_num
    · exact abs_pos.mpr (sub_ne_zero.mpr h)
  obtain ⟨δ, hδ, hbound⟩ := finite_positive_lower_bound pairs gap hgap
  let ε := min (δ / 2) (1 / (2 * ((C : ℝ) + 1)))
  have hden : 0 < 2 * ((C : ℝ) + 1) := by positivity
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεgap : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hεsmall : ε * (2 * ((C : ℝ) + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hCε0 : 0 ≤ (C : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε.le
  have hε1 : ε < 1 := by nlinarith
  have hCε : (C : ℝ) * ε < 1 := by nlinarith
  refine ⟨ε, hε, ?_⟩
  intro l hl p q a b hpq hpqW ha ha' hb hb'
  apply no_two_hits l ε C W (hs l hl) hε hε1 hCε
    (hlarge.trans_le (mul_le_mul_of_nonneg_left (hlow l hl) (Nat.cast_nonneg C)))
    ?_ p q a b hpq hpqW ha ha' hb hb'
  intro d k hd hk hne
  have ht : ((l, d), k) ∈ pairs := Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨hl, Finset.mem_range.mpr (show d < C + 1 by omega)⟩,
      Finset.mem_range.mpr (show k < W + 1 by omega)⟩
  have h := hbound _ ht
  simp only [gap, ite_eq_right hne] at h
  exact hεgap.trans_le h

/-- A finite union of positive arithmetic spectra cannot hit every sufficiently
small interval immediately above a block of `s.card + 1` consecutive points
of a fixed positive integer progression. The interval size is uniform in the
starting point `M`. -/
theorem finite_spectrum_progression_gap (s : Finset ℝ) (hs : ∀ l ∈ s, 0 < l)
    (step : ℕ) (hstep : 0 < step) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : ℕ, ∃ j : Fin (s.card + 1),
      ¬ ∃ l ∈ s, ∃ a : ℕ,
        ((M + step * j.val : ℕ) : ℝ) < (a : ℝ) * l ∧
        (a : ℝ) * l ≤ ((M + step * j.val : ℕ) : ℝ) + ε := by
  classical
  obtain ⟨ε, hε, hno⟩ := finite_no_two_hits s hs (step * s.card)
  refine ⟨ε, hε, fun M => ?_⟩
  by_contra! h
  choose l hl a ha ha' using h
  have hpair : ∀ i j : Fin (s.card + 1), i < j → l i = l j → False := by
    intro i j hij heq
    have hpq : M + step * i.val < M + step * j.val :=
      Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hij hstep) M
    have hj : j.val ≤ s.card := Nat.le_of_lt_succ j.isLt
    have hb := Nat.mul_le_mul_left step hj
    have hpqW : (M + step * j.val) - (M + step * i.val) ≤ step * s.card := by omega
    exact hno (l i) (hl i) _ _ (a i) (a j) hpq hpqW
      (ha i) (ha' i) (heq.symm ▸ ha j) (heq.symm ▸ ha' j)
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => (⟨l i, hl i⟩ : ↥s)) (by simp)
  have heq' : l i = l j := congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hpair i j hij heq'
  · exact hpair j i hji heq'.symm

/-- The finite-spectrum obstruction on any set of natural numbers with bounded
gaps. This is the arithmetic core of DPMMS Lemma 5.5. -/
theorem finite_spectrum_not_dense_approximated (s : Finset ℝ)
    (hs : ∀ l ∈ s, 0 < l) (K : Set ℕ) (D : ℕ)
    (hK : ∀ N : ℕ, ∃ m ∈ K, N ≤ m ∧ m ≤ N + D) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m ∈ K, M ≤ m →
      ∃ l ∈ s, ∃ a : ℕ, (m : ℝ) < (a : ℝ) * l ∧ (a : ℝ) * l ≤ m + ε) := by
  classical
  obtain ⟨ε, hε, hno⟩ := finite_no_two_hits s hs ((D + 1) * s.card + D)
  intro h
  obtain ⟨M, hM⟩ := h ε hε
  have hex : ∀ i : Fin (s.card + 1), ∃ m ∈ K,
      M + (D + 1) * i.val ≤ m ∧ m ≤ M + (D + 1) * i.val + D :=
    fun i => hK _
  choose m hm hlo hhi using hex
  have hh : ∀ i, ∃ l ∈ s, ∃ a : ℕ,
      (m i : ℝ) < (a : ℝ) * l ∧ (a : ℝ) * l ≤ m i + ε := by
    intro i
    exact hM (m i) (hm i) (by have := hlo i; omega)
  choose l hl a ha ha' using hh
  have hpair : ∀ i j : Fin (s.card + 1), i < j → l i = l j → False := by
    intro i j hij heq
    have hij' : i.val + 1 ≤ j.val := hij
    have hmul := Nat.mul_le_mul_left (D + 1) hij'
    simp only [Nat.mul_add, Nat.mul_one] at hmul
    have hi := hhi i
    have hj := hlo j
    have hpq : m i < m j := by omega
    have hjcard : j.val ≤ s.card := Nat.le_of_lt_succ j.isLt
    have hmul' := Nat.mul_le_mul_left (D + 1) hjcard
    have hpqW : m j - m i ≤ (D + 1) * s.card + D := by
      have := hhi j
      have := hlo i
      omega
    exact hno (l i) (hl i) _ _ (a i) (a j) hpq hpqW
      (ha i) (ha' i) (heq.symm ▸ ha j) (heq.symm ▸ ha' j)
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i => (⟨l i, hl i⟩ : ↥s)) (by simp)
  have heq' : l i = l j := congrArg Subtype.val heq
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hpair i j hij heq'
  · exact hpair j i hji heq'.symm

/-- The odd-iterate version of the arithmetic obstruction in DPMMS Lemma 5.5.
No finite set of positive generators can produce lengths arbitrarily close
above every sufficiently large odd integer. -/
theorem finite_spectrum_not_odd_approximated (s : Finset ℝ)
    (hs : ∀ l ∈ s, 0 < l) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → Odd m →
      ∃ l ∈ s, ∃ a : ℕ, (m : ℝ) < (a : ℝ) * l ∧ (a : ℝ) * l ≤ m + ε) := by
  obtain ⟨ε, hε, hgap⟩ := finite_spectrum_progression_gap s hs 2 (by omega)
  intro h
  obtain ⟨M, hM⟩ := h ε hε
  obtain ⟨j, hj⟩ := hgap (2 * M + 1)
  exact hj (hM (2 * M + 1 + 2 * j.val) (by omega) ⟨M + j.val, by omega⟩)

end Finsler.TwoSphere.Arithmetic
