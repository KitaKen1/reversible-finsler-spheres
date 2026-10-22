module

public import Finsler.Topology.NilpotentW

/-! Counting the critical levels below a cut. With finitely many prime closed geodesic images the
set of critical levels in [0, a] is finite; its number of elements is the level count of a. The
induction over the critical levels below a regular cut holds with this number: a property of a
positive level and a number which holds with number 0 at all small levels, is transported with
the same number along intervals without critical levels, and with the next number across regular
cuts with at most one critical level between them, holds at every positive regular cut with its
level count. The level count grows at most linearly: every critical level is a positive integer
multiple of one of the finitely many prime levels. -/

@[expose] public section

namespace Finsler.LevelCount

open Set
open Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- The number of critical levels in [0, a]. -/
def levelCount (a : ℝ) : ℕ := (crit F ∩ Icc 0 a).ncard

/-- Induction over the critical levels below a regular cut, with their number. -/
theorem forall_levelCount (hfin : (primeImages F).Finite) (P : ℝ → ℕ → Prop)
    (hsmall : ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ b : ℝ, 0 < b → b ≤ b₀ → P b 0)
    (hreg : ∀ a b : ℝ, 0 < a → a ≤ b → (∀ x ∈ Icc a b, x ∉ crit F) → ∀ k : ℕ, P a k → P b k)
    (hcross : ∀ a b : ℝ, 0 < a → a ≤ b → a ∉ crit F → b ∉ crit F →
      (crit F ∩ Icc a b).Subsingleton → ∀ k : ℕ, P a k → P b (k + 1))
    (a : ℝ) (ha : 0 < a) (hac : a ∉ crit F) : P a (levelCount F a) := by
  have key : ∀ m : ℕ, ∀ a : ℝ, 0 < a → a ∉ crit F → (crit F ∩ Icc 0 a).ncard = m → P a m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro a ha hac hm
      have hSfin : (crit F ∩ Icc 0 a).Finite := crit_finite F hfin 0 a
      by_cases hne : (crit F ∩ Icc 0 a).Nonempty
      · obtain ⟨c, hcS, hcmax⟩ := Set.exists_max_image _ id hSfin hne
        have hc0 : 0 < c := crit_pos F hcS.1
        have hca : c < a := lt_of_le_of_ne hcS.2.2 (fun h => hac (h ▸ hcS.1))
        have hTfin : (insert (0 : ℝ) ((crit F ∩ Icc 0 a) \ {c})).Finite :=
          (hSfin.subset sdiff_subset).insert 0
        obtain ⟨c', hc'T, hc'max⟩ := Set.exists_max_image _ id hTfin (insert_nonempty _ _)
        have hc'c : c' < c := by
          rcases hc'T with h | ⟨hx, hxne⟩
          · rw [h]
            exact hc0
          · exact lt_of_le_of_ne (hcmax _ hx) hxne
        have hc'0 : 0 ≤ c' := hc'max 0 (mem_insert _ _)
        have ha'0 : 0 < (c' + c) / 2 := by linarith
        have hlow : ∀ x ∈ crit F, 0 ≤ x → x ≤ a → x ≠ c → x ≤ c' := fun x hx h0 hxa hxc =>
          hc'max x (mem_insert_of_mem _ ⟨⟨hx, h0, hxa⟩, hxc⟩)
        have ha'c : (c' + c) / 2 ∉ crit F := by
          intro h
          have := hlow _ h ha'0.le (by linarith) (ne_of_lt (by linarith))
          linarith
        have hall : ∀ x ∈ crit F ∩ Icc ((c' + c) / 2) a, x = c := by
          rintro x ⟨hx, hx1, hx2⟩
          by_contra hxc
          have := hlow x hx (by linarith) hx2 hxc
          linarith
        have hsub : (crit F ∩ Icc ((c' + c) / 2) a).Subsingleton := by
          intro x hx y hy
          rw [hall x hx, hall y hy]
        have hEq : crit F ∩ Icc 0 a = insert c (crit F ∩ Icc 0 ((c' + c) / 2)) := by
          ext x
          constructor
          · rintro ⟨hx, hx0, hxa⟩
            by_cases hxc : x = c
            · exact Or.inl hxc
            · have := hlow x hx hx0 hxa hxc
              exact Or.inr ⟨hx, hx0, by linarith⟩
          · rintro (rfl | ⟨hx, hx0, hxa'⟩)
            · exact hcS
            · exact ⟨hx, hx0, by linarith⟩
        have hnot : c ∉ crit F ∩ Icc 0 ((c' + c) / 2) := by
          rintro ⟨-, -, hc2⟩
          linarith
        have hcard : (crit F ∩ Icc 0 ((c' + c) / 2)).ncard + 1 = m := by
          rw [← hm, hEq, Set.ncard_insert_of_notMem hnot (crit_finite F hfin 0 _)]
        have hlt : (crit F ∩ Icc 0 ((c' + c) / 2)).ncard < m := by omega
        have hk := ih _ hlt ((c' + c) / 2) ha'0 ha'c rfl
        have hab : (c' + c) / 2 ≤ a := by linarith
        rw [← hcard]
        exact hcross _ a ha'0 hab ha'c hac hsub _ hk
      · obtain ⟨b₀, hb₀, hzero⟩ := hsmall
        have hm0 : m = 0 := by
          rw [← hm, Set.not_nonempty_iff_eq_empty.mp hne, Set.ncard_empty]
        rw [hm0]
        have hb : 0 < min a b₀ := lt_min ha hb₀
        have hreg' : ∀ x ∈ Icc (min a b₀) a, x ∉ crit F := fun x hx hxc =>
          hne ⟨x, hxc, by linarith [hx.1], hx.2⟩
        exact hreg _ a hb (min_le_left _ _) hreg' 0 (hzero _ hb (min_le_right _ _))
  exact key _ a ha hac rfl

/-- With finitely many prime closed geodesic images the number of critical levels in [0, a]
grows at most linearly in a. -/
theorem exists_levelCount_le (hfin : (primeImages F).Finite) :
    ∃ C : ℕ, ∀ a : ℝ, 0 ≤ a → (levelCount F a : ℝ) ≤ C * (1 + a) := by
  classical
  have hP := primeLevels_finite F hfin
  refine ⟨⌈∑ l ∈ hP.toFinset, (1 / l + 1)⌉₊, fun a ha => ?_⟩
  have hsub : crit F ∩ Icc 0 a ⊆
      ((hP.toFinset.biUnion fun l =>
        (Finset.range (⌊a / l⌋₊ + 1)).image fun j : ℕ => (j : ℝ) * l : Finset ℝ) : Set ℝ) := by
    rintro c ⟨hc, -, hca⟩
    obtain ⟨l, hl, j, rfl⟩ := crit_eq_multiple F hc
    have hlpos := primeLevels_pos F hl
    rw [Finset.mem_coe, Finset.mem_biUnion]
    refine ⟨l, hP.mem_toFinset.mpr hl, Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr ?_, rfl⟩⟩
    exact Nat.lt_succ_of_le (Nat.le_floor ((le_div_iff₀ hlpos).mpr hca))
  have h1 : levelCount F a ≤
      (hP.toFinset.biUnion fun l =>
        (Finset.range (⌊a / l⌋₊ + 1)).image fun j : ℕ => (j : ℝ) * l).card := by
    have h := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rwa [Set.ncard_coe_finset] at h
  have h2 : (hP.toFinset.biUnion fun l =>
        (Finset.range (⌊a / l⌋₊ + 1)).image fun j : ℕ => (j : ℝ) * l).card ≤
      ∑ l ∈ hP.toFinset, (⌊a / l⌋₊ + 1) :=
    Finset.card_biUnion_le.trans (Finset.sum_le_sum fun l _ =>
      Finset.card_image_le.trans (Finset.card_range _).le)
  have h3 : ((∑ l ∈ hP.toFinset, (⌊a / l⌋₊ + 1) : ℕ) : ℝ) ≤
      (∑ l ∈ hP.toFinset, (1 / l + 1)) * (1 + a) := by
    rw [Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun l hl => ?_
    have hlpos := primeLevels_pos F (hP.mem_toFinset.mp hl)
    have hfl : ((⌊a / l⌋₊ : ℕ) : ℝ) ≤ a / l := Nat.floor_le (div_nonneg ha hlpos.le)
    have hl1 : 0 ≤ 1 / l := by positivity
    push_cast
    have e : (1 / l + 1) * (1 + a) = a / l + 1 + (1 / l + a) := by ring
    rw [e]
    linarith
  have h4 : (∑ l ∈ hP.toFinset, (1 / l + 1)) ≤ (⌈∑ l ∈ hP.toFinset, (1 / l + 1)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have h5 : (0 : ℝ) ≤ 1 + a := by linarith
  calc (levelCount F a : ℝ) ≤ ((∑ l ∈ hP.toFinset, (⌊a / l⌋₊ + 1) : ℕ) : ℝ) := by
        exact_mod_cast h1.trans h2
    _ ≤ (∑ l ∈ hP.toFinset, (1 / l + 1)) * (1 + a) := h3
    _ ≤ (⌈∑ l ∈ hP.toFinset, (1 / l + 1)⌉₊ : ℝ) * (1 + a) :=
        mul_le_mul_of_nonneg_right h4 h5

end

end Finsler.LevelCount
