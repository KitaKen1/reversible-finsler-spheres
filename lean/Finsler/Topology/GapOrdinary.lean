module

public import Finsler.Topology.DefectBound
public import Finsler.Topology.OrdinaryExact

/-! The gap structure from ordinary cohomology. Multiplication by w on the Borel cohomology of an
involutive complex is injective in a degree where the ordinary cohomology vanishes and surjective
onto a degree where it vanishes (sign sequence). Let w^N annihilate the global reflection Borel
classes.

* Present gap. If the ordinary cohomology of the tail pair (Λ, t_a) vanishes in the degrees from
  g₀ + 1 − N to g₀ + L + 1, then in the degrees l of [g₀, g₀ + L): every class of the tail group
  of degree l + 1 is a w^N-multiple, so it maps to zero in the global classes and is a connecting
  image; the cokernel of global restriction is carried by the connecting map onto the tail
  group, compatibly with w, and w is bijective there. Hence a class of (t_a, M) whose w-multiple
  is global is global, and every class of the next degree is a w-multiple modulo global classes.

* Absent gap. If the ordinary cohomology of (t_a, M) vanishes in the degrees from g₀ to
  g₀ + L + N, then w is bijective on the reflection Borel cohomology of (t_a, M) in the degrees
  of [g₀, g₀ + L], w^N is injective there, so global classes restrict to zero, and the same two
  statements hold.

These are the two cases of the comparison on degree gaps of the source (Lemma 9.2). The gap
structure of `DefectBound` therefore follows from the corresponding statements about ordinary
cohomology (`OrdinaryGaps`), which are not proved.

The vanishing of the tail groups in a present gap follows from the bijectivity of the ordinary
restriction from the loop space to the cut in the same degrees and one degree below
(`ComparisonGaps`, the form of the ordinary comparison (9.4) of the source), by the cochain-level
chase of `OrdinaryExact`. The ordinary comparison itself is not proved. -/

@[expose] public section

namespace Finsler.GapOrdinary

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.BorelCrossing Finsler.CriticalLevels Finsler.NilpotentW Finsler.EventSum
open Finsler.DefectBound Finsler.Defect

noncomputable section

/-! ### Multiplication by w and ordinary cohomology -/

section Sign

variable (K : InvComplex)

/-- If the ordinary cohomology vanishes in degree j, multiplication by w is injective on the
Borel cohomology of degree j. -/
theorem w_injective {j : ℕ} (h : ∀ z : H K j, z = 0) : Function.Injective (w K j) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨z, rfl⟩ := (exact_w K j y).mp hy
  rw [h z, map_zero]

/-- If the ordinary cohomology vanishes in degree j + 1, multiplication by w is surjective onto
the Borel cohomology of degree j + 1. -/
theorem w_surjective {j : ℕ} (h : ∀ z : H K (j + 1), z = 0) : Function.Surjective (w K j) :=
  fun x => (exact_forget K j x).mp (h _)

theorem wPow_apply_zero (lo k : ℕ) : wPow K lo k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [wPow_succ, ih, map_zero]

/-- A power of w is injective if the ordinary cohomology vanishes in the degrees it passes. -/
theorem wPow_injective (lo k : ℕ) (h : ∀ i, lo ≤ i → i < lo + k → ∀ z : H K i, z = 0) :
    Function.Injective (wPow K lo k) := by
  induction k with
  | zero => exact fun x y hxy => hxy
  | succ k ih =>
    intro x y hxy
    rw [wPow_succ, wPow_succ] at hxy
    exact ih (fun i h1 h2 => h i h1 (by omega))
      (w_injective K (h (lo + k) (by omega) (by omega)) hxy)

/-- A power of w is surjective if the ordinary cohomology vanishes in the degrees it reaches. -/
theorem wPow_surjective (lo k : ℕ) (h : ∀ i, lo < i → i ≤ lo + k → ∀ z : H K i, z = 0) :
    Function.Surjective (wPow K lo k) := by
  induction k with
  | zero => exact fun x => ⟨x, rfl⟩
  | succ k ih =>
    intro x
    obtain ⟨y, rfl⟩ := w_surjective K (h (lo + k + 1) (by omega) (by omega)) x
    obtain ⟨z, rfl⟩ := ih (fun i h1 h2 => h i h1 (by omega)) y
    exact ⟨z, rfl⟩

end Sign

variable {n : ℕ} (F : ReversibleMetric n) (a : ℝ)

/-! ### A present gap -/

/-- If w^N annihilates the global classes and the ordinary cohomology of the tail pair vanishes
in the N degrees up to j, the classes of the tail group of degree j map to zero in the global
classes. -/
theorem tail_to_full_zero {N : ℕ}
    (hN : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0) (j : ℕ)
    (hj : N ≤ j) (h : ∀ i, j < i + N → i ≤ j → ∀ z : H (tailComplex F a) i, z = 0)
    (z : HR (tailComplex F a) j) : HRmap (tailHom F a) j z = 0 := by
  obtain ⟨lo, rfl⟩ : ∃ lo, j = lo + N := ⟨j - N, by omega⟩
  obtain ⟨z', rfl⟩ := wPow_surjective (tailComplex F a) lo N
    (fun i h1 h2 => h i (by omega) h2) z
  rw [HRmap_wPow, hN]

/-- In a present gap a class whose w-multiple is global is global. -/
theorem present_inj {l : ℕ} (h : ∀ z : H (tailComplex F a) (l + 1), z = 0)
    (y : HR (levComplex F a) l)
    (hy : w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1))) :
    y ∈ LinearMap.range (HRmap (resHom F a) l) := by
  obtain ⟨x, hx⟩ := hy
  have h1 : tailDelta F a (l + 1) (w (levComplex F a) l y) = 0 := by
    rw [← hx]
    exact tailDelta_res F a (l + 1) x
  rw [tailDelta_w] at h1
  exact exact_tailDelta F a l y
    (w_injective (tailComplex F a) h (h1.trans (map_zero _).symm))

/-- In a present gap every class of the next degree is a w-multiple modulo global classes. -/
theorem present_surj {N : ℕ}
    (hN : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0) {l : ℕ}
    (hl : N ≤ l + 1)
    (h : ∀ i, l + 1 < i + N → i ≤ l + 1 + 1 → ∀ z : H (tailComplex F a) i, z = 0)
    (z : HR (levComplex F a) (l + 1)) :
    ∃ y : HR (levComplex F a) l,
      z + w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1)) := by
  obtain ⟨p, hp⟩ := w_surjective (tailComplex F a) (j := l + 1)
    (h (l + 1 + 1) (by omega) le_rfl) (tailDelta F a (l + 1) z)
  have hp0 : HRmap (tailHom F a) (l + 1) p = 0 :=
    tail_to_full_zero F a hN (l + 1) hl (fun i h1 h2 => h i h1 (by omega)) p
  obtain ⟨y, hy⟩ := exact_tail_sub F a l p hp0
  refine ⟨y, exact_tailDelta F a (l + 1) _ ?_⟩
  rw [map_add, tailDelta_w, hy, hp, two_eq_zero_of_mod]

/-! ### An absent gap -/

/-- If w^N annihilates the global classes and the ordinary cohomology of (t_a, M) vanishes in
the N degrees from j, global classes of degree j restrict to zero. -/
theorem absent_res_zero {N : ℕ}
    (hN : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0) {j : ℕ}
    (h : ∀ i, j ≤ i → i < j + N → ∀ z : H (levComplex F a) i, z = 0)
    (x : HR (fullComplex n) j) : HRmap (resHom F a) j x = 0 := by
  have h1 : wPow (levComplex F a) j N (HRmap (resHom F a) j x) =
      wPow (levComplex F a) j N 0 := by
    rw [← HRmap_wPow, hN, map_zero, wPow_apply_zero]
  exact wPow_injective (levComplex F a) j N h h1

/-- In an absent gap a class whose w-multiple is global is global. -/
theorem absent_inj {N : ℕ}
    (hN : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0) {l : ℕ}
    (h : ∀ i, l ≤ i → i < l + 1 + N → ∀ z : H (levComplex F a) i, z = 0)
    (y : HR (levComplex F a) l)
    (hy : w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1))) :
    y ∈ LinearMap.range (HRmap (resHom F a) l) := by
  obtain ⟨x, hx⟩ := hy
  have h0 : w (levComplex F a) l y = 0 := by
    rw [← hx]
    exact absent_res_zero F a hN (fun i h1 h2 => h i (by omega) (by omega)) x
  have hy0 : y = 0 := w_injective (levComplex F a) (h l le_rfl (by omega))
    (h0.trans (map_zero _).symm)
  rw [hy0]
  exact Submodule.zero_mem _

/-- In an absent gap every class of the next degree is a w-multiple. -/
theorem absent_surj {l : ℕ} (h : ∀ z : H (levComplex F a) (l + 1), z = 0)
    (z : HR (levComplex F a) (l + 1)) :
    ∃ y : HR (levComplex F a) l,
      z + w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1)) := by
  obtain ⟨y, rfl⟩ := w_surjective (levComplex F a) h z
  refine ⟨y, ?_⟩
  rw [two_eq_zero_of_mod]
  exact Submodule.zero_mem _

/-! ### The gap structure -/

/-- The gap structure at large regular cuts in terms of ordinary cohomology: a power of w
annihilating the global classes, and for every degree outside the band either no class, or a
present gap (vanishing ordinary cohomology of the tail pair), or an absent gap (vanishing
ordinary cohomology of the cut). -/
structure OrdinaryGaps (F : ReversibleMetric n) where
  /-- a power of w annihilating the global reflection classes -/
  N : ℕ
  w_nil : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0
  a₀ : ℝ
  δ : ℝ
  δ_pos : 0 < δ
  W : ℕ
  R : ℕ
  band : ℝ → Finset ℕ
  band_card : ∀ a, (band a).card ≤ W
  band_rank : ∀ a, a₀ ≤ a → a ∉ crit F → 2 * a ∉ crit F → ∀ j ∈ band a,
    finrank (ZMod 2) (coker F a j) ≤ R
  gap : ∀ a, a₀ ≤ a → a ∉ crit F → 2 * a ∉ crit F → ∀ j, j ∉ band a →
    (∀ x : HR (levComplex F a) j, x = 0) ∨
    (∃ g₀ t : ℕ, δ * a ≤ t ∧ g₀ ≤ j ∧ j ≤ g₀ + 14 * t ∧ N ≤ g₀ + 1 ∧
      ∀ i, g₀ + 1 ≤ i + N → i ≤ g₀ + 14 * t + 1 → ∀ z : H (tailComplex F a) i, z = 0) ∨
    (∃ g₀ t : ℕ, δ * a ≤ t ∧ g₀ ≤ j ∧ j ≤ g₀ + 14 * t ∧
      ∀ i, g₀ ≤ i → i ≤ g₀ + 14 * t + N → ∀ z : H (levComplex F a) i, z = 0)

variable {F}

/-- The gap structure of `DefectBound` from the gap structure in terms of ordinary
cohomology. -/
def toGapInputs (O : OrdinaryGaps F) : GapInputs F where
  a₀ := O.a₀
  δ := O.δ
  δ_pos := O.δ_pos
  W := O.W
  R := O.R
  band := O.band
  band_card := O.band_card
  band_rank := O.band_rank
  gap := fun a ha hac h2a j hj => by
    rcases O.gap a ha hac h2a j hj with h0 | ⟨g₀, t, ht, hj₀, hj₁, hN, htail⟩ |
      ⟨g₀, t, ht, hj₀, hj₁, hlev⟩
    · exact Or.inl h0
    · refine Or.inr ⟨g₀, t, ht, hj₀, hj₁, fun l hl hl' y hy => ?_, fun l hl hl' z => ?_⟩
      · exact present_inj F a (htail (l + 1) (by omega) (by omega)) y hy
      · exact present_surj F a O.w_nil (by omega)
          (fun i h1 h2 => htail i (by omega) (by omega)) z
    · refine Or.inr ⟨g₀, t, ht, hj₀, hj₁, fun l hl hl' y hy => ?_, fun l hl hl' z => ?_⟩
      · exact absent_inj F a O.w_nil (fun i h1 h2 => hlev i (by omega) (by omega)) y hy
      · exact absent_surj F a (hlev (l + 1) (by omega) (by omega)) z

/-- With finitely many prime closed geodesic images, the local bounds for single crossings and
the gap structure in terms of ordinary cohomology, the defect is bounded on all positive regular
cuts. -/
theorem exists_defect_le_of_ordinary (E : EventBounds F) (O : OrdinaryGaps F) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ C : ℕ, ∀ a, 0 < a → a ∉ crit F → defect F a ≤ C :=
  exists_defect_le E (toGapInputs O) hn hfin

/-! ### The gap structure from the ordinary comparison -/

/-- The ordinary cohomology of the tail pair vanishes in a degree where the ordinary restriction
to the cut is bijective in that degree and in the preceding one. -/
theorem tail_eq_zero_of_res (i : ℕ)
    (h : ∀ k, i ≤ k + 1 → k ≤ i → Function.Bijective (Hmap (resHom F a) k))
    (z : H (tailComplex F a) i) : z = 0 := by
  cases i with
  | zero =>
    exact OrdinaryExact.sub_eq_zero_zero (shortExactTail F a) (h 0 (by omega) le_rfl).1 z
  | succ m =>
    exact OrdinaryExact.sub_eq_zero_succ (shortExactTail F a) m (h m (by omega) (by omega)).2
      (h (m + 1) (by omega) le_rfl).1 z

/-- The gap structure in terms of the ordinary comparison between the loop space and the cuts.
For a large cut whose double is regular, every degree outside a band of bounded size either
carries no reflection Borel class of the cut, or lies in a long present gap (the ordinary
restriction from the loop space to the cut is bijective in the degrees of the gap and in N
degrees below), or lies in a long absent gap (the ordinary cohomology of the cut vanishes in
the degrees of the gap and in N degrees above). -/
structure ComparisonGaps (F : ReversibleMetric n) where
  N : ℕ
  w_nil : ∀ (lo : ℕ) (x : HR (fullComplex n) lo), wPow (fullComplex n) lo N x = 0
  a₀ : ℝ
  δ : ℝ
  δ_pos : 0 < δ
  W : ℕ
  R : ℕ
  band : ℝ → Finset ℕ
  band_card : ∀ a, (band a).card ≤ W
  band_rank : ∀ a, a₀ ≤ a → a ∉ crit F → 2 * a ∉ crit F → ∀ j ∈ band a,
    finrank (ZMod 2) (coker F a j) ≤ R
  gap : ∀ a, a₀ ≤ a → a ∉ crit F → 2 * a ∉ crit F → ∀ j, j ∉ band a →
    (∀ x : HR (levComplex F a) j, x = 0) ∨
    (∃ g₀ t : ℕ, δ * a ≤ t ∧ g₀ ≤ j ∧ j ≤ g₀ + 14 * t ∧ N ≤ g₀ + 1 ∧
      ∀ i, g₀ ≤ i + N → i ≤ g₀ + 14 * t + 1 → Function.Bijective (Hmap (resHom F a) i)) ∨
    (∃ g₀ t : ℕ, δ * a ≤ t ∧ g₀ ≤ j ∧ j ≤ g₀ + 14 * t ∧
      ∀ i, g₀ ≤ i → i ≤ g₀ + 14 * t + N → ∀ z : H (levComplex F a) i, z = 0)

/-- The gap structure in terms of ordinary cohomology from the ordinary comparison. -/
def toOrdinaryGaps (O : ComparisonGaps F) : OrdinaryGaps F where
  N := O.N
  w_nil := O.w_nil
  a₀ := O.a₀
  δ := O.δ
  δ_pos := O.δ_pos
  W := O.W
  R := O.R
  band := O.band
  band_card := O.band_card
  band_rank := O.band_rank
  gap := fun a ha hac h2a j hj => by
    rcases O.gap a ha hac h2a j hj with h0 | ⟨g₀, t, ht, hj₀, hj₁, hN, hres⟩ |
      ⟨g₀, t, ht, hj₀, hj₁, hlev⟩
    · exact Or.inl h0
    · refine Or.inr (Or.inl ⟨g₀, t, ht, hj₀, hj₁, hN, fun i h1 h2 z => ?_⟩)
      exact tail_eq_zero_of_res a i (fun k hk hk' => hres k (by omega) (by omega)) z
    · exact Or.inr (Or.inr ⟨g₀, t, ht, hj₀, hj₁, hlev⟩)

/-- With finitely many prime closed geodesic images, the local bounds for single crossings and
the gap structure in terms of the ordinary comparison, the defect is bounded on all positive
regular cuts. -/
theorem exists_defect_le_of_comparison (E : EventBounds F) (O : ComparisonGaps F) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ C : ℕ, ∀ a, 0 < a → a ∉ crit F → defect F a ≤ C :=
  exists_defect_le_of_ordinary E (toOrdinaryGaps O) hn hfin

end

end Finsler.GapOrdinary
