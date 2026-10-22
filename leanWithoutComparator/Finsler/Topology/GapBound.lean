module

public import Finsler.Topology.CutString

/-! No transient classes in a long gap. At a regular cut a (with 2a regular) call a class of the
reflection Borel cohomology of (t_a, M) global if it is the restriction of a global class. Let
[g₀, g₀ + 14t] be a range of degrees on which multiplication by w is bijective modulo global
classes: a class whose w-multiple is global is global, and every class of the next degree is a
w-multiple modulo global classes. If some class of a degree in this range is not global, then
descending by surjectivity gives a non-global class y₀ of degree g₀, and its w-powers form a
string of non-global, hence nonzero, classes over the whole range. Against the budget of the
potentials (`CutString.lev_string_budget`, with a string of length t from g₀ + 3t, shift 10t, t
cutoffs from g₀ + 4t and 2t cutoffs from g₀ + 10t) this gives

  2 t² ≤ 18 · M · N · #(critical levels in [0, 2a]).

Since the right side grows linearly in a, a gap whose length grows linearly in a contains no
non-global classes at large cuts. The local bounds (`EventBounds`) and the bijectivity of w
modulo global classes on gaps are hypotheses. -/

@[expose] public section

namespace Finsler.GapBound

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.CriticalLevels Finsler.LevelCount Finsler.EventSum Finsler.StringBound
open Finsler.CutString

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n}

/-- A non-global class in a range of degrees on which w is bijective modulo global classes
bounds the length of the range by the budget of the potentials. -/
theorem gap_bound (E : EventBounds F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ}
    (ha : 0 < a) (h2a : 2 * a ∉ crit F) (g₀ t : ℕ) (ht : 1 ≤ t)
    (hinj : ∀ l, g₀ ≤ l → l < g₀ + 14 * t → ∀ y : HR (levComplex F a) l,
      w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1)) →
        y ∈ LinearMap.range (HRmap (resHom F a) l))
    (hsurj : ∀ l, g₀ ≤ l → l < g₀ + 14 * t → ∀ z : HR (levComplex F a) (l + 1),
      ∃ y : HR (levComplex F a) l,
        z + w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1)))
    (j : ℕ) (hj₀ : g₀ ≤ j) (hj₁ : j ≤ g₀ + 14 * t) (z : HR (levComplex F a) j)
    (hz : z ∉ LinearMap.range (HRmap (resHom F a) j)) :
    2 * (t : ℤ) ^ 2 ≤ 18 * (E.M : ℤ) * (E.N : ℤ) * (levelCount F (2 * a) : ℤ) := by
  -- a non-global class of degree g₀
  have hdesc : ∀ j, g₀ ≤ j → j ≤ g₀ + 14 * t → ∀ z : HR (levComplex F a) j,
      z ∉ LinearMap.range (HRmap (resHom F a) j) →
      ∃ y₀ : HR (levComplex F a) g₀, y₀ ∉ LinearMap.range (HRmap (resHom F a) g₀) := by
    intro j
    induction j with
    | zero =>
      intro h0 _ z hz
      have e : g₀ = 0 := Nat.le_zero.mp h0
      subst e
      exact ⟨z, hz⟩
    | succ j ih =>
      intro h0 h1 z hz
      rcases Nat.eq_or_lt_of_le h0 with e | hlt
      · subst e
        exact ⟨z, hz⟩
      · obtain ⟨y, hy⟩ := hsurj j (by omega) (by omega) z
        refine ih (by omega) (by omega) y fun hyim => hz ?_
        obtain ⟨x, rfl⟩ := hyim
        have hw : w (levComplex F a) j (HRmap (resHom F a) j x) ∈
            LinearMap.range (HRmap (resHom F a) (j + 1)) :=
          ⟨w (fullComplex n) j x, HRmap_w (resHom F a) j x⟩
        have hz' : z = (z + w (levComplex F a) j (HRmap (resHom F a) j x)) +
            w (levComplex F a) j (HRmap (resHom F a) j x) := by
          rw [add_assoc, two_eq_zero_of_mod, add_zero]
        rw [hz']
        exact Submodule.add_mem _ hy hw
  obtain ⟨y₀, hy₀⟩ := hdesc j hj₀ hj₁ z hz
  -- its string of powers of w
  have hstr : ∀ m, m ≤ 14 * t →
      strFrom (fun l => w (levComplex F a) l) g₀ y₀ (g₀ + m) ∉
        LinearMap.range (HRmap (resHom F a) (g₀ + m)) := by
    intro m
    induction m with
    | zero =>
      intro _
      change strFrom (fun l => w (levComplex F a) l) g₀ y₀ g₀ ∉ _
      rw [strFrom_self]
      exact hy₀
    | succ m ih =>
      intro hm hmem
      change strFrom (fun l => w (levComplex F a) l) g₀ y₀ (g₀ + m + 1) ∈ _ at hmem
      rw [strFrom_succ _ g₀ y₀ (g₀ + m) (Nat.le_add_right _ _)] at hmem
      exact ih (by omega) (hinj (g₀ + m) (Nat.le_add_right _ _) (by omega) _ hmem)
  have h := lev_string_budget E hn hfin ha h2a
    (strFrom (fun l => w (levComplex F a) l) g₀ y₀) (g₀ + 3 * t) t (10 * t)
    (fun l hl => (strFrom_succ _ g₀ y₀ l (by omega)).symm)
    (fun l hl hl' h0 => by
      obtain ⟨m, rfl⟩ : ∃ m, l = g₀ + m := ⟨l - g₀, by omega⟩
      exact hstr m (by omega) (h0 ▸ Submodule.zero_mem _))
    (g₀ + 4 * t) t (g₀ + 10 * t) (2 * t) (by omega) (by omega) (by omega)
  have ht0 : (0 : ℤ) < t := by exact_mod_cast ht
  have h' : (t : ℤ) * (2 * (t : ℤ) ^ 2) ≤
      (t : ℤ) * (18 * (E.M : ℤ) * (E.N : ℤ) * (levelCount F (2 * a) : ℤ)) := by
    push_cast at h
    nlinarith [h]
  exact le_of_mul_le_mul_left h' ht0

/-- If the budget of the potentials is smaller than 2t², every class of a degree in a range
[g₀, g₀ + 14t] on which w is bijective modulo global classes is global. -/
theorem gap_global (E : EventBounds F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ}
    (ha : 0 < a) (h2a : 2 * a ∉ crit F) (g₀ t : ℕ) (ht : 1 ≤ t)
    (hinj : ∀ l, g₀ ≤ l → l < g₀ + 14 * t → ∀ y : HR (levComplex F a) l,
      w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1)) →
        y ∈ LinearMap.range (HRmap (resHom F a) l))
    (hsurj : ∀ l, g₀ ≤ l → l < g₀ + 14 * t → ∀ z : HR (levComplex F a) (l + 1),
      ∃ y : HR (levComplex F a) l,
        z + w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1)))
    (hbig : 18 * (E.M : ℤ) * (E.N : ℤ) * (levelCount F (2 * a) : ℤ) < 2 * (t : ℤ) ^ 2)
    (j : ℕ) (hj₀ : g₀ ≤ j) (hj₁ : j ≤ g₀ + 14 * t) (z : HR (levComplex F a) j) :
    z ∈ LinearMap.range (HRmap (resHom F a) j) := by
  by_contra hz
  exact absurd (gap_bound E hn hfin ha h2a g₀ t ht hinj hsurj j hj₀ hj₁ z hz) (not_le.mpr hbig)

end

end Finsler.GapBound
