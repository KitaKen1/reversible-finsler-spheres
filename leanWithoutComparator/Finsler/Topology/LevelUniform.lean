module

public import Finsler.Topology.LevelBounds

/-! Uniform rank and support bounds for the crossings of the critical levels. With finitely many
prime closed geodesic images there are constants B and A such that for every positive critical
level c and all cuts 0 < a < c < b with no other critical level in [a, b], the ordinary
cohomology of the loop pair (t_b, t_a) has total dimension at most B, and in every degree q in
which it is nonzero there is a label with a critical circle at c, the rotations of the k-fold
iterate of its closed geodesic, such that |q - I(k)| ≤ A. The bounds come from the formula of the
crossing of a level as the sum of shifted root labels: each root label is at most the loop
crossing of the chosen isolated band around its root level d √E with d dividing 2L, and these
finitely many crossings are finite dimensional and vanish in high degrees. -/

@[expose] public section

namespace Finsler.LevelUniform

open Module Set
open Finsler.SphereGeometry Finsler.Geometry Finsler.Geodesics
open Finsler.CriticalLevels Finsler.CriticalCircles Finsler.CircleLabel Finsler.CircleRoot
open Finsler.GeodesicFrames Finsler.LoopLabels Finsler.LevelBounds Finsler.OrientedCritical
open CategoryTheory Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple

noncomputable section

/-- The sum of a family shifted by b over the first Q degrees. -/
theorem sum_shift (f : ℕ → ℕ) (b Q : ℕ) :
    ∑ q ∈ Finset.range Q, (if b ≤ q then f (q - b) else 0) =
      ∑ j ∈ Finset.range (Q - b), f j := by
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : b ≤ Q
    · rw [ite_eq_left h, show Q + 1 - b = Q - b + 1 by omega, Finset.sum_range_succ]
    · rw [ite_eq_right h, add_zero, show Q + 1 - b = Q - b by omega]

theorem sum_shift_le (f : ℕ → ℕ) (b Q : ℕ) :
    ∑ q ∈ Finset.range Q, (if b ≤ q then f (q - b) else 0) ≤ ∑ j ∈ Finset.range Q, f j := by
  rw [sum_shift]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.sub_le Q b))

/-- A family vanishing from D on has partial sums at most its sum below D. -/
theorem sum_le_of_vanish (f : ℕ → ℕ) {D : ℕ} (hD : ∀ j, D ≤ j → f j = 0) (Q : ℕ) :
    ∑ j ∈ Finset.range Q, f j ≤ ∑ j ∈ Finset.range D, f j := by
  apply Finset.sum_le_sum_of_ne_zero
  intro j _ hj
  rw [Finset.mem_range]
  by_contra h
  exact hj (hD j (not_lt.mp h))


variable {n : ℕ} (F : ReversibleMetric n)

/-- The ordinary loop crossing of the chosen isolated band around a level. -/
abbrev bandH (hfin : (primeImages F).Finite) (x : ℝ) (j : ℕ) : Type :=
  H (triv (pairOf (lev_mono F (isoBand_le F hfin x)))) j

set_option maxHeartbeats 3200000 in
/-- **Uniform rank and support bounds for the crossings of the critical levels.** -/
theorem exists_level_bounds (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ B A : ℕ, ∀ {c a b : ℝ} (hab : a ≤ b), 0 < a → a < c → c < b →
      (∀ c' ∈ crit F, a ≤ c' → c' ≤ b → c' = c) →
      (∀ Q : ℕ, ∑ q ∈ Finset.range Q,
        finrank (ZMod 2) (H (triv (pairOf (lev_mono F hab))) q) ≤ B) ∧
      ∀ q : ℕ, (∃ x : H (triv (pairOf (lev_mono F hab))) q, x ≠ 0) →
        ∃ ℓ : Set (Sphere n) × Bool, ∃ hℓ : ℓ ∈ labels F hfin, ∃ k : ℕ,
          (k : ℝ) * Real.sqrt (Finsler.LoopEnergy.energy F
            (chosen F ℓ.1 ((mem_labels F hfin ℓ).mp hℓ)).loop) = c ∧
          q ≤ (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I k + A ∧
          (iterData (labelGeod F ℓ ((mem_labels F hfin ℓ).mp hℓ))).I k ≤ q + A := by
  classical
  -- the loop crossings of the chosen isolated bands are finite and vanish in high degrees
  have hband : ∀ x : ℝ, 0 < x → ∃ D : ℕ, (∀ j, Module.Finite (ZMod 2) (bandH F hfin x j)) ∧
      ∀ j, D ≤ j → ∀ y : bandH F hfin x j, y = 0 := by
    intro x hx
    obtain ⟨h0, -, -, -⟩ := isoBand_spec F hfin hx
    obtain ⟨hr1, hr2⟩ := isoBand_regular F hfin hx
    exact cross_finite F hn hfin h0 (isoBand_le F hfin x) hr1 hr2
  choose! Dx hDx using hband
  -- the totals of the bands
  set T : ℝ → ℕ := fun x => ∑ j ∈ Finset.range (Dx x), finrank (ZMod 2) (bandH F hfin x j)
    with hTdef
  -- the root levels of a label
  set Lf : (Set (Sphere n) × Bool) → ℕ := fun ℓ =>
    if h : ℓ.1 ∈ primeImages F then (iterData (labelGeod F ℓ h)).L else 0 with hLf
  set Ef : (Set (Sphere n) × Bool) → ℝ := fun ℓ =>
    if h : ℓ.1 ∈ primeImages F then
      Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 h).loop) else 0 with hEf
  set If : (Set (Sphere n) × Bool) → ℕ → ℕ := fun ℓ d =>
    if h : ℓ.1 ∈ primeImages F then (iterData (labelGeod F ℓ h)).I d else 0 with hIf
  set Tmax : ℕ := (labels F hfin).sup fun ℓ =>
    (Nat.divisors (2 * Lf ℓ)).sup fun d => T ((d : ℝ) * Ef ℓ) with hTmax
  set Dmax : ℕ := (labels F hfin).sup fun ℓ =>
    (Nat.divisors (2 * Lf ℓ)).sup fun d => Dx ((d : ℝ) * Ef ℓ) with hDmax
  set Imax : ℕ := (labels F hfin).sup fun ℓ =>
    (Nat.divisors (2 * Lf ℓ)).sup fun d => If ℓ d with hImax
  refine ⟨(labels F hfin).card * Tmax, max Imax Dmax,
    fun {c a b} hab ha hac hcb hone => ?_⟩
  have hc : 0 < c := ha.trans hac
  -- the formula of the level
  obtain ⟨s, bi, r, d, hs, hd, hcross⟩ :=
    loop_level_labels F hn hfin ha hac hcb hone hab le_rfl hac hcb le_rfl
  choose! hsl kk hkk hbi hbnd using hs
  choose! dr hdr hdrb using hbnd
  -- a common tight cut
  set e : ℝ := (insert d (s.image dr)).min' (Finset.insert_nonempty _ _) with hedef
  have he : 0 < e := (Finset.lt_min'_iff _ _).mpr fun x hx => by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hd
    · obtain ⟨ℓ, hℓ, rfl⟩ := Finset.mem_image.mp hx
      exact hdr ℓ hℓ
  have hed : e ≤ d := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hedr : ∀ ℓ ∈ s, e ≤ dr ℓ := fun ℓ hℓ =>
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem dr hℓ))
  set a' : ℝ := c ^ 2 - e / 4 with ha'
  set c' : ℝ := c ^ 2 + e / 4 with hc'
  have ha'c : a' < c ^ 2 := by rw [ha']; linarith
  have hcc' : c ^ 2 < c' := by rw [hc']; linarith
  have hw : c' - a' = e / 2 := by rw [ha', hc']; ring
  have hwd : c' - a' < d := by rw [hw]; linarith
  have hwr : ∀ ℓ ∈ s, c' - a' < dr ℓ := fun ℓ hℓ => by
    have := hedr ℓ hℓ
    rw [hw]
    linarith
  -- the crossing of the level is finite
  have hareg : a ∉ crit F := fun h => by
    have := hone a h le_rfl hab
    linarith
  have hbreg : b ∉ crit F := fun h => by
    have := hone b h hab le_rfl
    linarith
  obtain ⟨-, hfinX, -⟩ := cross_finite F hn hfin ha hab hareg hbreg
  have hform : ∀ q, finrank (ZMod 2) (H (triv (pairOf (lev_mono F hab))) q) =
      ∑ ℓ ∈ s, if bi ℓ ≤ q then r ℓ a' c' 1 (q - bi ℓ) else 0 := fun q =>
    hcross a' c' 1 le_rfl ha'c hcc' hwd q (hfinX q)
  -- the root level of a label of the level
  have hroot : ∀ ℓ ∈ s, ∃ x : ℝ, 0 < x ∧ (∀ j, r ℓ a' c' 1 j ≤
      finrank (ZMod 2) (bandH F hfin x j)) ∧ T x ≤ Tmax ∧ Dx x ≤ Dmax ∧
      If ℓ (Nat.gcd (kk ℓ) (2 * Lf ℓ)) ≤ Imax := by
    intro ℓ hℓ
    have hℓl := hsl ℓ hℓ
    have hp := (mem_labels F hfin ℓ).mp hℓl
    have hk := hkk ℓ hℓ
    have hEpos := chosen_energy_pos F ℓ.1 hp
    have hkpos : 0 < kk ℓ := by
      rcases Nat.eq_zero_or_pos (kk ℓ) with h0 | h0
      · rw [h0, Nat.cast_zero, zero_mul] at hk
        linarith
      · exact h0
    have hLpos : 0 < 2 * Lf ℓ := by
      simp only [hLf, dite_eq_left hp]
      have := (iterData (labelGeod F ℓ hp)).one_le
      omega
    have hgd : Nat.gcd (kk ℓ) (2 * Lf ℓ) ∈ Nat.divisors (2 * Lf ℓ) :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hLpos.ne'⟩
    have hgpos : 0 < Nat.gcd (kk ℓ) (2 * Lf ℓ) := Nat.gcd_pos_of_pos_left _ hkpos
    have hxeq : ((Nat.gcd (kk ℓ) (2 * (iterData (labelGeod F ℓ hp)).L) : ℕ) : ℝ) *
        Real.sqrt (Finsler.LoopEnergy.energy F (chosen F ℓ.1 hp).loop) =
        ((Nat.gcd (kk ℓ) (2 * Lf ℓ) : ℕ) : ℝ) * Ef ℓ := by
      simp only [hLf, hEf, dite_eq_left hp]
    refine ⟨((Nat.gcd (kk ℓ) (2 * Lf ℓ) : ℕ) : ℝ) * Ef ℓ, ?_, fun j => ?_, ?_, ?_, ?_⟩
    · rw [← hxeq]
      exact mul_pos (by exact_mod_cast Nat.gcd_pos_of_pos_left _ hkpos) hEpos
    · have hxpos : 0 < ((Nat.gcd (kk ℓ) (2 * Lf ℓ) : ℕ) : ℝ) * Ef ℓ := by
        rw [← hxeq]
        exact mul_pos (by exact_mod_cast Nat.gcd_pos_of_pos_left _ hkpos) hEpos
      have hb := hdrb ℓ hℓ a' c' 1 le_rfl ha'c hcc' (hwr ℓ hℓ) j
      rw [hxeq] at hb
      exact hb ((hDx _ hxpos).1 j)
    · exact (Finset.le_sup (f := fun d : ℕ => T ((d : ℝ) * Ef ℓ)) hgd).trans
        (Finset.le_sup (f := fun ℓ => (Nat.divisors (2 * Lf ℓ)).sup fun d : ℕ =>
          T ((d : ℝ) * Ef ℓ)) hℓl)
    · exact (Finset.le_sup (f := fun d : ℕ => Dx ((d : ℝ) * Ef ℓ)) hgd).trans
        (Finset.le_sup (f := fun ℓ => (Nat.divisors (2 * Lf ℓ)).sup fun d : ℕ =>
          Dx ((d : ℝ) * Ef ℓ)) hℓl)
    · exact (Finset.le_sup (f := fun d => If ℓ d) hgd).trans
        (Finset.le_sup (f := fun ℓ => (Nat.divisors (2 * Lf ℓ)).sup fun d => If ℓ d) hℓl)
  choose! xr hxr0 hxrb hxrT hxrD hxrI using hroot
  have hrvan : ∀ ℓ ∈ s, ∀ j, Dx (xr ℓ) ≤ j → r ℓ a' c' 1 j = 0 := by
    intro ℓ hℓ j hj
    have h1 := hxrb ℓ hℓ j
    have : Subsingleton (bandH F hfin (xr ℓ) j) :=
      ⟨fun y z => ((hDx _ (hxr0 ℓ hℓ)).2 j hj y).trans ((hDx _ (hxr0 ℓ hℓ)).2 j hj z).symm⟩
    rw [finrank_zero_of_subsingleton] at h1
    omega
  refine ⟨fun Q => ?_, fun q hq => ?_⟩
  · -- the total dimension
    calc ∑ q ∈ Finset.range Q, finrank (ZMod 2) (H (triv (pairOf (lev_mono F hab))) q)
        = ∑ ℓ ∈ s, ∑ q ∈ Finset.range Q, (if bi ℓ ≤ q then r ℓ a' c' 1 (q - bi ℓ) else 0) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun q _ => hform q
      _ ≤ ∑ ℓ ∈ s, Tmax := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          calc ∑ q ∈ Finset.range Q, (if bi ℓ ≤ q then r ℓ a' c' 1 (q - bi ℓ) else 0)
              ≤ ∑ j ∈ Finset.range Q, r ℓ a' c' 1 j := sum_shift_le _ _ _
            _ ≤ ∑ j ∈ Finset.range (Dx (xr ℓ)), r ℓ a' c' 1 j :=
                sum_le_of_vanish _ (hrvan ℓ hℓ) Q
            _ ≤ T (xr ℓ) := Finset.sum_le_sum fun j _ => hxrb ℓ hℓ j
            _ ≤ Tmax := hxrT ℓ hℓ
      _ = s.card * Tmax := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (labels F hfin).card * Tmax :=
          Nat.mul_le_mul_right _ (Finset.card_le_card fun ℓ hℓ => hsl ℓ hℓ)
  · -- the support
    obtain ⟨x, hx⟩ := hq
    have : Nontrivial (H (triv (pairOf (lev_mono F hab))) q) := ⟨⟨x, 0, hx⟩⟩
    have := hfinX q
    have hpos : 0 < finrank (ZMod 2) (H (triv (pairOf (lev_mono F hab))) q) :=
      Module.finrank_pos
    rw [hform q] at hpos
    obtain ⟨ℓ, hℓ, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    have hbq : bi ℓ ≤ q := by
      by_contra h
      exact hne (ite_eq_right h)
    rw [ite_eq_left hbq] at hne
    have hlt : q - bi ℓ < Dx (xr ℓ) := by
      by_contra h
      exact hne (hrvan ℓ hℓ _ (not_lt.mp h))
    have hD := hxrD ℓ hℓ
    have hI := hxrI ℓ hℓ
    have hp := (mem_labels F hfin ℓ).mp (hsl ℓ hℓ)
    have hbieq := hbi ℓ hℓ
    have hIf : If ℓ (Nat.gcd (kk ℓ) (2 * Lf ℓ)) =
        (iterData (labelGeod F ℓ hp)).I (Nat.gcd (kk ℓ) (2 * (iterData (labelGeod F ℓ hp)).L)) := by
      simp only [hIf, hLf, dite_eq_left hp]
    refine ⟨ℓ, hsl ℓ hℓ, kk ℓ, hkk ℓ hℓ, ?_, ?_⟩
    · have := le_max_right Imax Dmax
      omega
    · have := le_max_left Imax Dmax
      rw [hIf] at hI
      omega

end

end Finsler.LevelUniform
