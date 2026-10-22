module

public import Finsler.Topology.GapBound

/-! The defect is bounded, from local bounds for single crossings and the gap structure at large
cuts. The gap structure (`GapInputs`) says that at every large regular cut a with 2a regular the
degrees outside a set of at most W band degrees either carry no reflection Borel class of
(t_a, M) or lie in a range [g₀, g₀ + 14t] with t ≥ δa on which multiplication by w is bijective
modulo global classes, and that the cokernel of global restriction has dimension at most R in
every band degree. With finitely many prime closed geodesic images and the local bounds
(`EventBounds`): for large a the budget of the potentials is smaller than 2t², so every class in
such a range is global and the defect is at most W·R; the defect is the same at the two ends of
an interval without critical levels, so it is bounded on every bounded set of regular cuts, and
a regular cut can be moved to one whose double is regular. Hence the defect is bounded on all
positive regular cuts. The two inputs are not proved. -/

@[expose] public section

namespace Finsler.DefectBound

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.CriticalLevels Finsler.LevelCount Finsler.EventSum Finsler.GapBound
open Finsler.Defect Finsler.FiniteCut Finsler.RegularInterval

noncomputable section

variable {n : ℕ}

/-- The gap structure of the reflection Borel cohomology of (t_a, M) at large regular cuts. -/
structure GapInputs (F : ReversibleMetric n) where
  a₀ : ℝ
  δ : ℝ
  δ_pos : 0 < δ
  /-- bound for the number of band degrees -/
  W : ℕ
  /-- bound for the cokernel of global restriction in a band degree -/
  R : ℕ
  /-- the band degrees of a cut -/
  band : ℝ → Finset ℕ
  band_card : ∀ a, (band a).card ≤ W
  band_rank : ∀ a, a₀ ≤ a → a ∉ crit F → 2 * a ∉ crit F → ∀ j ∈ band a,
    finrank (ZMod 2) (coker F a j) ≤ R
  gap : ∀ a, a₀ ≤ a → a ∉ crit F → 2 * a ∉ crit F → ∀ j, j ∉ band a →
    (∀ x : HR (levComplex F a) j, x = 0) ∨
    ∃ g₀ t : ℕ, δ * a ≤ t ∧ g₀ ≤ j ∧ j ≤ g₀ + 14 * t ∧
      (∀ l, g₀ ≤ l → l < g₀ + 14 * t → ∀ y : HR (levComplex F a) l,
        w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1)) →
          y ∈ LinearMap.range (HRmap (resHom F a) l)) ∧
      (∀ l, g₀ ≤ l → l < g₀ + 14 * t → ∀ z : HR (levComplex F a) (l + 1),
        ∃ y : HR (levComplex F a) l,
          z + w (levComplex F a) l y ∈ LinearMap.range (HRmap (resHom F a) (l + 1)))

variable {F : ReversibleMetric n}

/-- If every class of a degree is global, the cokernel of global restriction vanishes in that
degree. -/
theorem finrank_coker_eq_zero {a : ℝ} {j : ℕ}
    (h : ∀ z : HR (levComplex F a) j, z ∈ LinearMap.range (HRmap (resHom F a) j)) :
    finrank (ZMod 2) (coker F a j) = 0 := by
  have hsub : Subsingleton (coker F a j) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [(Submodule.Quotient.mk_eq_zero _).mpr (h x), (Submodule.Quotient.mk_eq_zero _).mpr (h y)]
  exact finrank_zero_of_subsingleton

/-- At large regular cuts a with 2a regular the defect is at most W·R. -/
theorem exists_defect_le_large (E : EventBounds F) (Gp : GapInputs F) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ a₁ : ℝ, 0 < a₁ ∧ ∀ a, a₁ ≤ a → a ∉ crit F → 2 * a ∉ crit F →
      defect F a ≤ Gp.W * Gp.R := by
  obtain ⟨C, hC⟩ := exists_levelCount_le F hfin
  have hδ2 : 0 < 2 * Gp.δ ^ 2 := by have := Gp.δ_pos; positivity
  refine ⟨max Gp.a₀ (max 1 ((3 * (18 * E.M * E.N * C : ℕ) + 1) / (2 * Gp.δ ^ 2))),
    lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_right _ _)),
    fun a ha hac h2a => ?_⟩
  have ha₀ : Gp.a₀ ≤ a := (le_max_left _ _).trans ha
  have ha1 : 1 ≤ a := ((le_max_left _ _).trans (le_max_right _ _)).trans ha
  have ha2 : (3 * (18 * E.M * E.N * C : ℕ) + 1) / (2 * Gp.δ ^ 2) ≤ a :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans ha
  have ha0 : 0 < a := by linarith
  have hK : (3 * ((18 * E.M * E.N * C : ℕ) : ℝ) + 1) ≤ 2 * Gp.δ ^ 2 * a := by
    rw [div_le_iff₀ hδ2] at ha2
    linarith
  have hKnn : (0 : ℝ) ≤ ((18 * E.M * E.N * C : ℕ) : ℝ) := Nat.cast_nonneg _
  -- the budget is smaller than 2 (δ a)²
  have hbudget : (18 * (E.M : ℝ) * (E.N : ℝ) * (levelCount F (2 * a) : ℝ)) <
      2 * (Gp.δ * a) ^ 2 := by
    have h1 := hC (2 * a) (by linarith)
    have h2 : 18 * (E.M : ℝ) * (E.N : ℝ) * (levelCount F (2 * a) : ℝ) ≤
        ((18 * E.M * E.N * C : ℕ) : ℝ) * (1 + 2 * a) := by
      have h3 : (0 : ℝ) ≤ 18 * (E.M : ℝ) * (E.N : ℝ) := by positivity
      have h4 := mul_le_mul_of_nonneg_left h1 h3
      push_cast
      nlinarith [h4]
    have h5 : ((18 * E.M * E.N * C : ℕ) : ℝ) * (1 + 2 * a) ≤
        3 * ((18 * E.M * E.N * C : ℕ) : ℝ) * a := by nlinarith
    have h6 : 3 * ((18 * E.M * E.N * C : ℕ) : ℝ) * a < 2 * (Gp.δ * a) ^ 2 := by
      have h7 : 3 * ((18 * E.M * E.N * C : ℕ) : ℝ) * a < (2 * Gp.δ ^ 2 * a) * a := by
        nlinarith
      nlinarith [h7]
    linarith
  -- outside the band the cokernel vanishes
  have hzero : ∀ j, j ∉ Gp.band a → finrank (ZMod 2) (coker F a j) = 0 := by
    intro j hj
    rcases Gp.gap a ha₀ hac h2a j hj with h0 | ⟨g₀, t, ht, hj₀, hj₁, hinj, hsurj⟩
    · exact finrank_coker_eq_zero fun z => by
        rw [h0 z]
        exact Submodule.zero_mem _
    · have hδa : 0 < Gp.δ * a := mul_pos Gp.δ_pos ha0
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hδa ht
      have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr fun h => by
        rw [h] at ht0
        exact lt_irrefl _ (by exact_mod_cast ht0)
      have hbig : (18 * (E.M : ℝ) * (E.N : ℝ) * (levelCount F (2 * a) : ℝ)) <
          2 * (t : ℝ) ^ 2 := by
        have h8 : (Gp.δ * a) ^ 2 ≤ (t : ℝ) ^ 2 := pow_le_pow_left₀ hδa.le ht 2
        linarith
      have hbigZ : 18 * (E.M : ℤ) * (E.N : ℤ) * (levelCount F (2 * a) : ℤ) <
          2 * (t : ℤ) ^ 2 := by exact_mod_cast hbig
      exact finrank_coker_eq_zero fun z =>
        gap_global E hn hfin ha0 h2a g₀ t ht1 hinj hsurj hbigZ j hj₀ hj₁ z
  -- the sum over the band
  have hsupp : (Function.support fun j : ℕ => finrank (ZMod 2) (coker F a j)) ⊆
      ↑(Gp.band a) := by
    intro j hj
    by_contra hjb
    exact hj (hzero j hjb)
  have hsum : defect F a = ∑ j ∈ Gp.band a, finrank (ZMod 2) (coker F a j) :=
    finsum_eq_sum_of_support_subset _ hsupp
  rw [hsum]
  calc ∑ j ∈ Gp.band a, finrank (ZMod 2) (coker F a j)
      ≤ ∑ _j ∈ Gp.band a, Gp.R := Finset.sum_le_sum fun j hj => Gp.band_rank a ha₀ hac h2a j hj
    _ = (Gp.band a).card * Gp.R := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ Gp.W * Gp.R := Nat.mul_le_mul_right _ (Gp.band_card a)

/-- The defect of a regular cut in an interval without critical levels is that of its lower
end. -/
theorem defect_eq_of_regular (F : ReversibleMetric n) (hn : 1 ≤ n) {x a : ℝ} (hx : 0 < x)
    (hxa : x ≤ a) (hreg : ∀ z ∈ Icc x a, z ∉ crit F) : defect F a = defect F x := by
  obtain ⟨D⟩ := Finsler.CrossingW.levelDeformation_of_regular F hn x a a hx hxa le_rfl hreg
  exact (defect_eq_of_levelDeformation F hxa D).symm

/-- With finitely many prime closed geodesic images the defect is bounded on the regular cuts
below any level. -/
theorem exists_defect_le_below (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) (x₁ : ℝ) :
    ∃ C : ℕ, ∀ a, 0 < a → a ≤ x₁ → a ∉ crit F → defect F a ≤ C := by
  -- a regular level above x₁
  have hx : ∃ x, max x₁ 1 ≤ x ∧ x ∉ crit F := by
    have hSfin : (crit F ∩ Icc (max x₁ 1) (max x₁ 1 + 1)).Finite := crit_finite F hfin _ _
    have hinf : (Icc (max x₁ 1) (max x₁ 1 + 1)).Infinite := Icc_infinite (by linarith)
    obtain ⟨x, hx, hxn⟩ := hinf.exists_notMem_finite hSfin
    exact ⟨x, hx.1, fun hc => hxn ⟨hc, hx⟩⟩
  obtain ⟨x, hx1, hxc⟩ := hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx1)
  have key := Finsler.NilpotentW.exists_of_levels F hfin
    (fun y _ => ∃ C : ℕ, ∀ a, 0 < a → a ≤ y → a ∉ crit F → defect F a ≤ C) ?_ ?_ ?_ x hx0 hxc
  · obtain ⟨_, C, hC⟩ := key
    exact ⟨C, fun a ha hax hac => hC a ha (hax.trans ((le_max_left _ _).trans hx1)) hac⟩
  · obtain ⟨b₀, hb₀, hzero⟩ := Finsler.SmallLevel.exists_HR_lev_eq_zero F
    refine ⟨b₀, hb₀, fun b _ hbb => ⟨0, fun a ha hab _ => ?_⟩⟩
    have h0 : ∀ j, finrank (ZMod 2) (coker F a j) = 0 := fun j =>
      finrank_coker_eq_zero fun z => by
        rw [hzero a ha (hab.trans hbb) j z]
        exact Submodule.zero_mem _
    have : defect F a = 0 := by
      unfold defect
      rw [finsum_congr h0, finsum_zero]
    exact this.le
  · rintro y y' hy hyy' hreg k ⟨C, hC⟩
    refine ⟨C, fun a ha hay' hac => ?_⟩
    by_cases hay : a ≤ y
    · exact hC a ha hay hac
    · have hya : y ≤ a := (not_le.mp hay).le
      rw [defect_eq_of_regular F hn hy hya fun z hz => hreg z ⟨hz.1, hz.2.trans hay'⟩]
      exact hC y hy le_rfl (hreg y ⟨le_rfl, hyy'⟩)
  · rintro y y' hy hyy' hyc hy'c hsub k ⟨C, hC⟩
    refine ⟨max C (defect F y'), fun a ha hay' hac => ?_⟩
    by_cases hay : a ≤ y
    · exact (hC a ha hay hac).trans (le_max_left _ _)
    · have hya : y ≤ a := (not_le.mp hay).le
      by_cases hlow : ∀ z ∈ Icc y a, z ∉ crit F
      · rw [defect_eq_of_regular F hn hy hya hlow]
        exact (hC y hy le_rfl hyc).trans (le_max_left _ _)
      · have hup : ∀ z ∈ Icc a y', z ∉ crit F := by
          intro z hz hzc
          apply hlow
          intro z' hz' hz'c
          have e : z' = z := hsub ⟨hz'c, hz'.1, hz'.2.trans hay'⟩ ⟨hzc, hya.trans hz.1, hz.2⟩
          have hza : z = a := le_antisymm (e ▸ hz'.2) hz.1
          exact hac (hza ▸ hzc)
        rw [← defect_eq_of_regular F hn ha hay' hup]
        exact le_max_right _ _

/-- With finitely many prime closed geodesic images, a regular cut is the lower end of an
interval without critical levels whose upper end has a regular double. -/
theorem exists_regular_double (F : ReversibleMetric n) (hfin : (primeImages F).Finite) {a : ℝ}
    (hac : a ∉ crit F) :
    ∃ a' : ℝ, a ≤ a' ∧ (∀ z ∈ Icc a a', z ∉ crit F) ∧ 2 * a' ∉ crit F := by
  obtain ⟨b, hab, hreg⟩ := exists_regular_above F hfin hac
  have hSfin : ((fun z : ℝ => z / 2) '' (crit F ∩ Icc (2 * a) (2 * b))).Finite :=
    (crit_finite F hfin _ _).image _
  have hinf : (Icc a b).Infinite := Icc_infinite hab
  obtain ⟨a', ha', hn'⟩ := hinf.exists_notMem_finite hSfin
  refine ⟨a', ha'.1, fun z hz => hreg z ⟨hz.1, hz.2.trans ha'.2⟩, fun hc => hn' ?_⟩
  exact ⟨2 * a', ⟨hc, by linarith [ha'.1], by linarith [ha'.2]⟩, by ring⟩

/-- With finitely many prime closed geodesic images, the local bounds for single crossings and
the gap structure at large cuts, the defect is bounded on all positive regular cuts. -/
theorem exists_defect_le (E : EventBounds F) (Gp : GapInputs F) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ C : ℕ, ∀ a, 0 < a → a ∉ crit F → defect F a ≤ C := by
  obtain ⟨a₁, ha₁, hlarge⟩ := exists_defect_le_large E Gp hn hfin
  obtain ⟨C₁, hC₁⟩ := exists_defect_le_below F hn hfin a₁
  refine ⟨max C₁ (Gp.W * Gp.R), fun a ha hac => ?_⟩
  by_cases haa : a ≤ a₁
  · exact (hC₁ a ha haa hac).trans (le_max_left _ _)
  · obtain ⟨a', haa', hreg, h2a'⟩ := exists_regular_double F hfin hac
    rw [← defect_eq_of_regular F hn ha haa' hreg]
    exact (hlarge a' ((not_le.mp haa).le.trans haa') (hreg a' ⟨haa', le_rfl⟩) h2a').trans
      (le_max_right _ _)

end

end Finsler.DefectBound
