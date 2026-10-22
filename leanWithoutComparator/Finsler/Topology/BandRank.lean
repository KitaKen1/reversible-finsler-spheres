module

public import Finsler.Topology.CutFinite
public import Finsler.Topology.CrossingSupport
public import Finsler.Topology.Defect

/-! Counting the dimension of the reflection Borel cohomology of a cut by its crossings (source
(9.8)). An exact sequence A → B → C of finite-dimensional spaces gives dim B ≤ dim A + dim C; so
across two regular cuts a ≤ b the dimension of the reflection Borel cohomology of (t_b, M) in a
degree is at most that of (t_a, M) plus that of the crossing pair. With finitely many prime
closed geodesic images, let `act` be a set of levels such that the reflection crossing group of
a single crossing vanishes in degree j when its critical level is not in `act`, and has
dimension at most C in general. Then the reflection Borel cohomology of (t_a, M) in degree j has
dimension at most C times the number of critical levels of `act` below a, and so has the
cokernel of global restriction. By the sign sequence the dimension of the reflection Borel
cohomology in degree j is at most the sum of the dimensions of the ordinary cohomology in the
degrees up to j, which bounds the cokernel in low degrees by ordinary ranks. The local
statements for single crossings and the ordinary ranks are hypotheses. -/

@[expose] public section

namespace Finsler.BandRank

open Set Module Finsler.BorelCochain Finsler.BorelLoop Finsler.BorelCrossing Finsler.Geometry
open Finsler.Geodesics Finsler.CriticalLevels

/-- An exact sequence of finite-dimensional spaces bounds the dimension of the middle term. -/
theorem finrank_le_of_exact {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module (ZMod 2) A] [Module (ZMod 2) B] [Module (ZMod 2) C] [Module.Finite (ZMod 2) A]
    [Module.Finite (ZMod 2) B] [Module.Finite (ZMod 2) C] (f : A →ₗ[ZMod 2] B)
    (g : B →ₗ[ZMod 2] C) (h : ∀ x, g x = 0 → ∃ z, f z = x) :
    finrank (ZMod 2) B ≤ finrank (ZMod 2) A + finrank (ZMod 2) C := by
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 : LinearMap.ker g ≤ LinearMap.range f := fun x hx => h x (LinearMap.mem_ker.mp hx)
  have h3 := Submodule.finrank_mono h2
  have h4 := LinearMap.finrank_range_le f
  have h5 := Submodule.finrank_le (LinearMap.range g)
  omega

variable {n : ℕ} (F : ReversibleMetric n)

/-- Across two regular cuts the dimension of the reflection Borel cohomology grows at most by
the dimension of the crossing group. -/
theorem finrank_lev_le_cross (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hac : a ∉ crit F) (hbc : b ∉ crit F) (j : ℕ) :
    finrank (ZMod 2) (HR (levComplex F b) j) ≤
      finrank (ZMod 2) (HR (crossComplex F hab) j) + finrank (ZMod 2) (HR (levComplex F a) j) := by
  obtain ⟨-, hfa, -⟩ := FiniteCut.exists_finite_HR F hn hfin ha hac
  obtain ⟨-, hfb, -⟩ := FiniteCut.exists_finite_HR F hn hfin (ha.trans_le hab) hbc
  have := hfa j
  have := hfb j
  have : Module.Finite (ZMod 2) (HR (crossComplex F hab) j) :=
    CutFinite.finite_sub (shortExact F hab) j hfa (hfb j)
  exact finrank_le_of_exact (HRmap (relHom F hab) j) (HRmap (cutHom F hab) j)
    fun x hx => exact_crossing F hab j x hx

/-- With finitely many prime closed geodesic images: if the reflection crossing groups of single
crossings below the regular cut a have dimension at most C in degree j, and vanish in degree j
when no critical level of the crossing lies in `act`, the reflection Borel cohomology of
(t_a, M) in degree j has dimension at most C times the number of critical levels of `act`
in [0, a]. -/
theorem finrank_lev_le (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (act : Set ℝ) (C j : ℕ)
    {a : ℝ} (ha : 0 < a) (hac : a ∉ crit F)
    (hcr : ∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → b' ≤ a → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton →
      finrank (ZMod 2) (HR (crossComplex F hab') j) ≤ C ∧
        ((∀ l ∈ crit F ∩ Icc a' b', l ∉ act) → ∀ z : HR (crossComplex F hab') j, z = 0)) :
    finrank (ZMod 2) (HR (levComplex F a) j) ≤ C * (crit F ∩ Icc 0 a ∩ act).ncard := by
  have hfinite : ∀ b : ℝ, (crit F ∩ Icc 0 b ∩ act).Finite := fun b =>
    (crit_finite F hfin 0 b).subset inter_subset_left
  have hmono : ∀ {a' b' : ℝ}, a' ≤ b' →
      (crit F ∩ Icc 0 a' ∩ act).ncard ≤ (crit F ∩ Icc 0 b' ∩ act).ncard := fun {a' b'} h =>
    ncard_le_ncard (fun l hl => ⟨⟨hl.1.1, hl.1.2.1, hl.1.2.2.trans h⟩, hl.2⟩) (hfinite b')
  have key := LevelCount.forall_levelCount F hfin
    (fun b _ => b ≤ a →
      finrank (ZMod 2) (HR (levComplex F b) j) ≤ C * (crit F ∩ Icc 0 b ∩ act).ncard)
    (by
      obtain ⟨b₀, hb₀, hzero⟩ := SmallLevel.exists_HR_lev_eq_zero F
      refine ⟨b₀, hb₀, fun b hb hbb _ => ?_⟩
      have : Subsingleton (HR (levComplex F b) j) :=
        ⟨fun x y => (hzero b hb hbb j x).trans (hzero b hb hbb j y).symm⟩
      rw [finrank_zero_of_subsingleton]
      exact Nat.zero_le _)
    (fun a' b' ha' ha'b' hreg _ ih hb'a => by
      obtain ⟨D⟩ := CrossingW.levelDeformation_of_regular F hn a' b' b' ha' ha'b' le_rfl hreg
      have hbij := RegularInterval.cut_bijective_of_levelDeformation F ha'b' D j
      rw [(LinearEquiv.ofBijective (HRmap (cutHom F ha'b') j) hbij).finrank_eq]
      exact (ih (ha'b'.trans hb'a)).trans (Nat.mul_le_mul_left C (hmono ha'b')))
    (fun a' b' ha' ha'b' ha'c hb'c hsub _ ih hb'a => by
      obtain ⟨hC, hzero⟩ := hcr a' b' ha'b' ha' hb'a ha'c hb'c hsub
      have h1 := finrank_lev_le_cross F hn hfin ha' ha'b' ha'c hb'c j
      have h2 := ih (ha'b'.trans hb'a)
      by_cases hact : ∀ l ∈ crit F ∩ Icc a' b', l ∉ act
      · have : Subsingleton (HR (crossComplex F ha'b') j) :=
          ⟨fun x y => (hzero hact x).trans (hzero hact y).symm⟩
        have h0 : finrank (ZMod 2) (HR (crossComplex F ha'b') j) = 0 :=
          finrank_zero_of_subsingleton
        rw [h0, zero_add] at h1
        exact (h1.trans h2).trans (Nat.mul_le_mul_left C (hmono ha'b'))
      · obtain ⟨l, hl, hlact⟩ : ∃ l ∈ crit F ∩ Icc a' b', l ∈ act := by
          by_contra hcon
          exact hact fun l hl hla => hcon ⟨l, hl, hla⟩
        have hla' : a' < l := lt_of_le_of_ne hl.2.1 fun h => ha'c (h ▸ hl.1)
        have hnot : l ∉ crit F ∩ Icc 0 a' ∩ act := fun h => not_le.mpr hla' h.1.2.2
        have hins : insert l (crit F ∩ Icc 0 a' ∩ act) ⊆ crit F ∩ Icc 0 b' ∩ act := by
          intro x hx
          rcases hx with rfl | hx
          · exact ⟨⟨hl.1, ha'.le.trans hl.2.1, hl.2.2⟩, hlact⟩
          · exact ⟨⟨hx.1.1, hx.1.2.1, hx.1.2.2.trans ha'b'⟩, hx.2⟩
        have hcount : (crit F ∩ Icc 0 a' ∩ act).ncard + 1 ≤ (crit F ∩ Icc 0 b' ∩ act).ncard := by
          rw [← ncard_insert_of_notMem hnot (hfinite a')]
          exact ncard_le_ncard hins (hfinite b')
        calc finrank (ZMod 2) (HR (levComplex F b') j)
            ≤ C + C * (crit F ∩ Icc 0 a' ∩ act).ncard := by omega
          _ = C * ((crit F ∩ Icc 0 a' ∩ act).ncard + 1) := by ring
          _ ≤ C * (crit F ∩ Icc 0 b' ∩ act).ncard := Nat.mul_le_mul_left C hcount)
    a ha hac
  exact key le_rfl

/-- The dimension of the reflection Borel cohomology in degree j is at most the sum of the
dimensions of the ordinary cohomology in the degrees up to j (sign sequence). -/
theorem finrank_HR_le_sum (K : InvComplex) (hH : ∀ q, Module.Finite (ZMod 2) (H K q)) (j : ℕ) :
    finrank (ZMod 2) (HR K j) ≤ ∑ i ∈ Finset.range (j + 1), finrank (ZMod 2) (H K i) := by
  induction j with
  | zero =>
    have := hH 0
    rw [Finset.sum_range_one]
    exact LinearMap.finrank_le_finrank_of_injective (BorelQuasiIso.forget_zero_injective K)
  | succ j ih =>
    have := hH (j + 1)
    have := FiniteCut.finite_HR K hH j
    have := FiniteCut.finite_HR K hH (j + 1)
    have h := finrank_le_of_exact (w K j) (forget K (j + 1))
      fun x hx => (exact_forget K j x).mp hx
    rw [Finset.sum_range_succ]
    omega

/-- With finitely many prime closed geodesic images: if the ordinary cohomology of (t_a, M) at a
regular cut has dimension at most R₀ in the degrees up to j, the cokernel of global restriction
in degree j has dimension at most (j + 1) R₀. -/
theorem finrank_coker_le (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (hac : a ∉ crit F) (j R₀ : ℕ)
    (hR : ∀ i, i ≤ j → finrank (ZMod 2) (H (levComplex F a) i) ≤ R₀) :
    finrank (ZMod 2) (Defect.coker F a j) ≤ (j + 1) * R₀ := by
  obtain ⟨-, hH, -⟩ := FiniteCut.exists_finite_H F hn hfin ha hac
  have := FiniteCut.finite_HR (levComplex F a) hH j
  have h1 : finrank (ZMod 2) (Defect.coker F a j) ≤ finrank (ZMod 2) (HR (levComplex F a) j) :=
    Submodule.finrank_quotient_le _
  have h2 := finrank_HR_le_sum (levComplex F a) hH j
  have h3 : ∑ i ∈ Finset.range (j + 1), finrank (ZMod 2) (H (levComplex F a) i) ≤
      (j + 1) * R₀ := by
    have h := Finset.sum_le_card_nsmul (Finset.range (j + 1))
      (fun i => finrank (ZMod 2) (H (levComplex F a) i)) R₀
      (fun i hi => hR i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))
    rwa [Finset.card_range, smul_eq_mul] at h
  omega

/-- With finitely many prime closed geodesic images: under the hypotheses of `finrank_lev_le`
the cokernel of global restriction in degree j has dimension at most C times the number of
critical levels of `act` in [0, a]. -/
theorem finrank_coker_le_count (hn : 1 ≤ n) (hfin : (primeImages F).Finite) (act : Set ℝ)
    (C j : ℕ) {a : ℝ} (ha : 0 < a) (hac : a ∉ crit F)
    (hcr : ∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → b' ≤ a → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton →
      finrank (ZMod 2) (HR (crossComplex F hab') j) ≤ C ∧
        ((∀ l ∈ crit F ∩ Icc a' b', l ∉ act) → ∀ z : HR (crossComplex F hab') j, z = 0)) :
    finrank (ZMod 2) (Defect.coker F a j) ≤ C * (crit F ∩ Icc 0 a ∩ act).ncard := by
  obtain ⟨-, hf, -⟩ := FiniteCut.exists_finite_HR F hn hfin ha hac
  have := hf j
  exact (Submodule.finrank_quotient_le _).trans (finrank_lev_le F hn hfin act C j ha hac hcr)

/-- A uniform bound for the cokernel of global restriction in every degree, from local ranks.
With finitely many prime closed geodesic images, let the reflection crossing groups of single
crossings have dimension at most C in the degrees above `jlow` and vanish there when no
critical level of the crossing is active for the degree, let at most K critical levels be
active for each such degree, and let the ordinary cohomology of large regular cuts have
dimension at most R₀ in the degrees up to `jlow`. Then the cokernel of global restriction of a
large regular cut has dimension at most max ((jlow + 1) R₀) (C K) in every degree. -/
theorem finrank_coker_le_max (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a₀ : ℝ}
    (ha₀ : 0 < a₀) (C K jlow R₀ : ℕ) (act : ℕ → Set ℝ)
    (hcr : ∀ j : ℕ, jlow < j → ∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → a' ∉ crit F →
      b' ∉ crit F → (crit F ∩ Icc a' b').Subsingleton →
      finrank (ZMod 2) (HR (crossComplex F hab') j) ≤ C ∧
        ((∀ l ∈ crit F ∩ Icc a' b', l ∉ act j) → ∀ z : HR (crossComplex F hab') j, z = 0))
    (hcount : ∀ j : ℕ, jlow < j → ∀ a : ℝ, (crit F ∩ Icc 0 a ∩ act j).ncard ≤ K)
    (hlow : ∀ a : ℝ, a₀ ≤ a → a ∉ crit F → ∀ i : ℕ, i ≤ jlow →
      finrank (ZMod 2) (H (levComplex F a) i) ≤ R₀)
    {a : ℝ} (ha : a₀ ≤ a) (hac : a ∉ crit F) (j : ℕ) :
    finrank (ZMod 2) (Defect.coker F a j) ≤ max ((jlow + 1) * R₀) (C * K) := by
  have ha0 : 0 < a := ha₀.trans_le ha
  by_cases hj : j ≤ jlow
  · have h := finrank_coker_le F hn hfin ha0 hac j R₀ fun i hi => hlow a ha hac i (hi.trans hj)
    exact (h.trans (Nat.mul_le_mul_right R₀ (Nat.succ_le_succ hj))).trans (le_max_left _ _)
  · have hj' : jlow < j := not_le.mp hj
    have h := finrank_coker_le_count F hn hfin (act j) C j ha0 hac
      fun a' b' hab' ha' _ ha'c hb'c hsub => hcr j hj' a' b' hab' ha' ha'c hb'c hsub
    exact (h.trans (Nat.mul_le_mul_left C (hcount j hj' a))).trans (le_max_right _ _)

end Finsler.BandRank
