module

public import Finsler.Topology.DoublingBudget
public import Finsler.Topology.EndgameLevels

/-! The doubling budgets of the final section from a global basis. A global basis, in the form
used here, consists of at most one bottom class and one top class of the reflection Borel
cohomology of (Λ, M) in every degree, which span it, together with a set of degrees (the bottom
degrees of the odd stages) such that

* every bottom class is the forgetful image of a global K-class, and for an odd degree of one
  annihilated by a fixed power of U = v(v + w);
* the top class of degree n + q, q odd, is the evaluation cup of the bottom class of degree q;
* every other top class is the forgetful image of a global K-class;
* the degrees (4t + 1)(n − 1) are odd and their bottom classes are nonzero.

At a regular cut 2a, with finitely many prime closed geodesic images, let b_q be one when the
bottom class of the odd degree q is nonzero on t_{2a}, and p_q one when the top class of degree
n + q is not a multiple of the bottom class of that degree there. Then the total rank of the
restriction of global reflection classes to t_{2a} is at most the total dimension of the
forgetful images of the restricted global K-classes plus Σ p_q, and Σ b_q is at most the total
dimension of the forgetful images of the restricted global K-classes annihilated by the power of
U. These are the two rank statements of `DoublingBudget`, so the numbers satisfy the doubling
formula between a and 2a. Hence a global basis, a bound for the defect and a detection band give
the level inputs of the final section, and are contradictory when there are finitely many prime
closed geodesic images. The global basis, the bound and the detection band are not proved. -/

@[expose] public section

namespace Finsler.BasisBudget

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelLoop Finsler.BorelCochain
open Finsler.CriticalLevels Finsler.BorelIterate Finsler.BorelK Finsler.FiniteCut
open Finsler.BorelCoverK Finsler.TorsionK Finsler.DoublingBudget
open Finsler.BorelCanonicalEvaluation Finsler.EndgameAssembly Finsler.EndgameLevels

noncomputable section

/-! ### The forgetful map to the inner Borel cohomology -/

section Forget

variable {K L : InvComplex} (S : Commuting K)

/-- The forgetful map from the Borel cohomology of an iterated complex to the Borel cohomology of
the inner complex. -/
def fgtR (q : ℕ) : HR (borelInv S) q →ₗ[ZMod 2] HR K q :=
  (cohomologyEquiv S q).toLinearMap ∘ₗ forget (borelInv S) q

theorem fgtR_apply (q : ℕ) (z : HR (borelInv S) q) :
    fgtR S q z = cohomologyEquiv S q (forget (borelInv S) q z) := rfl

variable {SK : Commuting K} {SL : Commuting L} (Φ : CommHom SK SL)

/-- The forgetful map is natural. -/
theorem fgtR_natural (q : ℕ) (z : HR (borelInv SK) q) :
    fgtR SL q (HRmap (borelHom Φ) q z) = HRmap Φ.φ q (fgtR SK q z) := by
  rw [fgtR_apply, fgtR_apply, ← Hmap_forget, cohomologyEquiv_natural]

end Forget

/-! ### A sum over shifted degrees -/

/-- A sum over the degrees n + i, i in a set of degrees up to D, bounds the corresponding sum
over the degrees up to D. -/
theorem sum_shift_le (odd : ℕ → Prop) [DecidablePred odd] (P : ℕ → ℕ) (n D : ℕ) :
    ∑ q ∈ Finset.range (D + 1), (if n ≤ q ∧ odd (q - n) then P q else 0) ≤
      ∑ i ∈ (Finset.range (D + 1)).filter odd, P (n + i) := by
  rw [← Finset.sum_filter,
    ← Finset.sum_image (f := P) (g := fun i => n + i) (s := (Finset.range (D + 1)).filter odd)
      (fun i _ j _ h => Nat.add_left_cancel h)]
  refine Finset.sum_le_sum_of_subset fun q hq => ?_
  obtain ⟨hq1, hq2, hq3⟩ := Finset.mem_filter.mp hq
  have hq4 := Finset.mem_range.mp hq1
  exact Finset.mem_image.mpr ⟨q - n,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq3⟩, Nat.add_sub_of_le hq2⟩

/-! ### The basis -/

/-- A global basis of the reflection Borel cohomology of (Λ, M) with its K-lifts, in the form
used for the doubling budgets. -/
structure Data (n : ℕ) (hn : 1 ≤ n) where
  /-- the bottom class of degree q, zero if there is none -/
  bot : ∀ q, HR (fullComplex n) q
  /-- the top class of degree q, zero if there is none -/
  top : ∀ q, HR (fullComplex n) q
  /-- the bottom degrees of the odd stages -/
  odd : ℕ → Prop
  /-- the power of U annihilating the lifts of the odd bottoms -/
  torsion : ℕ
  span : ∀ q (x : HR (fullComplex n) q), ∃ c c' : ZMod 2, x = c • bot q + c' • top q
  top_eq : ∀ q, odd q → top (n + q) = fullE n hn q (bot q)
  lift_bot : ∀ q, ∃ z : HR (kFull n) q, fgtR (halfCommutingFull n) q z = bot q
  lift_odd : ∀ q, odd q → ∃ z : HR (kFull n) q,
    Ann (halfCommutingFull n) torsion q z ∧ fgtR (halfCommutingFull n) q z = bot q
  lift_top : ∀ q, (∀ q', odd q' → q ≠ n + q') →
    ∃ z : HR (kFull n) q, fgtR (halfCommutingFull n) q z = top q
  odd_mem : ∀ t : ℕ, odd ((4 * t + 1) * (n - 1))
  bot_ne : ∀ t : ℕ, bot ((4 * t + 1) * (n - 1)) ≠ 0

variable {n : ℕ} {hn : 1 ≤ n} (F : ReversibleMetric n) (G : Data n hn) (c : ℝ)

/-! ### The numbers of a cut -/

open Classical in
/-- One if the bottom class of degree q is nonzero on t_c, zero otherwise. -/
def bottomNum (q : ℕ) : ℕ := if HRmap (resHom F c) q (G.bot q) = 0 then 0 else 1

open Classical in
/-- Zero if the top class of degree q is a multiple of the bottom class of degree q on t_c, one
otherwise. -/
def partnerNum (q : ℕ) : ℕ :=
  if HRmap (resHom F c) q (G.top q) ∈
    Submodule.span (ZMod 2) {HRmap (resHom F c) q (G.bot q)} then 0 else 1

theorem bottomNum_of_eq (q : ℕ) (h : HRmap (resHom F c) q (G.bot q) = 0) :
    bottomNum F G c q = 0 := ite_eq_left h

theorem bottomNum_of_ne (q : ℕ) (h : HRmap (resHom F c) q (G.bot q) ≠ 0) :
    bottomNum F G c q = 1 := ite_eq_right h

theorem partnerNum_of_mem (q : ℕ) (h : HRmap (resHom F c) q (G.top q) ∈
    Submodule.span (ZMod 2) {HRmap (resHom F c) q (G.bot q)}) : partnerNum F G c q = 0 :=
  ite_eq_left h

theorem partnerNum_of_not_mem (q : ℕ) (h : HRmap (resHom F c) q (G.top q) ∉
    Submodule.span (ZMod 2) {HRmap (resHom F c) q (G.bot q)}) : partnerNum F G c q = 1 :=
  ite_eq_right h

theorem partnerNum_le_one (q : ℕ) : partnerNum F G c q ≤ 1 := by
  by_cases h : HRmap (resHom F c) q (G.top q) ∈
      Submodule.span (ZMod 2) {HRmap (resHom F c) q (G.bot q)}
  · rw [partnerNum_of_mem F G c q h]
    exact Nat.zero_le 1
  · rw [partnerNum_of_not_mem F G c q h]

/-- If the evaluation cup of the restricted bottom class of an odd degree q vanishes, the
partner number of degree n + q is zero. -/
theorem partnerNum_eq_zero_of_levE (q : ℕ) (hq : G.odd q)
    (h : levE F c hn q (HRmap (resHom F c) q (G.bot q)) = 0) :
    partnerNum F G c (n + q) = 0 := by
  apply partnerNum_of_mem
  have e : HRmap (resHom F c) (n + q) (G.top (n + q)) = 0 := by
    rw [G.top_eq q hq, fullE_res, h]
  rw [e]
  exact Submodule.zero_mem _

/-- The partner number of degree n + q is at most the bottom number of the odd degree q. -/
theorem partnerNum_le_bottomNum (q : ℕ) (hq : G.odd q) :
    partnerNum F G c (n + q) ≤ bottomNum F G c q := by
  by_cases h : HRmap (resHom F c) q (G.bot q) = 0
  · have e : levE F c hn q (HRmap (resHom F c) q (G.bot q)) = 0 := by
      rw [h, map_zero]
    rw [partnerNum_eq_zero_of_levE F G c q hq e]
    exact Nat.zero_le _
  · rw [bottomNum_of_ne F G c q h]
    exact partnerNum_le_one F G c (n + q)

/-! ### Restrictions of forgetful images -/

/-- The restriction to t_c of the forgetful image of a global K-class is the forgetful image of
its restriction. -/
theorem res_fgtR (q : ℕ) (z : HR (kFull n) q) :
    HRmap (resHom F c) q (fgtR (halfCommutingFull n) q z) =
      forgetTargetEquiv F c q
        (forget (kComplex F c) q (HRmap (borelHom (resComm F c)) q z)) :=
  (fgtR_natural (resComm F c) q z).symm

/-- The bottom number of an odd degree is at most the dimension of the forgetful image of the
restricted global K-classes annihilated by the power of U. -/
theorem bottomNum_le (q : ℕ) (hfinH : Module.Finite (ZMod 2) (H (kComplex F c) q))
    (hq : G.odd q) :
    bottomNum F G c q ≤ finrank (ZMod 2)
      (((annSub (halfCommutingFull n) G.torsion q).map
        (HRmap (borelHom (resComm F c)) q)).map (forget (kComplex F c) q)) := by
  by_cases h : HRmap (resHom F c) q (G.bot q) = 0
  · rw [bottomNum_of_eq F G c q h]
    exact Nat.zero_le _
  · rw [bottomNum_of_ne F G c q h]
    obtain ⟨z, hz, hzb⟩ := G.lift_odd q hq
    have hz' : z ∈ annSub (halfCommutingFull n) G.torsion q := hz
    have hy : forget (kComplex F c) q (HRmap (borelHom (resComm F c)) q z) ≠ 0 := by
      intro h0
      apply h
      rw [← hzb, res_fgtR, h0]
      exact (forgetTargetEquiv F c q).map_zero
    exact Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨_, Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hz')⟩,
        fun h0 => hy (congrArg Subtype.val h0)⟩

/-- In every degree the rank of the restriction of global reflection classes to t_c is at most
the dimension of the forgetful image of the restricted global K-classes, plus the partner number
if the degree is n + q' for an odd degree q'. -/
theorem finrank_range_le (q : ℕ) (hfinR : Module.Finite (ZMod 2) (HR (levComplex F c) q))
    [Decidable (n ≤ q ∧ G.odd (q - n))] :
    finrank (ZMod 2) (LinearMap.range (HRmap (resHom F c) q)) ≤
      finrank (ZMod 2) ((LinearMap.range (HRmap (borelHom (resComm F c)) q)).map
        (forget (kComplex F c) q)) +
        (if n ≤ q ∧ G.odd (q - n) then partnerNum F G c q else 0) := by
  obtain ⟨W, hW⟩ : ∃ W : Submodule (ZMod 2) (HR (levComplex F c) q),
      W = ((LinearMap.range (HRmap (borelHom (resComm F c)) q)).map
        (forget (kComplex F c) q)).map (forgetTargetEquiv F c q).toLinearMap := ⟨_, rfl⟩
  have hfr : finrank (ZMod 2) W = finrank (ZMod 2)
      ((LinearMap.range (HRmap (borelHom (resComm F c)) q)).map (forget (kComplex F c) q)) := by
    rw [hW]
    exact LinearEquiv.finrank_map_eq (forgetTargetEquiv F c q) _
  have hmem : ∀ z : HR (kFull n) q,
      HRmap (resHom F c) q (fgtR (halfCommutingFull n) q z) ∈ W := by
    intro z
    rw [hW, res_fgtR]
    exact ⟨_, Submodule.mem_map_of_mem (LinearMap.mem_range_self _ z), rfl⟩
  have hbot : HRmap (resHom F c) q (G.bot q) ∈ W := by
    obtain ⟨z, hz⟩ := G.lift_bot q
    rw [← hz]
    exact hmem z
  have hspan : ∀ S : Submodule (ZMod 2) (HR (levComplex F c) q),
      HRmap (resHom F c) q (G.bot q) ∈ S → HRmap (resHom F c) q (G.top q) ∈ S →
      LinearMap.range (HRmap (resHom F c) q) ≤ S := by
    rintro S hb ht _ ⟨y, rfl⟩
    obtain ⟨a, a', rfl⟩ := G.span q y
    rw [map_add, map_smul, map_smul]
    exact S.add_mem (S.smul_mem a hb) (S.smul_mem a' ht)
  by_cases hodd : n ≤ q ∧ G.odd (q - n)
  · rw [ite_eq_left hodd]
    by_cases hp : HRmap (resHom F c) q (G.top q) ∈
        Submodule.span (ZMod 2) {HRmap (resHom F c) q (G.bot q)}
    · have h1 : LinearMap.range (HRmap (resHom F c) q) ≤ W :=
        hspan W hbot ((Submodule.span_singleton_le_iff_mem _ _).mpr hbot hp)
      have h2 := Submodule.finrank_mono h1
      omega
    · have hne : HRmap (resHom F c) q (G.top q) ≠ 0 := fun h0 =>
        hp (h0 ▸ Submodule.zero_mem _)
      have h1 : LinearMap.range (HRmap (resHom F c) q) ≤
          W ⊔ Submodule.span (ZMod 2) {HRmap (resHom F c) q (G.top q)} :=
        hspan _ (Submodule.mem_sup_left hbot)
          (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
      have h2 := Submodule.finrank_mono h1
      have h3 := Submodule.finrank_add_le_finrank_add_finrank W
        (Submodule.span (ZMod 2) {HRmap (resHom F c) q (G.top q)})
      have h4 := finrank_span_singleton (K := ZMod 2) hne
      have h5 := partnerNum_of_not_mem F G c q hp
      omega
  · rw [ite_eq_right hodd, add_zero]
    have hlift : ∀ q', G.odd q' → q ≠ n + q' := by
      intro q' hq' hqq
      apply hodd
      rw [hqq, Nat.add_sub_cancel_left]
      exact ⟨Nat.le_add_right n q', hq'⟩
    obtain ⟨z, hz⟩ := G.lift_top q hlift
    have htop : HRmap (resHom F c) q (G.top q) ∈ W := by
      rw [← hz]
      exact hmem z
    have h2 := Submodule.finrank_mono (hspan W hbot htop)
    omega

/-! ### The doubling data of a cut -/

/-- With finitely many prime closed geodesic images and a global basis, at a regular cut 2a
there are numbers satisfying the doubling formula between a and 2a, in which the bottom number
of an odd degree is one if its bottom class is nonzero on t_{2a}, and the partner number is zero
if the evaluation cup of that restricted bottom class vanishes. -/
theorem exists_data (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ s : Finsler.PartnerRank.Data ℕ,
      s.T = (Defect.defect F a : ℤ) ∧ s.Tdouble = (Defect.defect F (2 * a) : ℤ) ∧
      (∀ q, G.odd q → HRmap (resHom F (2 * a)) q (G.bot q) ≠ 0 →
        q ∈ s.labels ∧ s.bottom q = 1) ∧
      (∀ q, G.odd q →
        levE F (2 * a) hn q (HRmap (resHom F (2 * a)) q (G.bot q)) = 0 → s.partner q ≤ 0) := by
  classical
  have h2 : 0 < 2 * a := by linarith
  obtain ⟨Q₀, hb⟩ := exists_budget F hn hfin ha h2a
  obtain ⟨Q, hfinR, hzeroR⟩ := exists_finite_HR F hn hfin h2 h2a
  have hfinH : ∀ q, Module.Finite (ZMod 2) (H (kComplex F (2 * a)) q) := fun q => by
    have := hfinR q
    exact Module.Finite.equiv (forgetTargetEquiv F (2 * a) q).symm
  obtain ⟨D, hD⟩ : ∃ D, D = Q₀ + Q := ⟨_, rfl⟩
  have hNn : ∑ i ∈ (Finset.range (D + 1)).filter G.odd, bottomNum F G (2 * a) i ≤
      ∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
        (((annSub (halfCommutingFull n) G.torsion q).map
          (HRmap (borelHom (resComm F (2 * a))) q)).map
            (forget (kComplex F (2 * a)) q)) :=
    (Finset.sum_le_sum fun i hi =>
      bottomNum_le F G (2 * a) i (hfinH i) (Finset.mem_filter.mp hi).2).trans
      (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
  have hVn : ∑ q ∈ Finset.range (D + 1),
        finrank (ZMod 2) (LinearMap.range (HRmap (resHom F (2 * a)) q)) ≤
      ∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
          ((LinearMap.range (HRmap (borelHom (resComm F (2 * a))) q)).map
            (forget (kComplex F (2 * a)) q)) +
        ∑ i ∈ (Finset.range (D + 1)).filter G.odd, partnerNum F G (2 * a) (n + i) := by
    refine (Finset.sum_le_sum fun q _ => finrank_range_le F G (2 * a) q (hfinR q)).trans ?_
    rw [Finset.sum_add_distrib]
    exact Nat.add_le_add_left
      (sum_shift_le G.odd (fun q => partnerNum F G (2 * a) q) n D) _
  have hpb : ∀ i ∈ (Finset.range (D + 1)).filter G.odd,
      ((partnerNum F G (2 * a) (n + i) : ℕ) : ℤ) ≤ ((bottomNum F G (2 * a) i : ℕ) : ℤ) :=
    fun i hi => Nat.cast_le.mpr
      (partnerNum_le_bottomNum F G (2 * a) i (Finset.mem_filter.mp hi).2)
  have hN : ∑ i ∈ (Finset.range (D + 1)).filter G.odd, ((bottomNum F G (2 * a) i : ℕ) : ℤ) ≤
      ((∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
        (((annSub (halfCommutingFull n) G.torsion q).map
          (HRmap (borelHom (resComm F (2 * a))) q)).map
            (forget (kComplex F (2 * a)) q)) : ℕ) : ℤ) := by
    exact_mod_cast hNn
  have hV : ((∑ q ∈ Finset.range (D + 1),
        finrank (ZMod 2) (LinearMap.range (HRmap (resHom F (2 * a)) q)) : ℕ) : ℤ) ≤
      ((∑ q ∈ Finset.range (D + 1), finrank (ZMod 2)
          ((LinearMap.range (HRmap (borelHom (resComm F (2 * a))) q)).map
            (forget (kComplex F (2 * a)) q)) : ℕ) : ℤ) +
        ∑ i ∈ (Finset.range (D + 1)).filter G.odd,
          ((partnerNum F G (2 * a) (n + i) : ℕ) : ℤ) := by
    exact_mod_cast hVn
  obtain ⟨s, hl, hbt, hpt, hT, hTd⟩ := hb D (by omega) (ι := ℕ)
    ((Finset.range (D + 1)).filter G.odd) (fun i => ((bottomNum F G (2 * a) i : ℕ) : ℤ))
    (fun i => ((partnerNum F G (2 * a) (n + i) : ℕ) : ℤ)) G.torsion hpb hN hV
  refine ⟨s, hT, hTd, fun q hq hne => ⟨?_, ?_⟩, fun q hq he => ?_⟩
  · have hqD : q ≤ D := by
      by_contra hcon
      exact hne (hzeroR q (by omega) _)
    rw [hl]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩
  · rw [hbt]
    change ((bottomNum F G (2 * a) q : ℕ) : ℤ) = 1
    rw [bottomNum_of_ne F G (2 * a) q hne, Nat.cast_one]
  · rw [hpt]
    change ((partnerNum F G (2 * a) (n + q) : ℕ) : ℤ) ≤ 0
    rw [partnerNum_eq_zero_of_levE F G (2 * a) q hq he, Nat.cast_zero]

/-- The doubling data at a regular cut x, between x/2 and x. -/
theorem exists_data_cut (hfin : (primeImages F).Finite) {x : ℝ} (hx : 0 < x)
    (hreg : x ∉ crit F) :
    ∃ s : Finsler.PartnerRank.Data ℕ,
      s.T = (Defect.defect F (x / 2) : ℤ) ∧ s.Tdouble = (Defect.defect F x : ℤ) ∧
      (∀ q, G.odd q → HRmap (resHom F x) q (G.bot q) ≠ 0 → q ∈ s.labels ∧ s.bottom q = 1) ∧
      (∀ q, G.odd q →
        levE F x hn q (HRmap (resHom F x) q (G.bot q)) = 0 → s.partner q ≤ 0) := by
  obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by ring⟩
  have ha : 0 < a := by linarith
  have e : 2 * a / 2 = a := by ring
  rw [e]
  exact exists_data F G hfin ha hreg

/-! ### The level inputs -/

/-- The trivial doubling data. -/
def zeroData : Finsler.PartnerRank.Data ℕ where
  labels := ∅
  bottom := fun _ => 0
  partner := fun _ => 0
  T := 0
  Tdouble := 0
  J := 0
  Ve := 0
  V := 0
  rank := by
    rw [Finset.sum_empty, Finset.sum_empty]
    norm_num
  fixed := by norm_num
  nonnegJ := le_refl 0
  partner_le := fun _ _ => le_refl 0

open Classical in
/-- The doubling data of all cuts: at a regular positive cut the data of `exists_data_cut`. -/
def budget (hfin : (primeImages F).Finite) (x : ℝ) : Finsler.PartnerRank.Data ℕ :=
  if h : 0 < x ∧ x ∉ crit F then Classical.choose (exists_data_cut F G hfin h.1 h.2)
  else zeroData

theorem budget_spec (hfin : (primeImages F).Finite) {x : ℝ} (hx : 0 < x) (hreg : x ∉ crit F) :
    (budget F G hfin x).T = (Defect.defect F (x / 2) : ℤ) ∧
      (budget F G hfin x).Tdouble = (Defect.defect F x : ℤ) ∧
      (∀ q, G.odd q → HRmap (resHom F x) q (G.bot q) ≠ 0 →
        q ∈ (budget F G hfin x).labels ∧ (budget F G hfin x).bottom q = 1) ∧
      (∀ q, G.odd q → levE F x hn q (HRmap (resHom F x) q (G.bot q)) = 0 →
        (budget F G hfin x).partner q ≤ 0) := by
  have h : 0 < x ∧ x ∉ crit F := ⟨hx, hreg⟩
  have e : budget F G hfin x = Classical.choose (exists_data_cut F G hfin h.1 h.2) :=
    dite_eq_left h
  rw [e]
  exact Classical.choose_spec (exists_data_cut F G hfin h.1 h.2)

/-- The inputs of the final section which remain when the doubling budgets are derived from a
global basis: the basis, a bound for the defect, and the detection band. -/
structure BasisInputs (F : ReversibleMetric n) (hn : 1 ≤ n) where
  basis : Data n hn
  /-- boundedness of the defect -/
  bound : ℕ
  defect_le : ∀ a, 0 < a → a ∉ crit F → Defect.defect F a ≤ bound
  /-- detection band -/
  α : ℝ
  α_pos : 0 < α
  C : ℝ
  q₀ : ℕ
  det_inj : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → (q : ℝ) < α * a - C →
    Function.Injective (HRmap (resHom F a) q)
  det_zero : ∀ (q : ℕ) (a : ℝ), q₀ ≤ q → 0 < a → α * a + C < (q : ℝ) →
    ∀ x, HRmap (resHom F a) q x = 0

variable {F}

/-- The level inputs from a global basis, a bound for the defect and a detection band, for
finitely many prime closed geodesic images. -/
def toLevelInputs (hfin : (primeImages F).Finite) (I : BasisInputs F hn) : LevelInputs F hn where
  bound := I.bound
  defect_le := I.defect_le
  ι := ℕ
  budget := budget F I.basis hfin
  budget_T := fun _ hx hreg => (budget_spec F I.basis hfin hx hreg).1
  budget_Tdouble := fun _ hx hreg => (budget_spec F I.basis hfin hx hreg).2.1
  α := I.α
  α_pos := I.α_pos
  C := I.C
  q₀ := I.q₀
  det_inj := I.det_inj
  det_zero := I.det_zero
  bottom := fun t => I.basis.bot ((4 * t + 1) * (n - 1))
  bottom_ne := I.basis.bot_ne
  label := fun t => (4 * t + 1) * (n - 1)
  label_mem := fun t _ hx hreg hne =>
    ((budget_spec F I.basis hfin hx hreg).2.2.1 _ (I.basis.odd_mem t) hne).1
  label_bottom := fun t _ hx hreg hne =>
    ((budget_spec F I.basis hfin hx hreg).2.2.1 _ (I.basis.odd_mem t) hne).2
  label_partner := fun t _ hx hreg he =>
    (budget_spec F I.basis hfin hx hreg).2.2.2 _ (I.basis.odd_mem t) he

/-- With finitely many prime closed geodesic images, a global basis, a bound for the defect and
a detection band are contradictory. -/
theorem false_of_basisInputs (h2 : 2 ≤ n) (hfin : (primeImages F).Finite)
    (I : BasisInputs F hn) : False :=
  false_of_levelInputs h2 hfin (toLevelInputs hfin I)

/-- Reduction of the candidate main assertion to a global basis, a bound for the defect and a
detection band for every metric with finitely many prime closed geodesic images. -/
theorem assertion_of_basisInputs
    (h : ∀ n : ℕ, ∀ h3 : 3 ≤ n, ∀ F : ReversibleMetric n, (primeImages F).Finite →
      Nonempty (BasisInputs F (le_trans (by norm_num) h3))) :
    ReversibleSphereAssertion :=
  assertion_of_levelInputs fun n h3 F hfin => (h n h3 F hfin).map (toLevelInputs hfin)

end

end Finsler.BasisBudget
