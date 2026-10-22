module

public import Finsler.Topology.EventRanks
public import Finsler.Topology.GapOrdinary
public import Mathlib.Algebra.FiveLemma

/-! Localization of a crossing at its fixed crossing above the ordinary groups. For a triple
s ⊆ t ⊆ u of invariant sets of loops with a fixed triple inside, restriction maps the K-Borel
sequence of (u, t, s) to that of the fixed triple, and the five lemma gives: if restriction is
bijective on (u, s) and (t, s) in degrees q and q + 1, it is bijective on the crossing (u, t) in
degree q + 1. With finitely many prime closed geodesic images, at regular cuts 2a ≤ 2b
restriction from (t_{2b}, M) and (t_{2a}, M) to their fixed pairs is bijective in high degrees
(`LocalizeK`), hence so is restriction from the crossing pair (t_{2b}, t_{2a}) to the fixed
crossing pair. Restriction commutes with the class w of the half rotation, and w is bijective
on the K-Borel cohomology of a complex in the degrees above its reflection Borel cohomology
(Gysin). So restriction from the crossing to the fixed crossing is bijective in every degree
above the reflection Borel cohomology of both crossing pairs: the threshold is uniform, it does
not depend on the order of nilpotency of U = v(v + w). On the fixed crossing the half rotation
acts trivially, so the components of a K-Borel class of degree q are injective with image the
families of root degrees at most q (`TrivialK`); hence above the reflection Borel groups of both
crossing pairs the total normalized restriction of a crossing is injective with image the
families of root degrees at most q. Below the ordinary groups of the crossing its K-Borel groups
vanish. -/

@[expose] public section

namespace Finsler.CrossLocalize

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelFixed Finsler.FixedLadder Finsler.CutPotential Finsler.AvoidPoint
open Finsler.BorelIterate Finsler.BorelCrossingK Finsler.GradedLadder Finsler.BorelExact
open Finsler.CriticalLevels Finsler.CrossingSlopes Finsler.LevelBounds
open Finsler.IntervalSobolev Finsler.SobolevReverse Finsler.PairTriple
open Finsler.BorelK Finsler.TotalExact Finsler.BorelCoverK Finsler.LocalCoverK
open Finsler.TrivialK Finsler.FixedGlobal Finsler.LadderEvent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-! ### Multiplication by w and bijectivity -/

section Gysin

variable {K L : InvComplex} (φ : InvHom K L)

/-- If a map of complexes is bijective on Borel cohomology of degree q + 1 and w is bijective on
the source and injective on the target in degree q, the map is bijective in degree q. -/
theorem bijective_of_w (q : ℕ) (hφ : Function.Bijective (HRmap φ (q + 1)))
    (hK : ∀ z : H K q, z = 0) (hK1 : ∀ z : H K (q + 1), z = 0) (hL : ∀ z : H L q, z = 0) :
    Function.Bijective (HRmap φ q) := by
  have hwK := Finsler.GapOrdinary.w_injective K hK
  have hwK' := Finsler.GapOrdinary.w_surjective K hK1
  have hwL := Finsler.GapOrdinary.w_injective L hL
  constructor
  · intro x y hxy
    apply hwK
    apply hφ.1
    rw [HRmap_w, HRmap_w, hxy]
  · intro y
    obtain ⟨x', hx'⟩ := hφ.2 (w L q y)
    obtain ⟨x, rfl⟩ := hwK' x'
    refine ⟨x, hwL ?_⟩
    rw [← HRmap_w, hx']

/-- Bijectivity in high degrees propagates down to every degree above the ordinary cohomology of
the source and the target. -/
theorem bijective_down {T Q : ℕ} (hQ : ∀ q, Q ≤ q → Function.Bijective (HRmap φ q))
    (hK : ∀ q, T ≤ q → ∀ z : H K q, z = 0) (hL : ∀ q, T ≤ q → ∀ z : H L q, z = 0) :
    ∀ q, T ≤ q → Function.Bijective (HRmap φ q) := by
  suffices h : ∀ m q, T ≤ q → Q ≤ q + m → Function.Bijective (HRmap φ q) from
    fun q hq => h Q q hq (by omega)
  intro m
  induction m with
  | zero => exact fun q _ hq => hQ q (by omega)
  | succ m ih =>
    intro q hq hqm
    exact bijective_of_w φ q (ih (q + 1) (by omega) (by omega)) (hK q hq) (hK (q + 1) (by omega))
      (hL q hq)

end Gysin

/-! ### The five lemma for restriction to a fixed triple -/

section Triple

variable {s t u s₀ t₀ u₀ : Set (Loops n)} (hst : s ⊆ t) (htu : t ⊆ u) (hs : KInv s)
  (ht : KInv t) (hu : KInv u) (hst₀ : s₀ ⊆ t₀) (htu₀ : t₀ ⊆ u₀) (hs₀ : KInv s₀) (ht₀ : KInv t₀)
  (hu₀ : KInv u₀) (hss : s₀ ⊆ s) (htt : t₀ ⊆ t) (huu : u₀ ⊆ u)

/-- Restriction commutes with the map from (u, t) to (u, s). -/
theorem res_sub (q : ℕ) (x : HR (borelInv (kCommuting htu ht hu)) q) :
    HRmap (borelHom (kHom (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀ hu₀ hst₀ subset_rfl)) q
        (HRmap (borelHom (kHom htu₀ ht₀ hu₀ htu ht hu htt huu)) q x) =
      HRmap (borelHom (kHom (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu hss huu)) q
        (HRmap (borelHom (kHom (hst.trans htu) hs hu htu ht hu hst subset_rfl)) q x) :=
  (HRmap_square _ _ _ _ (fun j z => borelHom_square _ _ _ _ (fun m y =>
    (kHom_comp (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu htu ht hu hss huu hst
      subset_rfl m y).trans
      (kHom_comp (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀ hu₀ htu ht hu hst₀ subset_rfl htt huu
        m y).symm) j z) q x).symm

/-- Restriction commutes with the map from (u, s) to (t, s). -/
theorem res_quot (q : ℕ) (x : HR (borelInv (kCommuting (hst.trans htu) hs hu)) q) :
    HRmap (borelHom (kHom hst₀ hs₀ ht₀ (hst₀.trans htu₀) hs₀ hu₀ subset_rfl htu₀)) q
        (HRmap (borelHom (kHom (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu hss huu)) q x) =
      HRmap (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt)) q
        (HRmap (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) q x) :=
  (HRmap_square _ _ _ _ (fun j y => borelHom_square _ _ _ _ (fun m z =>
    (kHom_comp hst₀ hs₀ ht₀ hst hs ht (hst.trans htu) hs hu hss htt subset_rfl htu m z).trans
      (kHom_comp hst₀ hs₀ ht₀ (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu subset_rfl htu₀
        hss huu m z).symm) j y) q x).symm

/-- **The five lemma for restriction to a fixed triple.** If restriction is surjective on (u, s)
in degree q, bijective on (t, s) in degree q and on (u, s) in degree q + 1, and injective on
(t, s) in degree q + 1, it is bijective on the crossing (u, t) in degree q + 1. -/
theorem res_bijective_succ (q : ℕ)
    (h1 : Function.Surjective
      (HRmap (borelHom (kHom (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu hss huu)) q))
    (h2 : Function.Bijective (HRmap (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt)) q))
    (h4 : Function.Bijective
      (HRmap (borelHom (kHom (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu hss huu)) (q + 1)))
    (h5 : Function.Injective (HRmap (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt)) (q + 1))) :
    Function.Bijective (HRmap (borelHom (kHom htu₀ ht₀ hu₀ htu ht hu htt huu)) (q + 1)) := by
  have hK := shortExactK hst htu hs ht hu
  have hF := shortExactK hst₀ htu₀ hs₀ ht₀ hu₀
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (HRmap (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) q)
    (delta hK q)
    (HRmap (borelHom (kHom (hst.trans htu) hs hu htu ht hu hst subset_rfl)) (q + 1))
    (HRmap (borelHom (kHom hst hs ht (hst.trans htu) hs hu subset_rfl htu)) (q + 1))
    (HRmap (borelHom (kHom hst₀ hs₀ ht₀ (hst₀.trans htu₀) hs₀ hu₀ subset_rfl htu₀)) q)
    (delta hF q)
    (HRmap (borelHom (kHom (hst₀.trans htu₀) hs₀ hu₀ htu₀ ht₀ hu₀ hst₀ subset_rfl)) (q + 1))
    (HRmap (borelHom (kHom hst₀ hs₀ ht₀ (hst₀.trans htu₀) hs₀ hu₀ subset_rfl htu₀)) (q + 1))
    (HRmap (borelHom (kHom (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu hss huu)) q)
    (HRmap (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt)) q)
    (HRmap (borelHom (kHom htu₀ ht₀ hu₀ htu ht hu htt huu)) (q + 1))
    (HRmap (borelHom (kHom (hst₀.trans htu₀) hs₀ hu₀ (hst.trans htu) hs hu hss huu)) (q + 1))
    (HRmap (borelHom (kHom hst₀ hs₀ ht₀ hst hs ht hss htt)) (q + 1))
    (LinearMap.ext fun x => res_quot hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu q x)
    (LinearMap.ext fun x => res_delta hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu q x)
    (LinearMap.ext fun x =>
      res_sub hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu (q + 1) x)
    (LinearMap.ext fun x =>
      res_quot hst htu hs ht hu hst₀ htu₀ hs₀ ht₀ hu₀ hss htt huu (q + 1) x)
    (LinearMap.exact_iff.mpr (ker_delta hK q))
    (LinearMap.exact_iff.mpr (ker_sub hK q))
    (LinearMap.exact_iff.mpr (ker_mid hK (q + 1)))
    (LinearMap.exact_iff.mpr (ker_delta hF q))
    (LinearMap.exact_iff.mpr (ker_sub hF q))
    (LinearMap.exact_iff.mpr (ker_mid hF (q + 1)))
    h1 h2 h4 h5

end Triple

/-! ### The components of a class on loops fixed by the half rotation -/

section Theta

variable {K : InvComplex} (S : Commuting K) (hS : ∀ j x, S.s j x = x)

/-- The family of components of an iterated Borel class with trivial second involution is
injective. -/
theorem totTheta_injective (q : ℕ) :
    Function.Injective (totMap (X := HR (borelInv S) q) (G := fun l => HR K l)
      (fun l => theta S hS q l)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  exact eq_zero_of_theta S hS q x (fun j _ => congrFun hx j)

/-- The families of components of iterated Borel classes of degree q with trivial second
involution are the families of degrees at most q. -/
theorem range_totTheta (q : ℕ) :
    LinearMap.range (totMap (X := HR (borelInv S) q) (G := fun l => HR K l)
      (fun l => theta S hS q l)) = LinearMap.range (cut (fun l => HR K l) q) := by
  ext y
  rw [mem_range_cut]
  constructor
  · rintro ⟨x, rfl⟩ l hl
    exact Finsler.ThetaLadder.theta_high S hS q l hl x
  · intro hy
    refine ⟨(trivSplit S hS q).symm (fun l => y l), ?_⟩
    funext l
    by_cases hl : l ≤ q
    · exact congrFun ((trivSplit S hS q).apply_symm_apply (fun l : Fin (q + 1) => y l))
        ⟨l, Nat.lt_succ_of_le hl⟩
    · rw [totMap_apply, Finsler.ThetaLadder.theta_high S hS q l (by omega), hy l (by omega)]

end Theta

/-! ### Crossings -/

variable (F : ReversibleMetric n)

/-- Restriction from the crossing pair (t_b, t_a) to the fixed crossing pair. -/
abbrev crossRes {a b : ℝ} (hab : a ≤ b) (q : ℕ) :=
  HRmap (borelHom (kHom (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b) (lev_mono F hab)
    (kInv_lev F a) (kInv_lev F b) (fixLev_subset_lev F a) (fixLev_subset_lev F b))) q

/-- With finitely many prime closed geodesic images, at regular cuts 2a ≤ 2b restriction from the
crossing pair to the fixed crossing pair is bijective in high degrees. -/
theorem exists_crossRes_bijective (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab2 : 2 * a ≤ 2 * b) (h2a : 2 * a ∉ crit F) (h2b : 2 * b ∉ crit F) :
    ∃ Q : ℕ, ∀ q, Q ≤ q → Function.Bijective (crossRes F hab2 q) := by
  have hb : 0 < b := by linarith
  obtain ⟨Qa, hQa⟩ := Finsler.LocalizeK.exists_bijective_fixed F hn hfin ha h2a
  obtain ⟨Qb, hQb⟩ := Finsler.LocalizeK.exists_bijective_fixed F hn hfin hb h2b
  refine ⟨max Qa Qb + 1, fun q hq => ?_⟩
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  exact res_bijective_succ (consts_subset_lev F (2 * a)) (lev_mono F hab2) kInv_consts
    (kInv_lev F (2 * a)) (kInv_lev F (2 * b)) (consts_subset_fixLev F (2 * a))
    (fixLev_mono F hab2) kInv_consts (kInv_fixLev F (2 * a)) (kInv_fixLev F (2 * b)) subset_rfl
    (fixLev_subset_lev F (2 * a)) (fixLev_subset_lev F (2 * b)) p
    (hQb p (by omega)).2 (hQa p (by omega)) (hQb (p + 1) (by omega))
    (hQa (p + 1) (by omega)).1

/-- **Localization of a crossing above its reflection Borel groups.** With finitely many prime
closed geodesic images, at regular cuts 2a ≤ 2b, if the reflection Borel groups of the crossing
pair and of the fixed crossing pair vanish from degree T on, restriction from the crossing pair
to the fixed crossing pair is bijective on K-Borel cohomology from degree T on. -/
theorem crossRes_bijective (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab2 : 2 * a ≤ 2 * b) (h2a : 2 * a ∉ crit F) (h2b : 2 * b ∉ crit F) {T : ℕ}
    (hX : ∀ q, T ≤ q → ∀ z : HR (crossComplex F hab2) q, z = 0)
    (hB : ∀ q, T ≤ q → ∀ z : crossR F hab2 q, z = 0) (q : ℕ) (hq : T ≤ q) :
    Function.Bijective (crossRes F hab2 q) := by
  obtain ⟨Q, hQ⟩ := exists_crossRes_bijective F hn hfin ha hab2 h2a h2b
  refine bijective_down _ hQ (fun p hp z => ?_) (fun p hp z => ?_) q hq
  · exact (LinearEquiv.map_eq_zero_iff (cohomologyEquiv (halfCommutingCross F hab2) p)).mp
      (hX p hp _)
  · exact (LinearEquiv.map_eq_zero_iff (cohomologyEquiv (kCommuting (fixLev_mono F hab2)
      (kInv_fixLev F (2 * a)) (kInv_fixLev F (2 * b))) p)).mp (hB p hp _)

/-- The total normalized restriction of a crossing is the family of components of the
restriction to the fixed crossing pair. -/
theorem crossEps_eq {a b : ℝ} (hab : a ≤ b) (q : ℕ) :
    crossEps F hab q =
      (totMap (X := HR (borelInv (kCommuting (fixLev_mono F hab) (kInv_fixLev F a)
          (kInv_fixLev F b))) q)
        (G := fun l => crossR F hab l)
        (fun l => theta (kCommuting (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b))
          (kCommuting_trivial (fixLev_mono F hab) (kInv_fixLev F a) (kInv_fixLev F b)
            (half_fixLev F b)) q l)) ∘ₗ crossRes F hab q :=
  LinearMap.ext fun _ => funext fun _ => rfl

/-- **The total normalized restriction above the reflection Borel groups.** Under the hypotheses
of the localization of a crossing, from degree T on the total normalized restriction of the
crossing is injective with image the families of root degrees at most q. -/
theorem crossEps_high (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab2 : 2 * a ≤ 2 * b) (h2a : 2 * a ∉ crit F) (h2b : 2 * b ∉ crit F) {T : ℕ}
    (hX : ∀ q, T ≤ q → ∀ z : HR (crossComplex F hab2) q, z = 0)
    (hB : ∀ q, T ≤ q → ∀ z : crossR F hab2 q, z = 0) (q : ℕ) (hq : T ≤ q) :
    Function.Injective (crossEps F hab2 q) ∧
      LinearMap.range (crossEps F hab2 q) = LinearMap.range (cut (crossR F hab2) q) := by
  have hbij := crossRes_bijective F hn hfin ha hab2 h2a h2b hX hB q hq
  have hS := kCommuting_trivial (fixLev_mono F hab2) (kInv_fixLev F (2 * a))
    (kInv_fixLev F (2 * b)) (half_fixLev F (2 * b))
  rw [crossEps_eq]
  refine ⟨(totTheta_injective _ hS q).comp hbij.1, ?_⟩
  rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hbij.2)]
  exact range_totTheta _ hS q

/-- **Vanishing below the ordinary groups.** With finitely many prime closed geodesic images, at
regular cuts 2a ≤ 2b with at most one critical level between them, the K-Borel crossing group
of degree q vanishes if the ordinary groups of the crossing vanish in all degrees at most q. -/
theorem crossK_zero_low (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (hab2 : 2 * a ≤ 2 * b) (ha : 0 < a) (h2a : 2 * a ∉ crit F) (h2b : 2 * b ∉ crit F)
    (hsub : (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton) {q : ℕ}
    (hz : ∀ i, i ≤ q → ∀ z : H (crossComplex F hab2) i, z = 0) (x : crossK F hab2 q) : x = 0 := by
  have h0 : 0 < 2 * a := by linarith
  obtain ⟨-, hfinX, -⟩ := cross_finite F hn hfin h0 hab2 h2a h2b
  have hH : ∀ p, Module.Finite (ZMod 2) (H (crossComplex F hab2) p) := fun p => by
    have := hfinX p
    exact Module.Finite.equiv (crossEquiv F hab2 p).symm
  have hHK : ∀ p, Module.Finite (ZMod 2) (H (kCross F hab2) p) := fun p => by
    have := Finsler.FiniteCut.finite_HR (crossComplex F hab2) hH p
    exact Module.Finite.equiv (cohomologyEquiv (halfCommutingCross F hab2) p).symm
  have hz' : ∀ i ∈ Finset.range (q + 1), finrank (ZMod 2) (H (crossComplex F hab2) i) = 0 :=
    fun i hi => by
      have : Subsingleton (H (crossComplex F hab2) i) :=
        ⟨fun x y => (hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) x).trans
          (hz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) y).symm⟩
      exact finrank_zero_of_subsingleton
  have hle : finrank (ZMod 2) (crossK F hab2 q) ≤ 0 :=
    calc finrank (ZMod 2) (crossK F hab2 q) = finrank (ZMod 2) (HR (kCross F hab2) q) := rfl
      _ ≤ ∑ i ∈ Finset.range (q + 1), finrank (ZMod 2) (H (kCross F hab2) i) :=
          Finsler.BandRank.finrank_HR_le_sum (kCross F hab2) hHK q
      _ = ∑ i ∈ Finset.range (q + 1), finrank (ZMod 2) (HR (crossComplex F hab2) i) :=
          Finset.sum_congr rfl fun i _ =>
            (cohomologyEquiv (halfCommutingCross F hab2) i).finrank_eq
      _ ≤ ∑ i ∈ Finset.range (q + 1), finrank (ZMod 2) (H (crossComplex F hab2) i) :=
          Finset.sum_le_sum fun i _ =>
            Finsler.EventRanks.finrank_HR_cross_le F hn hfin hab2 h0 h2a h2b hsub i
      _ = 0 := Finset.sum_eq_zero hz'
  have := Finsler.CutFinite.finite_crossK F hn hfin h0 hab2 h2a h2b q
  have hs : Subsingleton (crossK F hab2 q) := Module.finrank_zero_iff.mp (Nat.le_zero.mp hle)
  exact Subsingleton.elim x 0

end

end Finsler.CrossLocalize
