module

public import Finsler.Topology.CrossingSlopes
public import Finsler.Topology.CrossingWK
public import Finsler.Topology.EventSum
public import Finsler.Topology.BandRank

/-! The rank bounds of the local events. Doubling and the root identify the crossing pair
(t_b, t_a) with the fixed crossing pair of t_{2b} and t_{2a}, equivariantly for the reversal;
hence the reflection Borel cohomology of the fixed crossing pair is that of the crossing pair at
half the cuts. With finitely many prime closed geodesic images, the reflection Borel groups of a
single crossing embed into its ordinary groups (w acts as zero), the K-Borel groups of a single
crossing in degree q have dimension at most the sum of its reflection Borel groups up to degree
q (the Borel cohomology of the iterated complex is bounded by its ordinary cohomology, which is
the reflection Borel cohomology), and the total dimension of the ordinary groups of a single
crossing is uniformly bounded. Therefore there is M with: the total dimension of the reflection
Borel cohomology of the fixed crossing pair of a single crossing at regular cuts 2a, 2b is at
most M, and the K-Borel groups of such a crossing have dimension at most M in every degree.
These are the rank fields of the local bounds of the events; the cutoffs near a crossing and the
far conditions are not treated here. -/

@[expose] public section

namespace Finsler.EventRanks

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.BorelCrossing
open Finsler.BorelFixed Finsler.FixedLadder Finsler.CutPotential Finsler.AvoidPoint
open Finsler.BorelIterate Finsler.BorelCrossingK Finsler.GradedLadder
open Finsler.CriticalLevels Finsler.CrossingSlopes Finsler.LevelBounds Finsler.LevelUniform
open Finsler.IntervalSobolev Finsler.SobolevReverse Finsler.PairTriple

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

section Doubling

variable {a b : ℝ} (hab : a ≤ b) (hab2 : 2 * a ≤ 2 * b)

/-- Doubling as a map of crossing pairs. -/
def dblCross : pairOf (lev_mono F hab) ⟶ pairOf (fixLev_mono F hab2) :=
  pairMap _ _ (dblMap F b) (fun _ hu => double_mem_fixLev F hu)

/-- The root as a map of crossing pairs. -/
def rootCross : pairOf (fixLev_mono F hab2) ⟶ pairOf (lev_mono F hab) :=
  pairMap _ _ (rootMap F b) (fun _ hu => root_mem_lev F hu)

theorem dbl_root_cross :
    dblCross F hab hab2 ≫ rootCross F hab hab2 = 𝟙 (pairOf (lev_mono F hab)) := by
  have h : (rootMap F b).comp (dblMap F b) = ContinuousMap.id (lev F b) := by
    ext u
    have e := Finsler.SobolevHalfRoot.root_doubleSphere (u : SphereLoop n)
    exact e
  exact (pairMap_comp _ _ _ (dblMap F b) (rootMap F b) (fun _ hu => double_mem_fixLev F hu)
    (fun _ hu => root_mem_lev F hu)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

theorem root_dbl_cross :
    rootCross F hab hab2 ≫ dblCross F hab hab2 = 𝟙 (pairOf (fixLev_mono F hab2)) := by
  have h : (dblMap F b).comp (rootMap F b) = ContinuousMap.id (fixLev F (2 * b)) := by
    ext u
    have e := congrArg Subtype.val (Finsler.SobolevHalfRoot.double_rootSphere ⟨(u : SphereLoop n),
      fixLev_subset_halfFixed F (2 * b) u.2⟩)
    exact e
  exact (pairMap_comp _ _ _ (rootMap F b) (dblMap F b) (fun _ hu => root_mem_lev F hu)
    (fun _ hu => double_mem_fixLev F hu)).symm.trans
    ((pairMap_congr _ _ h _ (fun _ hx => hx)).trans (pairMap_id _))

/-- The reversal of the fixed crossing pair. -/
abbrev revFixCross : pairOf (fixLev_mono F hab2) ⟶ pairOf (fixLev_mono F hab2) :=
  revSub (fixLev_mono F hab2) (Finsler.LocalCoverK.kInv_fixLev F (2 * a)).rev_mem
    (Finsler.LocalCoverK.kInv_fixLev F (2 * b)).rev_mem

theorem dblCross_rev :
    dblCross F hab hab2 ≫ revFixCross F hab2 = revCross F hab ≫ dblCross F hab hab2 := by
  have h : (revSet (Finsler.LocalCoverK.kInv_fixLev F (2 * b)).rev_mem).comp (dblMap F b) =
      (dblMap F b).comp (revLev F b) := by
    ext u
    have e := reverse_double (u : SphereLoop n)
    exact e
  exact (pairMap_comp _ _ _ (dblMap F b) _ (fun _ hu => double_mem_fixLev F hu)
    (fun _ hx => (Finsler.LocalCoverK.kInv_fixLev F (2 * a)).rev_mem _ hx)).symm.trans
    ((pairMap_congr _ _ h _ (fun u hx => double_mem_fixLev F (reverse_mem_lev F hx))).trans
      (pairMap_comp _ _ _ (revLev F b) (dblMap F b) (fun _ hx => reverse_mem_lev F hx)
        (fun _ hu => double_mem_fixLev F hu)))

theorem rootCross_rev :
    rootCross F hab hab2 ≫ revCross F hab = revFixCross F hab2 ≫ rootCross F hab hab2 := by
  calc rootCross F hab hab2 ≫ revCross F hab
      = rootCross F hab hab2 ≫ revCross F hab ≫ dblCross F hab hab2 ≫ rootCross F hab hab2 := by
        rw [dbl_root_cross, Category.comp_id]
    _ = rootCross F hab hab2 ≫ (revCross F hab ≫ dblCross F hab hab2) ≫ rootCross F hab hab2 := by
        simp only [Category.assoc]
    _ = rootCross F hab hab2 ≫ (dblCross F hab hab2 ≫ revFixCross F hab2) ≫
          rootCross F hab hab2 := by
        rw [dblCross_rev]
    _ = (rootCross F hab hab2 ≫ dblCross F hab hab2) ≫ revFixCross F hab2 ≫
          rootCross F hab hab2 := by
        simp only [Category.assoc]
    _ = revFixCross F hab2 ≫ rootCross F hab hab2 := by
        rw [root_dbl_cross, Category.id_comp]

/-- Pullback along doubling. -/
abbrev dblCrossHom :
    InvHom (rComplex (fixLev_mono F hab2) (Finsler.LocalCoverK.kInv_fixLev F (2 * a))
      (Finsler.LocalCoverK.kInv_fixLev F (2 * b))) (crossComplex F hab) :=
  pullHom (revCross_sq F hab) (revSub_sq _ _ _) (dblCross F hab hab2) (dblCross_rev F hab hab2)

/-- Pullback along the root. -/
abbrev rootCrossHom :
    InvHom (crossComplex F hab) (rComplex (fixLev_mono F hab2)
      (Finsler.LocalCoverK.kInv_fixLev F (2 * a)) (Finsler.LocalCoverK.kInv_fixLev F (2 * b))) :=
  pullHom (revSub_sq _ _ _) (revCross_sq F hab) (rootCross F hab hab2) (rootCross_rev F hab hab2)

theorem root_dbl_cross_f (j : ℕ) (x : (crossComplex F hab).C j) :
    (invHomComp (rootCrossHom F hab hab2) (dblCrossHom F hab hab2)).f j x = x := by
  have h := pull_comp_apply (dblCross F hab hab2) (rootCross F hab hab2) j x
  have h' : ((pull (dblCross F hab hab2 ≫ rootCross F hab hab2)).f j).hom x = x := by
    rw [dbl_root_cross]
    exact pull_id_apply _ j x
  exact h.symm.trans h'

theorem dbl_root_cross_f (j : ℕ) (x : (rComplex (fixLev_mono F hab2)
    (Finsler.LocalCoverK.kInv_fixLev F (2 * a)) (Finsler.LocalCoverK.kInv_fixLev F (2 * b))).C j) :
    (invHomComp (dblCrossHom F hab hab2) (rootCrossHom F hab hab2)).f j x = x := by
  have h := pull_comp_apply (rootCross F hab hab2) (dblCross F hab hab2) j x
  have h' : ((pull (rootCross F hab hab2 ≫ dblCross F hab hab2)).f j).hom x = x := by
    rw [root_dbl_cross]
    exact pull_id_apply _ j x
  exact h.symm.trans h'

/-- **Doubling for crossing pairs.** The reflection Borel cohomology of the crossing pair
(t_b, t_a) is that of the fixed crossing pair of t_{2b} and t_{2a}. -/
def crossDoublingEquiv (q : ℕ) : HR (crossComplex F hab) q ≃ₗ[ZMod 2] crossR F hab2 q :=
  LinearEquiv.ofLinearMap (HRmap (rootCrossHom F hab hab2) q) (HRmap (dblCrossHom F hab hab2) q)
    (LinearMap.ext fun z => by
      change HRmap (rootCrossHom F hab hab2) q (HRmap (dblCrossHom F hab hab2) q z) = z
      rw [← HRmap_comp]
      exact HRmap_id_of (dbl_root_cross_f F hab hab2) q z)
    (LinearMap.ext fun z => by
      change HRmap (dblCrossHom F hab hab2) q (HRmap (rootCrossHom F hab hab2) q z) = z
      rw [← HRmap_comp]
      exact HRmap_id_of (root_dbl_cross_f F hab hab2) q z)

end Doubling


section Bounds

/-- The ordinary groups of the single crossings have uniformly bounded total dimension. -/
theorem exists_cross_total (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ B : ℕ, ∀ (a' b' : ℝ) (hab' : a' ≤ b'), 0 < a' → a' ∉ crit F → b' ∉ crit F →
      (crit F ∩ Icc a' b').Subsingleton → ∀ Q : ℕ,
      ∑ q ∈ Finset.range Q, finrank (ZMod 2) (H (crossComplex F hab') q) ≤ B := by
  obtain ⟨B, A, hBA⟩ := exists_level_bounds F hn hfin
  refine ⟨B, fun a' b' hab' ha' hac hbc hsub Q => ?_⟩
  by_cases hreg : ∀ x ∈ Icc a' b', x ∉ crit F
  · have h0 : ∀ q, finrank (ZMod 2) (H (crossComplex F hab') q) = 0 := fun q => by
      have : Subsingleton (H (crossComplex F hab') q) :=
        ⟨fun x y => (cross_zero_regular F hn ha' hab' hreg q x).trans
          (cross_zero_regular F hn ha' hab' hreg q y).symm⟩
      exact finrank_zero_of_subsingleton
    simp only [h0, Finset.sum_const_zero, Nat.zero_le]
  · push Not at hreg
    obtain ⟨c₀, ⟨h1', h2'⟩, hc₀⟩ := hreg
    have h1 : a' < c₀ := lt_of_le_of_ne h1' fun h => hac (h ▸ hc₀)
    have h2 : c₀ < b' := lt_of_le_of_ne h2' fun h => hbc (h.symm ▸ hc₀)
    have hone : ∀ c' ∈ crit F, a' ≤ c' → c' ≤ b' → c' = c₀ := fun c' hc' h3 h4 =>
      hsub ⟨hc', h3, h4⟩ ⟨hc₀, h1', h2'⟩
    obtain ⟨htot, -⟩ := hBA hab' ha' h1 h2 hone
    calc ∑ q ∈ Finset.range Q, finrank (ZMod 2) (H (crossComplex F hab') q)
        = ∑ q ∈ Finset.range Q, finrank (ZMod 2) (H (triv (pairOf (lev_mono F hab'))) q) :=
          Finset.sum_congr rfl fun q _ => (crossEquiv F hab' q).finrank_eq
      _ ≤ B := htot Q

/-- The reflection Borel groups of a single crossing embed into its ordinary groups. -/
theorem finrank_HR_cross_le (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 < a) (hac : a ∉ crit F) (hbc : b ∉ crit F)
    (hsub : (crit F ∩ Icc a b).Subsingleton) (q : ℕ) :
    finrank (ZMod 2) (HR (crossComplex F hab) q) ≤ finrank (ZMod 2) (H (crossComplex F hab) q) := by
  obtain ⟨-, hfinX, -⟩ := cross_finite F hn hfin ha hab hac hbc
  have : Module.Finite (ZMod 2) (H (crossComplex F hab) q) := by
    have := hfinX q
    exact Module.Finite.equiv (crossEquiv F hab q).symm
  cases q with
  | zero =>
    exact LinearMap.finrank_le_finrank_of_injective
      (Finsler.BorelQuasiIso.forget_zero_injective _)
  | succ q =>
    exact LinearMap.finrank_le_finrank_of_injective
      (Finsler.CrossingW.cross_forget_injective F hn hfin hab ha hac hbc hsub q)

omit F in
/-- The total dimension of a graded family vanishing from degree Q on is at most the sum of its
dimensions below Q. -/
theorem totRank_le_sum (G : ℕ → Type) [∀ q, AddCommGroup (G q)] [∀ q, Module (ZMod 2) (G q)]
    [∀ q, Module.Finite (ZMod 2) (G q)] {Q : ℕ} (hz : ∀ q, Q ≤ q → ∀ x : G q, x = 0) :
    totRank G ≤ ∑ q ∈ Finset.range Q, finrank (ZMod 2) (G q) := by
  let r : ((q : ℕ) → G q) →ₗ[ZMod 2] ((q : Fin Q) → G q) :=
    LinearMap.pi fun q => LinearMap.proj (q : ℕ)
  have hr : Function.Injective r := by
    intro x y hxy
    funext q
    by_cases hq : q < Q
    · exact congrFun hxy ⟨q, hq⟩
    · rw [hz q (not_lt.mp hq) (x q), hz q (not_lt.mp hq) (y q)]
  calc totRank G = finrank (ZMod 2) ((q : ℕ) → G q) := rfl
    _ ≤ finrank (ZMod 2) ((q : Fin Q) → G q) := LinearMap.finrank_le_finrank_of_injective hr
    _ = ∑ q : Fin Q, finrank (ZMod 2) (G q) := Module.finrank_pi_fintype (ZMod 2)
    _ = ∑ q ∈ Finset.range Q, finrank (ZMod 2) (G q) :=
        Fin.sum_univ_eq_sum_range (fun q => finrank (ZMod 2) (G q)) Q

set_option maxHeartbeats 1600000 in
/-- **The rank bounds of the local events.** -/
theorem exists_event_ranks (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ M : ℕ,
      (∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
        (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → totRank (crossR F hab) ≤ M) ∧
      (∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
        (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ q,
          finrank (ZMod 2) (crossK F hab q) ≤ M) := by
  obtain ⟨B, hB⟩ := exists_cross_total F hn hfin
  refine ⟨B, fun a b hab2 ha h2a h2b hsub => ?_, fun a b hab2 ha h2a h2b hsub q => ?_⟩
  · have hab : a ≤ b := by linarith
    have hac : a ∉ crit F := fun h => h2a (crit_double F h)
    have hbc : b ∉ crit F := fun h => h2b (crit_double F h)
    have hsub' : (crit F ∩ Icc a b).Subsingleton := by
      intro x hx y hy
      have h := hsub ⟨crit_double F hx.1, by linarith [hx.2.1], by linarith [hx.2.2]⟩
        ⟨crit_double F hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
      linarith
    obtain ⟨Q, hQ⟩ := exists_crossHR_high F hn hfin ha hab hac hbc
    obtain ⟨-, hfinX, -⟩ := cross_finite F hn hfin ha hab hac hbc
    have hH : ∀ p, Module.Finite (ZMod 2) (H (crossComplex F hab) p) := fun p => by
      have := hfinX p
      exact Module.Finite.equiv (crossEquiv F hab p).symm
    have hfinR : ∀ q, Module.Finite (ZMod 2) (crossR F hab2 q) := fun q => by
      have := Finsler.FiniteCut.finite_HR (crossComplex F hab) hH q
      exact Module.Finite.equiv (crossDoublingEquiv F hab hab2 q)
    calc totRank (crossR F hab2) ≤ ∑ q ∈ Finset.range Q, finrank (ZMod 2) (crossR F hab2 q) :=
          totRank_le_sum (crossR F hab2) fun q hq x => by
            have h := hQ q hq ((crossDoublingEquiv F hab hab2 q).symm x)
            rw [← (crossDoublingEquiv F hab hab2 q).apply_symm_apply x, h, map_zero]
      _ = ∑ q ∈ Finset.range Q, finrank (ZMod 2) (HR (crossComplex F hab) q) :=
          Finset.sum_congr rfl fun q _ => (crossDoublingEquiv F hab hab2 q).finrank_eq.symm
      _ ≤ ∑ q ∈ Finset.range Q, finrank (ZMod 2) (H (crossComplex F hab) q) :=
          Finset.sum_le_sum fun q _ => finrank_HR_cross_le F hn hfin hab ha hac hbc hsub' q
      _ ≤ B := hB a b hab ha hac hbc hsub' Q
  · have h0 : 0 < 2 * a := by linarith
    obtain ⟨-, hfinX, -⟩ := cross_finite F hn hfin h0 hab2 h2a h2b
    have hH : ∀ p, Module.Finite (ZMod 2) (H (crossComplex F hab2) p) := fun p => by
      have := hfinX p
      exact Module.Finite.equiv (crossEquiv F hab2 p).symm
    have hHK : ∀ p, Module.Finite (ZMod 2) (H (kCross F hab2) p) := fun p => by
      have := Finsler.FiniteCut.finite_HR (crossComplex F hab2) hH p
      exact Module.Finite.equiv (cohomologyEquiv (halfCommutingCross F hab2) p).symm
    calc finrank (ZMod 2) (crossK F hab2 q) = finrank (ZMod 2) (HR (kCross F hab2) q) := rfl
      _ ≤ ∑ i ∈ Finset.range (q + 1), finrank (ZMod 2) (H (kCross F hab2) i) :=
          Finsler.BandRank.finrank_HR_le_sum (kCross F hab2) hHK q
      _ = ∑ i ∈ Finset.range (q + 1), finrank (ZMod 2) (HR (crossComplex F hab2) i) :=
          Finset.sum_congr rfl fun i _ => (cohomologyEquiv (halfCommutingCross F hab2) i).finrank_eq
      _ ≤ ∑ i ∈ Finset.range (q + 1), finrank (ZMod 2) (H (crossComplex F hab2) i) :=
          Finset.sum_le_sum fun i _ => finrank_HR_cross_le F hn hfin hab2 h0 h2a h2b hsub i
      _ ≤ B := hB (2 * a) (2 * b) hab2 h0 h2a h2b hsub (q + 1)


open Finsler.EventSum Finsler.BorelK Finsler.TotalExact in
/-- **The local bounds of the events from the cutoffs near a crossing.** The rank fields of the
local bounds hold with a uniform constant, so the local bounds exist as soon as the cutoffs near
a crossing (at most N of them) and the far conditions are given. -/
theorem nonempty_eventBounds (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {N : ℕ}
    (near : ℝ → ℝ → Finset ℕ) (near_card : ∀ a b, (near a b).card ≤ N)
    (far : ∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
      (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ k, k ∉ near a b →
      (∀ x : fixR F (2 * a) (k + 1), fixDelta F hab (k + 1) x = 0) ∧
        LinearMap.range (cut (crossR F hab) (k + 1)) ≤
          LinearMap.range (crossEps F hab (2 * k + 1)) ∧
        Function.Injective (crossEps F hab (2 * k + 1 + 1)) ∧
        LinearMap.range (crossEps F hab (2 * k + 1 + 1)) =
          LinearMap.range (cut (crossR F hab) (k + 1)) ∧
        Function.Injective (crossEps F hab (2 * k + 1 + 1 + 1)) ∧
        LinearMap.range (crossEps F hab (2 * k + 1 + 1 + 1)) ≤
          LinearMap.range (cut (crossR F hab) (k + 1))) :
    Nonempty (EventBounds F) := by
  obtain ⟨M, hR, hK⟩ := exists_event_ranks F hn hfin
  exact ⟨⟨M, N, near, near_card, hR, hK, far⟩⟩

end Bounds

end

end Finsler.EventRanks
