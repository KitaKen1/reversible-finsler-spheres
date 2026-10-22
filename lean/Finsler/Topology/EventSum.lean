module

public import Finsler.Topology.CutStable
public import Finsler.Topology.LevelCount

/-! The sum of the potentials over the cutoffs at a regular cut, from local bounds for single
crossings. The local input (`EventBounds`) gives, for every pair of regular cuts 2a ≤ 2b with at
most one critical level between them, a bound M for the dimensions of the total fixed crossing
group and of the K-Borel crossing groups, and a set of at most N cutoffs outside of which the
hypotheses of a far cutoff hold. With finitely many prime closed geodesic images the potential
vanishes at small cuts, is the same at the two ends of an interval without critical levels, does
not increase at a far cutoff of a crossing and increases by at most 6M at the others. By
induction over the critical levels, the sum over any number of cutoffs of the potentials at a
regular cut 2a is at most 6MN times the number of critical levels in [0, 2a], which grows at
most linearly in a. The local input is not proved. -/

@[expose] public section

namespace Finsler.EventSum

open Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.BorelCochain Finsler.BorelLoop
open Finsler.BorelK Finsler.BorelExact Finsler.TotalExact Finsler.GradedLadder
open Finsler.CutPotential Finsler.CutFinite Finsler.CutRegular Finsler.CutStable
open Finsler.CriticalLevels Finsler.FiniteCut Finsler.LevelCount

noncomputable section

variable {n : ℕ}

/-- The potential of the cutoff k + 1 at the cut x, in the degrees 2k + 1 and 2k + 2. -/
def pot (F : ReversibleMetric n) (x : ℝ) (k : ℕ) : ℤ := cutPhi F x (k + 1) (2 * k + 1)

/-- Local bounds for the crossings of single critical levels. -/
structure EventBounds (F : ReversibleMetric n) where
  /-- bound for the dimensions of the crossing groups -/
  M : ℕ
  /-- bound for the number of cutoffs near a crossing -/
  N : ℕ
  /-- the cutoffs near a crossing -/
  near : ℝ → ℝ → Finset ℕ
  near_card : ∀ a b, (near a b).card ≤ N
  totRank_le : ∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
    (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → totRank (crossR F hab) ≤ M
  finrank_le : ∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
    (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ q, finrank (ZMod 2) (crossK F hab q) ≤ M
  far : ∀ (a b : ℝ) (hab : 2 * a ≤ 2 * b), 0 < a → 2 * a ∉ crit F → 2 * b ∉ crit F →
    (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton → ∀ k, k ∉ near a b →
    (∀ x : fixR F (2 * a) (k + 1), fixDelta F hab (k + 1) x = 0) ∧
      LinearMap.range (cut (crossR F hab) (k + 1)) ≤
        LinearMap.range (crossEps F hab (2 * k + 1)) ∧
      Function.Injective (crossEps F hab (2 * k + 1 + 1)) ∧
      LinearMap.range (crossEps F hab (2 * k + 1 + 1)) =
        LinearMap.range (cut (crossR F hab) (k + 1)) ∧
      Function.Injective (crossEps F hab (2 * k + 1 + 1 + 1)) ∧
      LinearMap.range (crossEps F hab (2 * k + 1 + 1 + 1)) ≤
        LinearMap.range (cut (crossR F hab) (k + 1))

variable {F : ReversibleMetric n}

/-- Across a crossing of at most one critical level the potential of a cutoff increases by at
most 6M, and does not increase at a cutoff which is not near. -/
theorem pot_cross (E : EventBounds F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a b : ℝ}
    (ha : 0 < a) (hab : 2 * a ≤ 2 * b) (h2a : 2 * a ∉ crit F) (h2b : 2 * b ∉ crit F)
    (hsub : (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton) (k : ℕ) :
    pot F (2 * b) k ≤ pot F (2 * a) k + (if k ∈ E.near a b then 6 * (E.M : ℤ) else 0) := by
  have hb : 0 < b := by linarith
  have h0a : 0 < 2 * a := by linarith
  have h0b : 0 < 2 * b := by linarith
  have hV := finTot_fixR F hn hfin ha h2a
  have hV' := finTot_fixR F hn hfin hb h2b
  have hW := finTot_crossR F hn hfin ha hab h2a h2b
  by_cases hk : k ∈ E.near a b
  · rw [ite_eq_left hk]
    exact (cutPhi_near F hab (k + 1) (2 * k + 1) hV hV' hW
      (finite_HK F hn hfin h0a h2a (2 * k + 1)) (finite_HK F hn hfin h0a h2a (2 * k + 1 + 1))
      (finite_HK F hn hfin h0b h2b (2 * k + 1 + 1))
      (finite_crossK F hn hfin h0a hab h2a h2b (2 * k + 1 + 1))
      (finite_crossK F hn hfin h0a hab h2a h2b (2 * k + 1 + 1 + 1))
      (E.totRank_le a b hab ha h2a h2b hsub)
      (E.finrank_le a b hab ha h2a h2b hsub (2 * k + 1 + 1))
      (E.finrank_le a b hab ha h2a h2b hsub (2 * k + 1 + 1 + 1))).1
  · rw [ite_eq_right hk, add_zero]
    obtain ⟨hd, hl₀, hl₁, hl₁P, hl₂, hl₂P⟩ := E.far a b hab ha h2a h2b hsub k hk
    exact cutPhi_far F hab (k + 1) (2 * k + 1) hV hV' hW
      (finite_HK F hn hfin h0a h2a (2 * k + 1)) (finite_HK F hn hfin h0a h2a (2 * k + 1 + 1))
      (finite_HK F hn hfin h0b h2b (2 * k + 1 + 1))
      (finite_crossK F hn hfin h0a hab h2a h2b (2 * k + 1 + 1)) hd hl₀ hl₁ hl₁P hl₂ hl₂P

/-- The sum over the cutoffs increases by at most 6MN across a crossing of at most one critical
level. -/
theorem sum_pot_cross (E : EventBounds F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite)
    {a b : ℝ} (ha : 0 < a) (hab : 2 * a ≤ 2 * b) (h2a : 2 * a ∉ crit F) (h2b : 2 * b ∉ crit F)
    (hsub : (crit F ∩ Icc (2 * a) (2 * b)).Subsingleton) (K : ℕ) :
    ∑ k ∈ Finset.range K, pot F (2 * b) k ≤
      ∑ k ∈ Finset.range K, pot F (2 * a) k + 6 * (E.M : ℤ) * (E.N : ℤ) := by
  have h1 : ∑ k ∈ Finset.range K, pot F (2 * b) k ≤
      ∑ k ∈ Finset.range K,
        (pot F (2 * a) k + (if k ∈ E.near a b then 6 * (E.M : ℤ) else 0)) :=
    Finset.sum_le_sum fun k _ => pot_cross E hn hfin ha hab h2a h2b hsub k
  rw [Finset.sum_add_distrib] at h1
  have h2 : ∑ k ∈ Finset.range K, (if k ∈ E.near a b then 6 * (E.M : ℤ) else 0) ≤
      6 * (E.M : ℤ) * (E.N : ℤ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    have h3 : ((Finset.range K).filter fun k => k ∈ E.near a b).card ≤ E.N :=
      (Finset.card_le_card fun k hk => (Finset.mem_filter.mp hk).2).trans (E.near_card a b)
    have h4 : (0 : ℤ) ≤ 6 * (E.M : ℤ) := by positivity
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast h3) h4
  linarith

/-- With finitely many prime closed geodesic images and local bounds for single crossings: at a
regular cut 2a the sum over any number of cutoffs of the potentials is at most 6MN times the
number of critical levels in [0, 2a]. -/
theorem sum_pot_le (E : EventBounds F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ}
    (ha : 0 < a) (h2a : 2 * a ∉ crit F) (K : ℕ) :
    ∑ k ∈ Finset.range K, pot F (2 * a) k ≤
      6 * (E.M : ℤ) * (E.N : ℤ) * (levelCount F (2 * a) : ℤ) := by
  have h0a : 0 < 2 * a := by linarith
  refine forall_levelCount F hfin
    (fun x m => ∀ K : ℕ, ∑ k ∈ Finset.range K, pot F x k ≤ 6 * (E.M : ℤ) * (E.N : ℤ) * (m : ℤ))
    ?_ ?_ ?_ (2 * a) h0a h2a K
  · obtain ⟨x₀, hx₀, hsmall⟩ := exists_cutPhi_small F
    refine ⟨x₀, hx₀, fun x hx hxx K => ?_⟩
    obtain ⟨c, rfl⟩ : ∃ c, x = 2 * c := ⟨x / 2, by ring⟩
    have hc : 0 < c := by linarith
    rw [Nat.cast_zero, mul_zero]
    exact (Finset.sum_eq_zero fun k _ => hsmall c hc hxx (k + 1) (2 * k + 1)).le
  · intro x y hx hxy hreg m hP K
    obtain ⟨c, rfl⟩ : ∃ c, x = 2 * c := ⟨x / 2, by ring⟩
    obtain ⟨d, rfl⟩ : ∃ d, y = 2 * d := ⟨y / 2, by ring⟩
    have hc : 0 < c := by linarith
    have hcd : c ≤ d := by linarith
    have e : ∑ k ∈ Finset.range K, pot F (2 * d) k = ∑ k ∈ Finset.range K, pot F (2 * c) k :=
      Finset.sum_congr rfl fun k _ =>
        cutPhi_eq_of_regular F hn hfin hc hcd hreg (k + 1) (2 * k + 1)
    rw [e]
    exact hP K
  · intro x y hx hxy hxc hyc hsub m hP K
    obtain ⟨c, rfl⟩ : ∃ c, x = 2 * c := ⟨x / 2, by ring⟩
    obtain ⟨d, rfl⟩ : ∃ d, y = 2 * d := ⟨y / 2, by ring⟩
    have hc : 0 < c := by linarith
    have h1 := sum_pot_cross E hn hfin hc hxy hxc hyc hsub K
    have h2 := hP K
    push_cast
    linarith

/-- With finitely many prime closed geodesic images and local bounds for single crossings, the
sum over the cutoffs of the potentials at a regular cut 2a grows at most linearly in a. -/
theorem exists_sum_pot_le (E : EventBounds F) (hn : 1 ≤ n) (hfin : (primeImages F).Finite) :
    ∃ C : ℕ, ∀ a : ℝ, 0 < a → 2 * a ∉ crit F → ∀ K : ℕ,
      ((∑ k ∈ Finset.range K, pot F (2 * a) k : ℤ) : ℝ) ≤ C * (1 + a) := by
  obtain ⟨C₀, hC₀⟩ := exists_levelCount_le F hfin
  refine ⟨6 * E.M * E.N * C₀ * 2, fun a ha h2a K => ?_⟩
  have h1 := sum_pot_le E hn hfin ha h2a K
  have h2 := hC₀ (2 * a) (by linarith)
  have h3 : ((∑ k ∈ Finset.range K, pot F (2 * a) k : ℤ) : ℝ) ≤
      6 * (E.M : ℝ) * (E.N : ℝ) * (levelCount F (2 * a) : ℝ) := by
    exact_mod_cast h1
  have h4 : (0 : ℝ) ≤ 6 * (E.M : ℝ) * (E.N : ℝ) := by positivity
  have h5 : (C₀ : ℝ) * (1 + 2 * a) ≤ (C₀ : ℝ) * 2 * (1 + a) := by
    have : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg C₀
    nlinarith
  calc ((∑ k ∈ Finset.range K, pot F (2 * a) k : ℤ) : ℝ)
      ≤ 6 * (E.M : ℝ) * (E.N : ℝ) * (levelCount F (2 * a) : ℝ) := h3
    _ ≤ 6 * (E.M : ℝ) * (E.N : ℝ) * ((C₀ : ℝ) * 2 * (1 + a)) :=
        mul_le_mul_of_nonneg_left (h2.trans h5) h4
    _ = ((6 * E.M * E.N * C₀ * 2 : ℕ) : ℝ) * (1 + a) := by
        push_cast
        ring

end

end Finsler.EventSum
