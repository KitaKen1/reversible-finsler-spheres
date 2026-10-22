module

public import Finsler.Topology.CutRegular
public import Finsler.Topology.GradedStable

/-! Vanishing of the potential at small cuts and for large cutoffs. For small a > 0 the K-Borel
cohomology of (t_{2a}, M) and the reflection Borel cohomology of its fixed pair vanish, so the
potential of every cutoff at 2a is zero. With finitely many prime closed geodesic images, at a
regular cut 2a restriction to the fixed pair is bijective on K-Borel cohomology in high degrees;
since the components of an iterated Borel class for a trivial second involution are arbitrary,
the total normalized restriction is then bijective in high degrees, and the reflection groups of
the fixed pair vanish in high degrees. Hence the potential of a large cutoff in high degrees is
zero. -/

@[expose] public section

namespace Finsler.CutStable

open CategoryTheory Set Module
open Finsler.Geometry Finsler.Geodesics Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.SobolevReverse Finsler.SobolevEnergy Finsler.SobolevReflectionAction
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.BorelIterate Finsler.BorelK Finsler.BorelFixed Finsler.BorelExact
open Finsler.BorelFreeK Finsler.AvoidPoint Finsler.BorelDeformation Finsler.BorelLocalK
open Finsler.BorelCoverK Finsler.LocalCoverK Finsler.TotalExact Finsler.GradedLadder
open Finsler.FixedLadder Finsler.LadderEvent Finsler.CutPotential Finsler.CutFinite
open Finsler.CriticalLevels Finsler.FiniteCut Finsler.LocalizeK Finsler.TrivialK
open Finsler.FixedGlobal Finsler.NilpotentWK Finsler.GradedStable

noncomputable section

variable {n : ℕ} (F : ReversibleMetric n)

/-- At small cuts the potential of every cutoff is zero. -/
theorem exists_cutPhi_small :
    ∃ x₀ : ℝ, 0 < x₀ ∧ ∀ a : ℝ, 0 < a → 2 * a ≤ x₀ → ∀ j q, cutPhi F (2 * a) j q = 0 := by
  obtain ⟨b₀, hb₀, hK⟩ := exists_HK_lev_eq_zero F
  obtain ⟨b₁, hb₁, hR⟩ := Finsler.SmallLevel.exists_HR_lev_eq_zero F
  refine ⟨min b₀ (2 * b₁), lt_min hb₀ (by linarith), fun a ha hx j q => ?_⟩
  have h2a : 0 < 2 * a := by linarith
  have hab : a ≤ b₁ := by linarith [min_le_right b₀ (2 * b₁)]
  have hfix : ∀ l (x : fixR F (2 * a) l), x = 0 := fun l x =>
    HR_fix_eq_zero F (Q := 0) (fun p _ z => hR a ha hab p z) l (Nat.zero_le l) x
  unfold cutPhi phi
  exact gphi_eq_zero_of_vanish (fixR F (2 * a)) hfix
    (fun y => hK (2 * a) h2a (hx.trans (min_le_left _ _)) (q + 1) y) j _ _

/-- With finitely many prime closed geodesic images, at a regular cut 2a the total normalized
restriction is bijective in high degrees. -/
theorem exists_epsTot_bijective (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ}
    (ha : 0 < a) (h2a : 2 * a ∉ crit F) :
    ∃ Q : ℕ, (∀ l, Q ≤ l → ∀ x : fixR F (2 * a) l, x = 0) ∧ ∀ p, Q ≤ p →
      Function.Bijective (epsTot (consts_subset_lev F (2 * a)) kInv_consts (kInv_lev F (2 * a))
        (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a)) subset_rfl
        (fixLev_subset_lev F (2 * a)) (half_fixLev F (2 * a)) p) := by
  obtain ⟨Q₀, hbij⟩ := exists_bijective_fixed F hn hfin ha h2a
  obtain ⟨Q₁, -, hz⟩ := exists_fixR_finite F hn hfin ha h2a
  refine ⟨max Q₀ Q₁, fun l hl x => hz l (le_trans (le_max_right _ _) hl) x, fun p hp => ?_⟩
  have hp₀ : Q₀ ≤ p := le_trans (le_max_left _ _) hp
  have hp₁ : Q₁ ≤ p := le_trans (le_max_right _ _) hp
  constructor
  · intro x x' hxx
    have h1 := res_eq_zero_of_eps (consts_subset_lev F (2 * a)) kInv_consts
      (kInv_lev F (2 * a)) (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a))
      subset_rfl (fixLev_subset_lev F (2 * a)) (half_fixLev F (2 * a)) p (x - x')
      (fun l _ => by
        rw [map_sub, sub_eq_zero]
        exact congrFun hxx l)
    exact sub_eq_zero.mp ((hbij p hp₀).1 (h1.trans (map_zero _).symm))
  · intro y
    obtain ⟨x, hx⟩ := (hbij p hp₀).2
      ((trivSplit (kCommuting (consts_subset_fixLev F (2 * a)) kInv_consts
        (kInv_fixLev F (2 * a)))
        (kCommuting_trivial (consts_subset_fixLev F (2 * a)) kInv_consts
          (kInv_fixLev F (2 * a)) (half_fixLev F (2 * a))) p).symm fun l : Fin (p + 1) => y l)
    refine ⟨x, funext fun l => ?_⟩
    by_cases hl : l ≤ p
    · have h1 := congrFun ((trivSplit (kCommuting (consts_subset_fixLev F (2 * a)) kInv_consts
        (kInv_fixLev F (2 * a)))
        (kCommuting_trivial (consts_subset_fixLev F (2 * a)) kInv_consts
          (kInv_fixLev F (2 * a)) (half_fixLev F (2 * a))) p).apply_symm_apply
        fun l : Fin (p + 1) => y l) ⟨l, Nat.lt_succ_of_le hl⟩
      exact (congrArg (fun z => trivSplit (kCommuting (consts_subset_fixLev F (2 * a))
        kInv_consts (kInv_fixLev F (2 * a)))
        (kCommuting_trivial (consts_subset_fixLev F (2 * a)) kInv_consts
          (kInv_fixLev F (2 * a)) (half_fixLev F (2 * a))) p z ⟨l, Nat.lt_succ_of_le hl⟩)
        hx).trans h1
    · have hl' : p < l := Nat.not_le.mp hl
      exact (eps_high (consts_subset_lev F (2 * a)) kInv_consts (kInv_lev F (2 * a))
        (consts_subset_fixLev F (2 * a)) kInv_consts (kInv_fixLev F (2 * a)) subset_rfl
        (fixLev_subset_lev F (2 * a)) (half_fixLev F (2 * a)) p l hl' x).trans
        (hz l (by omega) (y l)).symm

/-- With finitely many prime closed geodesic images, at a regular cut 2a the potential of a
large cutoff in high degrees is zero. -/
theorem exists_cutPhi_stable (hn : 1 ≤ n) (hfin : (primeImages F).Finite) {a : ℝ} (ha : 0 < a)
    (h2a : 2 * a ∉ crit F) :
    ∃ J : ℕ, ∀ j q, J ≤ j → J ≤ q → cutPhi F (2 * a) j q = 0 := by
  obtain ⟨Q, hz, hbij⟩ := exists_epsTot_bijective F hn hfin ha h2a
  refine ⟨Q, fun j q hj hq => ?_⟩
  unfold cutPhi phi
  exact gphi_eq_zero_of_stable (fixR F (2 * a)) j (fun l hl x => hz l (by omega) x) _ _
    (hbij (q + 1) (by omega)) (hbij q hq).2

end

end Finsler.CutStable
