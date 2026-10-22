module

public import Finsler.Loop.ShuffleWordSimplex
import all TauCeti.AlgebraicTopology.SimplicialSet.Shuffle

/-! The pinned TauCeti shuffle is exactly the finite sum of the
concrete word simplices, in arbitrary degrees over F2. -/

@[expose] public section
namespace Finsler.ShuffleWordChain

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.ShuffleWords Finsler.ShuffleWordSimplex
open scoped Simplicial BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

private theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

theorem shuffle_sum (p q N : ℕ) (hN : p + q = N) :
    SSet.shuffleChain coeff p q N hN =
      ∑ w ∈ words p q, ((Δ[p] : SSet.{0}) ⊗ Δ[q]).ιChainComplex (simplex p q N w) := by
  induction N generalizing p q with
  | zero =>
    obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
    simpa only [words, Finset.sum_singleton] using
      SSet.shuffleChain_zero_zero coeff hN (simplex 0 0 0 [])
  | succ N ih =>
    cases p with
    | zero =>
      cases q with
      | zero => omega
      | succ q =>
        rw [SSet.shuffleChain_zero_succ, ih 0 q (by omega), sum_zero_succ]
        simp only [Preadditive.sum_comp, ← Category.assoc, SSet.ι_chainComplexMap_f,
          SSet.stdSimplex.ιChainComplex_prodConeChain]
        apply Finset.sum_congr rfl
        intro w _
        rw [← vertical_step]
    | succ p =>
      cases q with
      | zero =>
        rw [SSet.shuffleChain_succ_zero, ih p 0 (by omega), sum_succ_zero]
        simp only [Preadditive.sum_comp, ← Category.assoc, SSet.ι_chainComplexMap_f,
          SSet.stdSimplex.ιChainComplex_prodConeChain]
        apply Finset.sum_congr rfl
        intro w _
        rw [← horizontal_step]
      | succ q =>
        rw [SSet.shuffleChain_succ_succ, ih p (q + 1) (by omega), ih (p + 1) q (by omega),
          sign_smul, sum_succ_succ]
        simp only [Preadditive.sum_comp, ← Category.assoc, SSet.ι_chainComplexMap_f,
          SSet.stdSimplex.ιChainComplex_prodConeChain]
        congr 1
        · apply Finset.sum_congr rfl
          intro w _
          rw [← horizontal_step]
        · apply Finset.sum_congr rfl
          intro w _
          rw [← vertical_step]

end
end Finsler.ShuffleWordChain
