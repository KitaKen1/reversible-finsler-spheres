module

public import Finsler.Topology.CochainComparison
public import TauCeti.AlgebraicTopology.SimplicialSet.Shuffle
import all TauCeti.AlgebraicTopology.SimplicialSet.Shuffle
public import Mathlib.AlgebraicTopology.SimplicialSet.ProdStdSimplexOne

/-! Compare Tau Ceti's recursive shuffle of a simplex with the interval
against the actual nondegenerate prism simplices used by mathlib. -/

@[expose] public section
namespace Finsler.PrismShuffle

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def base (p : ℕ) : ((Δ[p] : SSet.{0}) ⊗ Δ[0]) _⦋p⦌ :=
  (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋p⦌), SSet.stdSimplex.const 0 0 _)

def rect (p : ℕ) (i : Fin (p + 1)) : ((Δ[p] : SSet.{0}) ⊗ Δ[1]) _⦋p + 1⦌ :=
  (SSet.prodStdSimplex₁.nonDegenerateEquiv i).val

theorem cone_base (p : ℕ) :
    SSet.stdSimplex.prodCone
      ((SSet.stdSimplex.δ 0 ▷ (Δ[0] : SSet.{0})).app (Opposite.op ⦋p⦌) (base p)) =
        base (p + 1) := by
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro j
    cases j using Fin.cases with
    | zero => rfl
    | succ j => rfl
  · apply SSet.stdSimplex.ext
    intro j
    exact Subsingleton.elim (α := Fin 1) _ _

theorem cone_vertical (p : ℕ) :
    SSet.stdSimplex.prodCone
      (((Δ[p] : SSet.{0}) ◁ SSet.stdSimplex.δ 0).app (Opposite.op ⦋p⦌) (base p)) =
        rect p 0 := by
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro j
    cases j using Fin.cases with
    | zero =>
      change (0 : Fin (p + 1)) = Fin.predAbove 0 0
      simp
    | succ j =>
      change j = Fin.predAbove 0 j.succ
      simp [Fin.predAbove_zero_succ]
  · apply SSet.stdSimplex.ext
    intro j
    cases j using Fin.cases with
    | zero =>
      change (0 : Fin 2) = SSet.stdSimplex.objMk₁.{0} (0 : Fin (p + 1)).succ.castSucc 0
      symm
      exact SSet.stdSimplex.objMk₁_of_castSucc_lt.{0} _ _ (by simp)
    | succ j =>
      change (1 : Fin 2) = SSet.stdSimplex.objMk₁.{0} (0 : Fin (p + 1)).succ.castSucc j.succ
      symm
      exact SSet.stdSimplex.objMk₁_of_le_castSucc.{0} _ _ (by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ, Fin.val_zero]
        omega)

theorem cone_horizontal (p : ℕ) (i : Fin (p + 1)) :
    SSet.stdSimplex.prodCone
      ((SSet.stdSimplex.δ 0 ▷ (Δ[1] : SSet.{0})).app (Opposite.op ⦋p + 1⦌) (rect p i)) =
        rect (p + 1) i.succ := by
  apply Prod.ext
  · apply SSet.stdSimplex.ext
    intro j
    cases j using Fin.cases with
    | zero =>
      change (0 : Fin (p + 2)) = i.succ.predAbove 0
      simp
    | succ j =>
      change (i.predAbove j).succ = i.succ.predAbove j.succ
      simp
  · apply SSet.stdSimplex.ext
    intro j
    cases j using Fin.cases with
    | zero =>
      change (0 : Fin 2) = SSet.stdSimplex.objMk₁.{0} i.succ.succ.castSucc 0
      symm
      exact SSet.stdSimplex.objMk₁_of_castSucc_lt.{0} _ _ (by simp)
    | succ j =>
      change SSet.stdSimplex.objMk₁.{0} i.succ.castSucc j =
        SSet.stdSimplex.objMk₁.{0} i.succ.succ.castSucc j.succ
      have h : j.castSucc < i.succ.castSucc ↔ j.succ.castSucc < i.succ.succ.castSucc := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
        omega
      simp only [SSet.stdSimplex.objMk₁_apply, h]

theorem shuffle_zero (p : ℕ) :
    SSet.shuffleChain coeff p 0 p (Nat.add_zero p) =
      ((Δ[p] : SSet.{0}) ⊗ Δ[0]).ιChainComplex (base p) := by
  induction p with
  | zero => exact SSet.shuffleChain_zero_zero coeff rfl (base 0)
  | succ p ih =>
    rw [SSet.shuffleChain_succ_zero, ih, ← Category.assoc,
      SSet.ι_chainComplexMap_f, SSet.stdSimplex.ιChainComplex_prodConeChain, cone_base]

private theorem sign_smul {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (p : ℕ) (v : V) : ((-1 : ℤ) ^ p) • v = v := by
  have hs : (((-1 : ℤ) ^ p : ℤ) : ZMod 2) = 1 := by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_eq_self_mod_two, one_pow]
  rw [← Int.cast_smul_eq_zsmul (ZMod 2), hs, one_smul]

theorem shuffle_one (p : ℕ) :
    SSet.shuffleChain coeff p 1 (p + 1) rfl =
      ∑ i : Fin (p + 1), ((Δ[p] : SSet.{0}) ⊗ Δ[1]).ιChainComplex (rect p i) := by
  induction p with
  | zero =>
    rw [SSet.shuffleChain_zero_succ, shuffle_zero, ← Category.assoc,
      SSet.ι_chainComplexMap_f, SSet.stdSimplex.ιChainComplex_prodConeChain, cone_vertical]
    simp
  | succ p ih =>
    rw [SSet.shuffleChain_succ_succ, ih, shuffle_zero, sign_smul]
    simp only [Preadditive.sum_comp, ← Category.assoc, SSet.ι_chainComplexMap_f,
      SSet.stdSimplex.ιChainComplex_prodConeChain, cone_vertical]
    have hh (i : Fin (p + 1)) :
        ((Δ[p + 1] : SSet.{0}) ⊗ Δ[1]).ιChainComplex (R := coeff)
          (SSet.stdSimplex.prodCone ((SSet.stdSimplex.δ 0 ▷ (Δ[1] : SSet.{0})).app
            (Opposite.op ⦋p + 1⦌) (rect p i))) =
        ((Δ[p + 1] : SSet.{0}) ⊗ Δ[1]).ιChainComplex (rect (p + 1) i.succ) :=
      congrArg (fun s => ((Δ[p + 1] : SSet.{0}) ⊗ Δ[1]).ιChainComplex (R := coeff) s)
        (cone_horizontal p i)
    simp only [hh]
    conv_rhs => rw [Fin.sum_univ_succ]
    exact add_comm _ _

end
end Finsler.PrismShuffle
