/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in Tau Ceti's LICENSE.
The projection calculation is adapted from singularCross_eq_singularCup in
TauCeti/AlgebraicTopology/Cohomology/CrossProduct.lean at the fixed project pin.
-/
module

public import Finsler.Topology.SingularCrossEvaluation
public import Finsler.Topology.PoolCupComparison

/-! The actual external cochain is the existing cup of projection pullbacks.
This is a cochain equality, before quotienting by boundaries. -/

@[expose] public section

namespace Finsler.CrossCupComparison

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicTopology HomologicalComplex SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier
open TauCeti.ChainComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem raw_diagonal_projection (X Y : TopCat.{0}) :
    TopCat.alexanderWhitney X Y coeff coeff =
      (X ⊗ Y).alexanderWhitneyDiagonal (𝟙 (coeff ⊗ coeff)) ≫
        HomologicalComplex.tensorHom
          (SSet.chainComplexMap (TopCat.toSSet.map (fst X Y)) coeff)
          (SSet.chainComplexMap (TopCat.toSSet.map (snd X Y)) coeff) := by
  have hdiag : lift (𝟙 (X ⊗ Y)) (𝟙 (X ⊗ Y)) ≫ (fst X Y ⊗ₘ snd X Y) = 𝟙 (X ⊗ Y) := by
    ext <;> simp
  rw [TauCeti.alexanderWhitneyDiagonal_def,
    (SSet.chainComplexFunctor (ModuleCat (ZMod 2))).map_id]
  simp only [NatTrans.id_app, Category.id_comp, Category.assoc]
  have hD : SSet.chainComplexMap (TopCat.toSSet.map (fst X Y ⊗ₘ snd X Y)) (coeff ⊗ coeff) ≫
        TopCat.alexanderWhitney X Y coeff coeff =
      TopCat.alexanderWhitney (X ⊗ Y) (X ⊗ Y) coeff coeff ≫
        HomologicalComplex.tensorHom
          (SSet.chainComplexMap (TopCat.toSSet.map (fst X Y)) coeff)
          (SSet.chainComplexMap (TopCat.toSSet.map (snd X Y)) coeff) :=
    TopCat.alexanderWhitney_naturality (fst X Y) (snd X Y) coeff coeff
  rw [← hD]
  rw [← Category.assoc,
    ← ((SSet.chainComplexFunctor (ModuleCat (ZMod 2))).obj (coeff ⊗ coeff)).map_comp,
    ← TopCat.toSSet.map_comp, hdiag, TopCat.toSSet.map_id,
    ((SSet.chainComplexFunctor (ModuleCat (ZMod 2))).obj (coeff ⊗ coeff)).map_id,
    Category.id_comp]

theorem diagonal_projection (X Y : TopCat.{0}) :
    SingularCrossEvaluation.diagonal X Y =
      (X ⊗ Y).alexanderWhitneyDiagonal (λ_ coeff).inv ≫
        HomologicalComplex.tensorHom
          (SSet.chainComplexMap (TopCat.toSSet.map (fst X Y)) coeff)
          (SSet.chainComplexMap (TopCat.toSSet.map (snd X Y)) coeff) := by
  unfold SingularCrossEvaluation.diagonal SingularCrossEvaluation.coefficient
  rw [raw_diagonal_projection]
  simp only [TauCeti.alexanderWhitneyDiagonal_def, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp, Category.assoc]
  rfl

theorem cochain_comparison (X Y : TopCat.{0}) (p q : ℕ)
    (φ : singularCochainGroup (ZMod 2) X p) (ψ : singularCochainGroup (ZMod 2) Y q) :
    SingularCrossEvaluation.cochain X Y p q φ ψ =
      cochainCup p q (cochainPullback (fst X Y) p φ) (cochainPullback (snd X Y) q ψ) := by
  have hn := cupCochain_naturality (k := ZMod 2)
    (SingularCrossEvaluation.diagonal X Y) (ρ_ coeff).hom
    ((X ⊗ Y).alexanderWhitneyDiagonal (λ_ coeff).inv)
    (𝟙 (chains (X ⊗ Y)))
    (SSet.chainComplexMap (TopCat.toSSet.map (fst X Y)) coeff)
    (SSet.chainComplexMap (TopCat.toSSet.map (snd X Y)) coeff)
    (by simpa only [Category.id_comp] using diagonal_projection X Y)
    p q (p + q) rfl φ ψ
  have hnative : PoolCupComparison.nativeCup (X ⊗ Y) p q
      (cochainPullback (fst X Y) p φ) (cochainPullback (snd X Y) q ψ) =
      cupCochain (ZMod 2) ((X ⊗ Y).alexanderWhitneyDiagonal (λ_ coeff).inv)
        (ρ_ coeff).hom p q (p + q) rfl
        (cochainPullback (fst X Y) p φ) (cochainPullback (snd X Y) q ψ) := by
    unfold PoolCupComparison.nativeCup
    rfl
  have hc : cupCochain (ZMod 2) ((X ⊗ Y).alexanderWhitneyDiagonal (λ_ coeff).inv)
      (ρ_ coeff).hom p q (p + q) rfl
      (cochainPullback (fst X Y) p φ) (cochainPullback (snd X Y) q ψ) =
        SingularCrossEvaluation.cochain X Y p q φ ψ := by
    calc
      _ = 𝟙 ((chains (X ⊗ Y)).X (p + q)) ≫
          cupCochain (ZMod 2) (SingularCrossEvaluation.diagonal X Y) (ρ_ coeff).hom
            p q (p + q) rfl φ ψ := hn
      _ = cupCochain (ZMod 2) (SingularCrossEvaluation.diagonal X Y) (ρ_ coeff).hom
          p q (p + q) rfl φ ψ := Category.id_comp _
      _ = _ := cupCochain_apply (SingularCrossEvaluation.diagonal X Y) (ρ_ coeff).hom
        p q (p + q) rfl φ ψ
  exact hc.symm.trans (hnative.symm.trans
    (PoolCupComparison.cochain_comparison (X ⊗ Y) p q _ _))


end
end Finsler.CrossCupComparison
