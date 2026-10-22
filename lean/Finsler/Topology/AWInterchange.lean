/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Finsler.Topology.AWInterchangeSSet
public import TauCeti.AlgebraicTopology.Singular.AlexanderWhitney
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-!
# The singular Alexander–Whitney map and the interchange of factors

For spaces `X` and `Y`, the Alexander–Whitney map `C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` on
singular chains, followed by the Koszul braiding `x ⊗ y ↦ (-1)^(p * q) y ⊗ x`, is chain homotopic
to the map induced by the swap `X × Y ⟶ Y × X` and the coefficient braiding, followed by the
Alexander–Whitney map of `Y × X` (`TopCat.alexanderWhitneyKoszulBraidingHomotopy`).  Precomposing
with the diagonal, the Alexander–Whitney diagonal of a coefficient morphism `u : T ⟶ R ⊗ S`
followed by the Koszul braiding is chain homotopic to the Alexander–Whitney diagonal of
`u ≫ (β_ R S).hom` (`TopCat.alexanderWhitneyDiagonalKoszulBraidingHomotopy`).  This is the
chain-level form of the graded commutativity of the cup product.

Both homotopies are transported from the simplicial statement
`Finsler.AWInterchangeSSet.alexanderWhitneyKoszulBraidingHomotopy` along the comparison map
`Sing (X × Y) ⟶ Sing X × Sing Y`, which commutes with the swaps
(`CategoryTheory.product_comparison_swap`).

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2, Theorem 3.11.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe w v u

namespace Finsler.AWInterchange

open TopCat

private theorem product_comparison_swap {C D : Type*} [Category* C] [Category* D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) (A B : C) :
    F.map (β_ A B).hom ≫ CartesianMonoidalCategory.prodComparison F B A =
      CartesianMonoidalCategory.prodComparison F A B ≫ (β_ (F.obj A) (F.obj B)).hom := by
  ext <;> simp [← Functor.map_comp]

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [BraidedCategory C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]

/-- **The singular Alexander–Whitney map commutes with the interchange of factors up to
homotopy**: the Alexander–Whitney map `C(X × Y; R ⊗ S) ⟶ C(X; R) ⊗ C(Y; S)` followed by the Koszul
braiding, `x ⊗ y ↦ (-1)^(p * q) y ⊗ x` in bidegree `(p, q)`, is chain homotopic to the coefficient
braiding `R ⊗ S ⟶ S ⊗ R` followed by the map induced by the swap `X × Y ⟶ Y × X` and the
Alexander–Whitney map of `Y × X`. -/
def alexanderWhitneyKoszulBraidingHomotopy (X Y : TopCat.{w}) (R S : C) :
    Homotopy (alexanderWhitney X Y R S ≫ TauCeti.NatChainComplex.koszulBraidingHom
        ((toSSet.obj X).chainComplex R) ((toSSet.obj Y).chainComplex S))
      (((SSet.chainComplexFunctor C).map (β_ R S).hom).app (toSSet.obj (X ⊗ Y)) ≫
        SSet.chainComplexMap (toSSet.map (β_ X Y).hom) (S ⊗ R) ≫ alexanderWhitney Y X S R) :=
  (Homotopy.ofEq (by rw [alexanderWhitney_def, Category.assoc])).trans <|
    ((Finsler.AWInterchangeSSet.alexanderWhitneyKoszulBraidingHomotopy (toSSet.obj X) (toSSet.obj Y) R S).compLeft
      (SSet.chainComplexMap (CartesianMonoidalCategory.prodComparison toSSet X Y)
        (R ⊗ S))).trans <|
      Homotopy.ofEq <| by
        rw [alexanderWhitney_def, ← NatTrans.naturality_assoc, ← Functor.map_comp_assoc,
          ← product_comparison_swap, Functor.map_comp_assoc,
          NatTrans.naturality_assoc, NatTrans.naturality_assoc]

variable {R S T : C}

/-- **The Alexander–Whitney diagonal commutes with the interchange of factors up to homotopy**:
the Alexander–Whitney diagonal `C(X; T) ⟶ C(X; R) ⊗ C(X; S)` of `u : T ⟶ R ⊗ S` followed by the
Koszul braiding is chain homotopic to the Alexander–Whitney diagonal of `u ≫ (β_ R S).hom`. -/
def alexanderWhitneyDiagonalKoszulBraidingHomotopy (X : TopCat.{w}) (u : T ⟶ R ⊗ S) :
    Homotopy (X.alexanderWhitneyDiagonal u ≫ TauCeti.NatChainComplex.koszulBraidingHom
        ((toSSet.obj X).chainComplex R) ((toSSet.obj X).chainComplex S))
      (X.alexanderWhitneyDiagonal (u ≫ (β_ R S).hom)) :=
  (Homotopy.ofEq (by simp only [TauCeti.alexanderWhitneyDiagonal_def, Category.assoc])).trans <|
    ((alexanderWhitneyKoszulBraidingHomotopy X X R S).compLeft
      (((SSet.chainComplexFunctor C).map u).app _ ≫
        SSet.chainComplexMap (toSSet.map (lift (𝟙 X) (𝟙 X))) (R ⊗ S))).trans <|
      Homotopy.ofEq <| by
        rw [TauCeti.alexanderWhitneyDiagonal_def, Category.assoc, NatTrans.naturality_assoc,
          ← Functor.map_comp_assoc, ← Functor.map_comp, lift_braiding_hom, Functor.map_comp,
          NatTrans.comp_app,
          Category.assoc]

private theorem singular_diagonal (X : TopCat.{w}) :
    toSSet.map (lift (𝟙 X) (𝟙 X)) ≫
        CartesianMonoidalCategory.prodComparison toSSet X X =
      lift (𝟙 (toSSet.obj X)) (𝟙 (toSSet.obj X)) := by
  ext <;> simp [← Functor.map_comp]

private def preDiagonal (X : TopCat.{w}) (u : T ⟶ R ⊗ S) :
    (toSSet.obj X).chainComplex T ⟶
      (toSSet.obj X ⊗ toSSet.obj X).chainComplex (R ⊗ S) :=
  ((SSet.chainComplexFunctor C).map u).app _ ≫
    SSet.chainComplexMap (lift (𝟙 (toSSet.obj X)) (𝟙 (toSSet.obj X))) (R ⊗ S)

private theorem preDiagonal_factor (X : TopCat.{w}) (u : T ⟶ R ⊗ S) :
    ((SSet.chainComplexFunctor C).map u).app _ ≫
        SSet.chainComplexMap (toSSet.map (lift (𝟙 X) (𝟙 X))) (R ⊗ S) ≫
          SSet.chainComplexMap (CartesianMonoidalCategory.prodComparison toSSet X X) (R ⊗ S) =
      preDiagonal X u := by
  rw [← Functor.map_comp, singular_diagonal]
  rfl

private theorem preDiagonal_natural {X Y : TopCat.{w}} (f : X ⟶ Y) (u : T ⟶ R ⊗ S) :
    SSet.chainComplexMap (toSSet.map f) T ≫ preDiagonal Y u =
      preDiagonal X u ≫ SSet.chainComplexMap (toSSet.map f ⊗ₘ toSSet.map f) (R ⊗ S) := by
  have hΔ : toSSet.map f ≫ lift (𝟙 (toSSet.obj Y)) (𝟙 (toSSet.obj Y)) =
      lift (𝟙 (toSSet.obj X)) (𝟙 (toSSet.obj X)) ≫ (toSSet.map f ⊗ₘ toSSet.map f) := by
    ext <;> simp
  dsimp [preDiagonal]
  rw [← Category.assoc, NatTrans.naturality, Category.assoc, ← Functor.map_comp,
    hΔ, Functor.map_comp, ← Category.assoc]

private theorem diagonal_hom_formula (X : TopCat.{w}) (u : T ⟶ R ⊗ S) (i j : ℕ) :
    (alexanderWhitneyDiagonalKoszulBraidingHomotopy X u).hom i j =
      (preDiagonal X u).f i ≫
        (Finsler.AWInterchangeSSet.alexanderWhitneyKoszulBraidingHomotopy
          (toSSet.obj X) (toSSet.obj X) R S).hom i j := by
  simp only [alexanderWhitneyDiagonalKoszulBraidingHomotopy,
    alexanderWhitneyKoszulBraidingHomotopy, Homotopy.trans_hom, Homotopy.ofEq_hom,
    Homotopy.compLeft_hom, Pi.zero_apply, zero_add, add_zero]
  have hp := congrArg (fun F => F.f i ≫
    (Finsler.AWInterchangeSSet.alexanderWhitneyKoszulBraidingHomotopy
      (toSSet.obj X) (toSSet.obj X) R S).hom i j) (preDiagonal_factor X u)
  simpa only [HomologicalComplex.comp_f, Category.assoc] using hp

/-- Naturality of the actual diagonal interchange homotopy, before passing to classes. -/
theorem diagonal_hom_naturality {X Y : TopCat.{w}} (f : X ⟶ Y) (u : T ⟶ R ⊗ S) (i j : ℕ) :
    (SSet.chainComplexMap (toSSet.map f) T).f i ≫
        (alexanderWhitneyDiagonalKoszulBraidingHomotopy Y u).hom i j =
      (alexanderWhitneyDiagonalKoszulBraidingHomotopy X u).hom i j ≫
        (SSet.chainComplexMap (toSSet.map f) S ⊗ₘ SSet.chainComplexMap (toSSet.map f) R).f j := by
  have hp : (SSet.chainComplexMap (toSSet.map f) T).f i ≫ (preDiagonal Y u).f i =
      (preDiagonal X u).f i ≫
        (SSet.chainComplexMap (toSSet.map f ⊗ₘ toSSet.map f) (R ⊗ S)).f i :=
    congrArg (fun F => F.f i) (preDiagonal_natural f u)
  rw [diagonal_hom_formula, diagonal_hom_formula, ← Category.assoc, hp, Category.assoc,
    Finsler.AWInterchangeSSet.hom_naturality, ← Category.assoc]

/-- The explicit chain boundary identity of the natural interchange homotopy. -/
theorem diagonal_boundary (X : TopCat.{w}) (u : T ⟶ R ⊗ S) (n : ℕ) :
    (X.alexanderWhitneyDiagonal u ≫ TauCeti.NatChainComplex.koszulBraidingHom
        ((toSSet.obj X).chainComplex R) ((toSSet.obj X).chainComplex S)).f (n + 1) =
      ((toSSet.obj X).chainComplex T).d (n + 1) n ≫
          (alexanderWhitneyDiagonalKoszulBraidingHomotopy X u).hom n (n + 1) +
        (alexanderWhitneyDiagonalKoszulBraidingHomotopy X u).hom (n + 1) (n + 2) ≫
          (HomologicalComplex.tensorObj ((toSSet.obj X).chainComplex S)
            ((toSSet.obj X).chainComplex R)).d (n + 2) (n + 1) +
        (X.alexanderWhitneyDiagonal (u ≫ (β_ R S).hom)).f (n + 1) := by
  simpa only [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] using
    (alexanderWhitneyDiagonalKoszulBraidingHomotopy X u).comm (n + 1)


end Finsler.AWInterchange
