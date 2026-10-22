module

public import Finsler.Topology.FilteredBilinearLoopProduct
public import Finsler.Topology.TensorCrossEvaluation

/-! Evaluation of the genuine shuffle external product using the actual
Alexander--Whitney map. Coefficient multiplication and its inverse cancel;
the shuffle/AW homotopy, not an asserted Kunneth decomposition, gives the result. -/

@[expose] public section

namespace Finsler.SingularCrossEvaluation

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.ChainEvaluation
open TauCeti.ChainComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def coefficient (X : TopCat.{0}) {M N : ModuleCat.{0} (ZMod 2)} (f : M ⟶ N) :=
  ((SSet.chainComplexFunctor (ModuleCat (ZMod 2))).map f).app (TopCat.toSSet.obj X)

def diagonal (X Y : TopCat.{0}) :
    chains (TopCat.of (X × Y)) ⟶ HomologicalComplex.tensorObj (chains X) (chains Y) :=
  coefficient (X ⊗ Y) (λ_ coeff).inv ≫ TopCat.alexanderWhitney X Y coeff coeff

theorem coefficient_inverse (X : TopCat.{0}) :
    coefficient X (λ_ coeff).hom ≫ coefficient X (λ_ coeff).inv =
      𝟙 ((TopCat.toSSet.obj X).chainComplex (coeff ⊗ coeff)) := by
  unfold coefficient
  rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id]
  rfl

theorem cross_diagonal (X Y : TopCat.{0}) (i j m : ℕ) (h : i + j = m) :
    FilteredBilinearLoopProduct.crossMap X Y i j m h ≫ homologyMap (diagonal X Y) m =
      homologyCross (chains X) (chains Y) i j m h := by
  change (TopCat.singularHomologyCross X Y coeff coeff i j m h ≫
      homologyMap (coefficient (X ⊗ Y) (λ_ coeff).hom) m) ≫
        homologyMap (coefficient (X ⊗ Y) (λ_ coeff).inv ≫
          TopCat.alexanderWhitney X Y coeff coeff) m = _
  rw [homologyMap_comp, Category.assoc, ← Category.assoc
    (homologyMap (coefficient (X ⊗ Y) (λ_ coeff).hom) m),
    ← homologyMap_comp, coefficient_inverse]
  have hid := HomologicalComplex.homologyMap_id
    ((TopCat.toSSet.obj (X ⊗ Y)).chainComplex (coeff ⊗ coeff)) m
  calc
    _ = TopCat.singularHomologyCross X Y coeff coeff i j m h ≫
        homologyMap (TopCat.alexanderWhitney X Y coeff coeff) m := by
      exact (congrArg (fun f => TopCat.singularHomologyCross X Y coeff coeff i j m h ≫
        f ≫ homologyMap (TopCat.alexanderWhitney X Y coeff coeff) m) hid).trans
          (congrArg (TopCat.singularHomologyCross X Y coeff coeff i j m h ≫ ·)
            (Category.id_comp (homologyMap (TopCat.alexanderWhitney X Y coeff coeff) m)))
    _ = _ := TopCat.singularHomologyCross_comp_homologyMap_alexanderWhitney X Y coeff coeff i j m h

def cochain (X Y : TopCat.{0}) (p q : ℕ)
    (φ : (chains X).X p ⟶ coeff) (ψ : (chains Y).X q ⟶ coeff) :
    (chains (TopCat.of (X × Y))).X (p + q) ⟶ coeff :=
  (diagonal X Y).f (p + q) ≫ tensorCochain (ρ_ coeff).hom φ ψ (p + q)

theorem cochain_closed (X Y : TopCat.{0}) (p q : ℕ)
    (φ : (chains X).X p ⟶ coeff) (ψ : (chains Y).X q ⟶ coeff)
    (hφ : (chains X).d (p + 1) p ≫ φ = 0) (hψ : (chains Y).d (q + 1) q ≫ ψ = 0) :
    (chains (TopCat.of (X × Y))).d (p + q + 1) (p + q) ≫ cochain X Y p q φ ψ = 0 := by
  unfold cochain
  rw [← Category.assoc, ← HomologicalComplex.Hom.comm, Category.assoc,
    TensorCrossEvaluation.tensor_closed p q φ ψ hφ hψ, comp_zero]

theorem cross_evaluation (X Y : TopCat.{0}) (p q : ℕ)
    (φ : (chains X).X p ⟶ coeff) (ψ : (chains Y).X q ⟶ coeff)
    (hφ : (chains X).d (p + 1) p ≫ φ = 0) (hψ : (chains Y).d (q + 1) q ≫ ψ = 0) :
    FilteredBilinearLoopProduct.crossMap X Y p q (p + q) rfl ≫
      evaluation (chains (TopCat.of (X × Y))) (p + q) (cochain X Y p q φ ψ)
        (cochain_closed X Y p q φ ψ hφ hψ) =
      (evaluation (chains X) p φ hφ ⊗ₘ evaluation (chains Y) q ψ hψ) ≫ (ρ_ coeff).hom := by
  have he := ChainEvaluation.naturality (chains (TopCat.of (X × Y))) (diagonal X Y) (p + q)
    (tensorCochain (ρ_ coeff).hom φ ψ (p + q))
    (TensorCrossEvaluation.tensor_closed p q φ ψ hφ hψ) (cochain_closed X Y p q φ ψ hφ hψ)
  calc
    _ = FilteredBilinearLoopProduct.crossMap X Y p q (p + q) rfl ≫
        (homologyMap (diagonal X Y) (p + q) ≫
          evaluation (HomologicalComplex.tensorObj (chains X) (chains Y)) (p + q)
            (tensorCochain (ρ_ coeff).hom φ ψ (p + q))
              (TensorCrossEvaluation.tensor_closed p q φ ψ hφ hψ)) :=
      congrArg (FilteredBilinearLoopProduct.crossMap X Y p q (p + q) rfl ≫ ·) he
    _ = _ := by rw [← Category.assoc, cross_diagonal, TensorCrossEvaluation.cross_evaluation]

theorem cross_evaluation_of_ne (X Y : TopCat.{0}) (p q i j : ℕ)
    (h : i + j = p + q) (hi : i ≠ p)
    (φ : (chains X).X p ⟶ coeff) (ψ : (chains Y).X q ⟶ coeff)
    (hφ : (chains X).d (p + 1) p ≫ φ = 0) (hψ : (chains Y).d (q + 1) q ≫ ψ = 0) :
    FilteredBilinearLoopProduct.crossMap X Y i j (p + q) h ≫
      evaluation (chains (TopCat.of (X × Y))) (p + q) (cochain X Y p q φ ψ)
        (cochain_closed X Y p q φ ψ hφ hψ) = 0 := by
  have he := ChainEvaluation.naturality (chains (TopCat.of (X × Y))) (diagonal X Y) (p + q)
    (tensorCochain (ρ_ coeff).hom φ ψ (p + q))
    (TensorCrossEvaluation.tensor_closed p q φ ψ hφ hψ) (cochain_closed X Y p q φ ψ hφ hψ)
  calc
    _ = FilteredBilinearLoopProduct.crossMap X Y i j (p + q) h ≫
        (homologyMap (diagonal X Y) (p + q) ≫
          evaluation (HomologicalComplex.tensorObj (chains X) (chains Y)) (p + q)
            (tensorCochain (ρ_ coeff).hom φ ψ (p + q))
              (TensorCrossEvaluation.tensor_closed p q φ ψ hφ hψ)) :=
      congrArg (FilteredBilinearLoopProduct.crossMap X Y i j (p + q) h ≫ ·) he
    _ = 0 := by
      rw [← Category.assoc, cross_diagonal,
        TensorCrossEvaluation.cross_evaluation_of_ne p q i j h hi φ ψ hφ hψ]


end
end Finsler.SingularCrossEvaluation
