module

public import Finsler.Topology.SmallRectangleCross
public import Finsler.Topology.ProductSimplexCarrier
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Pairing

/-! The actual factorwise-small cross product on simplex generators,
including coefficient multiplication. Vanishing on every whole standard
product therefore implies vanishing on the full fixed bidegree summand. -/

@[expose] public section
namespace Finsler.SmallRectangleCrossSimplex

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SmallRectangleShuffle
open Finsler.SingularChainCross
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)
  {j k : ℕ}

def model (σ : (X.smallSingularSubcomplex U : SSet) _⦋j⦌)
    (τ : (Y.smallSingularSubcomplex V : SSet) _⦋k⦌) :
    ((Δ[j] : SSet.{0}) ⊗ Δ[k]) ⟶ ((X ⊗ Y).smallSingularSubcomplex (rectangles U V) : SSet) :=
  (SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫ productLift U V

theorem model_inclusion (σ : (X.smallSingularSubcomplex U : SSet) _⦋j⦌)
    (τ : (Y.smallSingularSubcomplex V : SSet) _⦋k⦌) :
    model U V σ τ ≫ ((X ⊗ Y).smallSingularSubcomplex (rectangles U V)).ι =
      ProductSimplexCarrier.model X Y σ.val τ.val := by
  rw [model, Category.assoc, productLift_inclusion]
  ext n z : 3
  rfl

theorem cross_simplex (N : ℕ) (htotal : j + k = N)
    (σ : (X.smallSingularSubcomplex U : SSet) _⦋j⦌)
    (τ : (Y.smallSingularSubcomplex V : SSet) _⦋k⦌) :
    (((X.smallSingularSubcomplex U : SSet).ιChainComplex (R := coeff) σ) ⊗ₘ
      ((Y.smallSingularSubcomplex V : SSet).ιChainComplex (R := coeff) τ)) ≫
      ιTensorObj (small X U) (small Y V) j k N htotal ≫ (SmallRectangleCross.cross U V).f N =
    (λ_ coeff).hom ≫ SSet.shuffleChain coeff j k N htotal ≫
      (SSet.chainComplexMap (model U V σ τ) coeff).f N := by
  have ht := SSet.ιChainComplex_tensorHom_ιChainComplex_shuffle_f
    (X.smallSingularSubcomplex U : SSet) (Y.smallSingularSubcomplex V : SSet)
    coeff coeff σ τ htotal
  have he := congrArg (fun t => t ≫
    (SSet.chainComplexMap (productLift U V) (coeff ⊗ coeff)).f N ≫
      (coefficient ((X ⊗ Y).smallSingularSubcomplex (rectangles U V) : SSet) (λ_ coeff).hom).f N) ht
  calc
    _ = SSet.shuffleChain (coeff ⊗ coeff) j k N htotal ≫
        (SSet.chainComplexMap (model U V σ τ) (coeff ⊗ coeff)).f N ≫
        (coefficient ((X ⊗ Y).smallSingularSubcomplex (rectangles U V) : SSet)
          (λ_ coeff).hom).f N := by
      simpa only [SmallRectangleCross.cross, SmallRectangleShuffle.shuffle,
        HomologicalComplex.comp_f, Category.assoc, model, Functor.map_comp] using he
    _ = _ := by
      unfold coefficient
      rw [TauCeti.SSet.chainComplexMap_f_chainComplexFunctor_map_app_f,
        ← Category.assoc, SSet.shuffleChain_chainComplexFunctor_map_app_f, Category.assoc]

theorem zero_of_models (N : ℕ) (htotal : j + k = N) {M : ModuleCat.{0} (ZMod 2)}
    (g : (small (X ⊗ Y) (rectangles U V)).X N ⟶ M)
    (hz : ∀ (σ : (X.smallSingularSubcomplex U : SSet) _⦋j⦌)
      (τ : (Y.smallSingularSubcomplex V : SSet) _⦋k⦌),
      (SSet.chainComplexMap (model U V σ τ) coeff).f N ≫ g = 0) :
    ιTensorObj (small X U) (small Y V) j k N htotal ≫
      (SmallRectangleCross.cross U V).f N ≫ g = 0 := by
  apply SSet.tensorChainComplexX_hom_ext
    (K := (X.smallSingularSubcomplex U : SSet)) (L := (Y.smallSingularSubcomplex V : SSet))
    (R := coeff) (S := coeff)
  intro σ τ
  have h := congrArg (fun f => f ≫ g) (cross_simplex U V N htotal σ τ)
  simpa only [Category.assoc, hz σ τ, comp_zero] using h

end
end Finsler.SmallRectangleCrossSimplex
