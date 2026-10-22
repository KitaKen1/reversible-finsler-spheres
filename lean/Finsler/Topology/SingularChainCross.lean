module

public import Finsler.Topology.CochainComparison
public import Finsler.Topology.SmallChainCarrier
public import TauCeti.AlgebraicTopology.Singular.Shuffle
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-! The actual singular shuffle cross product, with coefficient multiplication,
and insertion of a fixed singular simplex in the right factor. -/

@[expose] public section
namespace Finsler.SingularChainCross

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def coefficient (K : SSet.{0}) {M N : ModuleCat.{0} (ZMod 2)} (u : M ⟶ N) :=
  ((SSet.chainComplexFunctor (ModuleCat (ZMod 2))).map u).app K

def component (X Y : TopCat.{0}) (p q : ℕ) :
    (chains X).X p ⊗ (chains Y).X q ⟶ (chains (X ⊗ Y)).X (p + q) :=
  ιTensorObj (chains X) (chains Y) p q (p + q) rfl ≫
    (TopCat.shuffle X Y coeff coeff).f (p + q) ≫
      (coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom).f (p + q)

theorem component_simplex (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ (TopCat.toSSet.obj Y).ιChainComplex τ) ≫
        component X Y p q =
      (λ_ coeff).hom ≫ SSet.shuffleChain coeff p q (p + q) rfl ≫
        (SSet.chainComplexMap ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
          Functor.LaxMonoidal.μ TopCat.toSSet X Y) coeff).f (p + q) := by
  have ht := TopCat.ιChainComplex_tensorHom_ιChainComplex_shuffle_f coeff coeff σ τ rfl
  calc
    _ = (SSet.shuffleChain (coeff ⊗ coeff) p q (p + q) rfl ≫
        (SSet.chainComplexMap ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
          Functor.LaxMonoidal.μ TopCat.toSSet X Y) (coeff ⊗ coeff)).f (p + q)) ≫
        (coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom).f (p + q) := by
      simpa only [component, Category.assoc] using congrArg
        (fun t => t ≫ (coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom).f (p + q)) ht
    _ = _ := by
      unfold coefficient
      rw [Category.assoc, TauCeti.SSet.chainComplexMap_f_chainComplexFunctor_map_app_f,
        ← Category.assoc, SSet.shuffleChain_chainComplexFunctor_map_app_f, Category.assoc]

def right (X Y : TopCat.{0}) (p q : ℕ) (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    (chains X).X p ⟶ (chains (X ⊗ Y)).X (p + q) :=
  (ρ_ ((chains X).X p)).inv ≫
    (((chains X).X p) ◁ (TopCat.toSSet.obj Y).ιChainComplex τ) ≫ component X Y p q

theorem right_simplex (X Y : TopCat.{0}) (p q : ℕ)
    (σ : TopCat.toSSet.obj X _⦋p⦌) (τ : TopCat.toSSet.obj Y _⦋q⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ right X Y p q τ =
      SSet.shuffleChain coeff p q (p + q) rfl ≫
        (SSet.chainComplexMap ((SSet.yonedaEquiv.symm σ ⊗ₘ SSet.yonedaEquiv.symm τ) ≫
          Functor.LaxMonoidal.μ TopCat.toSSet X Y) coeff).f (p + q) := by
  have ht : ((TopCat.toSSet.obj X).ιChainComplex (R := coeff) σ ▷ (𝟙_ (ModuleCat (ZMod 2)))) ≫
      ((chains X).X p ◁ (TopCat.toSSet.obj Y).ιChainComplex (R := coeff) τ) =
    (TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ (TopCat.toSSet.obj Y).ιChainComplex τ :=
    (tensorHom_def _ _).symm
  have he : (λ_ coeff).hom = (ρ_ coeff).hom := by
    change (λ_ (𝟙_ (ModuleCat (ZMod 2)))).hom = (ρ_ (𝟙_ (ModuleCat (ZMod 2)))).hom
    exact unitors_equal
  calc
    _ = (ρ_ coeff).inv ≫ ((TopCat.toSSet.obj X).ιChainComplex σ ⊗ₘ
        (TopCat.toSSet.obj Y).ιChainComplex τ) ≫ component X Y p q := by
      unfold right
      rw [← Category.assoc, rightUnitor_inv_naturality]
      simpa only [Category.assoc] using congrArg
        (fun t => (ρ_ coeff).inv ≫ t ≫ component X Y p q) ht
    _ = _ := by
      rw [component_simplex, ← Category.assoc, ← Category.assoc,
        he, Iso.inv_hom_id, Category.id_comp]

end
end Finsler.SingularChainCross
