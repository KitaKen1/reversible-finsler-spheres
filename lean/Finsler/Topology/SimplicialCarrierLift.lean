module

public import Finsler.Topology.SupportedCap
public import Finsler.Topology.SupportedCapNaturality

/-! Lift an actual simplicial map through an actual topological subspace
when every image simplex lies there. Naturality follows from the genuine
subspace inclusion, so this constructs a map of simplicial sets, rather
than unrelated degreewise choices of output chains. -/

@[expose] public section
namespace Finsler.SimplicialCarrierLift

open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem inclusion_injective (X : TopCat.{0}) (D : Set X) (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((TopCat.toSSet.map (SupportedCap.subspaceMap X D)).app n) := by
  intro σ τ h
  apply ((TopCat.of D).toSSetObjEquiv n).injective
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  have hh := congrArg (fun z => X.toSSetObjEquiv n z t) h
  simpa [TauCeti.TopCat.toSSetObjEquiv_toSSet_map_app, SupportedCap.subspaceMap] using hh

variable (X : TopCat.{0}) (D : Set X) {K : SSet.{0}} (G : K ⟶ TopCat.toSSet.obj X)
  (hG : ∀ (n : ℕ) (σ : K _⦋n⦌), Set.range (X.toSSetObjEquiv _ (G.app _ σ)) ⊆ D)

def lift : K ⟶ TopCat.toSSet.obj (TopCat.of D) where
  app n := TypeCat.ofHom fun σ => SupportedCap.simplexLift X D (G.app n σ) (hG n.unop.len σ)
  naturality n m θ := by
    apply ConcreteCategory.hom_ext
    intro σ
    apply inclusion_injective X D m
    change (TopCat.toSSet.map (SupportedCap.subspaceMap X D)).app m
      (SupportedCap.simplexLift X D (G.app m (K.map θ σ)) (hG _ _)) =
      (TopCat.toSSet.map (SupportedCap.subspaceMap X D)).app m
        ((TopCat.toSSet.obj (TopCat.of D)).map θ
          (SupportedCap.simplexLift X D (G.app n σ) (hG _ _)))
    rw [SupportedCap.simplexLift_image,
      NatTrans.naturality_apply (TopCat.toSSet.map (SupportedCap.subspaceMap X D)) θ,
      SupportedCap.simplexLift_image]
    exact NatTrans.naturality_apply G θ σ

theorem lift_inclusion : lift X D G hG ≫ TopCat.toSSet.map (SupportedCap.subspaceMap X D) = G := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro σ
  exact SupportedCap.simplexLift_image X D (G.app n σ) (hG n.unop.len σ)

theorem chainMap_inclusion :
    SSet.chainComplexMap (lift X D G hG) coeff ≫
      SupportedCapNaturality.push (SupportedCap.subspaceMap X D) = SSet.chainComplexMap G coeff := by
  rw [SupportedCapNaturality.push, ← Functor.map_comp, lift_inclusion]

end
end Finsler.SimplicialCarrierLift
