module

public import Finsler.Topology.SmallRectangleCross

/-! The actual simplicial shuffle cross with F2 coefficient
multiplication, its naturality, and its literal map to the singular
cross already used by the geometric operations. -/

@[expose] public section
namespace Finsler.SimplicialChainCross

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SingularChainCross

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

def cross (K L : SSet.{0}) : K.chainComplex coeff ⊗ L.chainComplex coeff ⟶ (K ⊗ L).chainComplex coeff :=
  SSet.shuffle K L coeff coeff ≫ coefficient (K ⊗ L) (λ_ coeff).hom

theorem naturality {K K' L L' : SSet.{0}} (f : K ⟶ K') (g : L ⟶ L') :
    (SSet.chainComplexMap f coeff ⊗ₘ SSet.chainComplexMap g coeff) ≫ cross K' L' =
      cross K L ≫ SSet.chainComplexMap (f ⊗ₘ g) coeff := by
  have hn : SSet.chainComplexMap (f ⊗ₘ g) (coeff ⊗ coeff) ≫ coefficient (K' ⊗ L') (λ_ coeff).hom =
      coefficient (K ⊗ L) (λ_ coeff).hom ≫ SSet.chainComplexMap (f ⊗ₘ g) coeff :=
    (((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).map (λ_ coeff).hom).naturality (f ⊗ₘ g))
  unfold cross
  rw [← Category.assoc, SSet.shuffle_naturality, Category.assoc, hn, Category.assoc]

theorem identity_left {K L L' : SSet.{0}} (g : L ⟶ L') :
    (𝟙 (K.chainComplex coeff) ⊗ₘ SSet.chainComplexMap g coeff) ≫ cross K L' =
      cross K L ≫ SSet.chainComplexMap (𝟙 K ⊗ₘ g) coeff := by
  have hi : SSet.chainComplexMap (𝟙 K) coeff = 𝟙 (K.chainComplex coeff) := by
    change ((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).obj coeff).map (𝟙 K) = _
    rw [CategoryTheory.Functor.map_id]
  simpa only [hi] using naturality (𝟙 K) g

theorem to_top (X Y : TopCat.{0}) :
    cross (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) ≫
      SSet.chainComplexMap (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y) coeff =
      SmallRectangleCross.ambient X Y := by
  have hn : SSet.chainComplexMap (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y)
      (coeff ⊗ coeff) ≫ coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom =
      coefficient (TopCat.toSSet.obj X ⊗ TopCat.toSSet.obj Y) (λ_ coeff).hom ≫
        SSet.chainComplexMap (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y) coeff :=
    (((SSet.chainComplexFunctor (ModuleCat.{0} (ZMod 2))).map (λ_ coeff).hom).naturality
      (CategoryTheory.Functor.LaxMonoidal.μ TopCat.toSSet X Y))
  simpa only [cross, SmallRectangleCross.ambient, TopCat.shuffle_def, Category.assoc] using
    congrArg (fun f => SSet.shuffle (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) coeff coeff ≫ f) hn.symm

end
end Finsler.SimplicialChainCross
