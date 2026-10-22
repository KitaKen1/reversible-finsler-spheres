module

public import Finsler.Topology.SmallRectangleCross
public import Finsler.Topology.SupportedCapNaturality

/-! Naturality of the actual singular cross product, including the
coefficient multiplication used by the geometric cap operations. -/

@[expose] public section
namespace Finsler.SmallCrossNaturality

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SmallRectangleCross Finsler.SingularChainCross

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ambient_naturality {X Y X' Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y') :
    (push f ⊗ₘ push g) ≫ ambient X' Y' = ambient X Y ≫ push (f ⊗ₘ g) := by
  have hs : (push f ⊗ₘ push g) ≫ TopCat.shuffle X' Y' coeff coeff =
      TopCat.shuffle X Y coeff coeff ≫
        SSet.chainComplexMap (TopCat.toSSet.map (f ⊗ₘ g)) (coeff ⊗ coeff) :=
    TopCat.shuffle_naturality f g coeff coeff
  have hn : SSet.chainComplexMap (TopCat.toSSet.map (f ⊗ₘ g)) (coeff ⊗ coeff) ≫
      coefficient (TopCat.toSSet.obj (X' ⊗ Y')) (λ_ coeff).hom =
      coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom ≫ push (f ⊗ₘ g) :=
    (((SSet.chainComplexFunctor (ModuleCat (ZMod 2))).map (λ_ coeff).hom).naturality
      (TopCat.toSSet.map (f ⊗ₘ g)))
  unfold ambient
  rw [← Category.assoc, hs, Category.assoc, hn, Category.assoc]

end
end Finsler.SmallCrossNaturality
