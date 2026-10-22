module

public import Finsler.Topology.SmallRectangleShuffle

/-! Include the actual coefficient multiplication in factorwise small
shuffle cross products, retaining their literal product-cover factorization. -/

@[expose] public section
namespace Finsler.SmallRectangleCross

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SmallRectangleShuffle Finsler.SingularChainCross

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def ambient (X Y : TopCat.{0}) : chains X ⊗ chains Y ⟶ chains (X ⊗ Y) :=
  TopCat.shuffle X Y coeff coeff ≫ coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)

def cross : small X U ⊗ small Y V ⟶ small (X ⊗ Y) (rectangles U V) :=
  SmallRectangleShuffle.shuffle U V ≫
    coefficient ((X ⊗ Y).smallSingularSubcomplex (rectangles U V) : SSet) (λ_ coeff).hom

theorem cross_inclusion :
    cross U V ≫ inclusion (X ⊗ Y) (rectangles U V) =
      (inclusion X U ⊗ₘ inclusion Y V) ≫ ambient X Y := by
  have hn : coefficient ((X ⊗ Y).smallSingularSubcomplex (rectangles U V) : SSet)
        (λ_ coeff).hom ≫ inclusion (X ⊗ Y) (rectangles U V) =
      SSet.chainComplexMap ((X ⊗ Y).smallSingularSubcomplex (rectangles U V)).ι (coeff ⊗ coeff) ≫
        coefficient (TopCat.toSSet.obj (X ⊗ Y)) (λ_ coeff).hom :=
    (((SSet.chainComplexFunctor (ModuleCat (ZMod 2))).map (λ_ coeff).hom).naturality
      ((X ⊗ Y).smallSingularSubcomplex (rectangles U V)).ι).symm
  unfold cross
  rw [Category.assoc, hn, ← Category.assoc, SmallRectangleShuffle.shuffle_inclusion,
    Category.assoc]
  rfl

end
end Finsler.SmallRectangleCross
