module

public import Finsler.Loop.NormalizedCapShuffleLowDegree
public import Finsler.Loop.SmallNormalizedCapShuffle
public import Finsler.Loop.LocalizedCapCupComponentSource

/-! Low first-degree vanishing survives actual small carriers and a
subsequent arbitrary cup factor. No closure of either cochain is needed. -/

@[expose] public section
namespace Finsler.SmallNormalizedCapShuffleLowDegree

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem ambient_cup_zero (X Y : TopCat.{0}) (a b d p j q : ℕ)
    (hd : a + b = d) (hN : d + q = p + j) (hp : p < a)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ)
    (ψ : singularCochainGroup (ZMod 2) (X ⊗ Y) b) :
    SingularChainCross.component X Y p j ≫
      absoluteChain (X ⊗ Y) d q (p + j) hN
        (CupOne.cup (X ⊗ Y) a b d hd
          (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) ψ) = 0 := by
  rw [← LocalizedCapCupComponentSource.cap_cup_input (X ⊗ Y) a b d q (p + j) hd hN.symm,
    ← Category.assoc, NormalizedCapShuffleLowDegree.component_cap_zero X Y a p j (b + q)
      (by omega) hp φ hφ, zero_comp]

variable {X Y : TopCat.{0}} {ι κ : Type} (U : ι → Set X) (V : κ → Set Y)

theorem component_cap_zero (a p j q : ℕ) (hN : a + q = p + j) (hp : p < a)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ) :
    SmallNormalizedCapShuffle.component (X := X) (Y := Y) U V p j ≫
      SmallCapCarrier.smallCap (X ⊗ Y) (SmallRectangleShuffle.rectangles (X := X) (Y := Y) U V)
        a q (p + j) hN (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) = 0 := by
  haveI : Mono ((inclusion (X ⊗ Y) (SmallRectangleShuffle.rectangles U V)).f q) :=
    inferInstanceAs (Mono ((sigmaConst.obj coeff).map
      (((X ⊗ Y).smallSingularSubcomplex (SmallRectangleShuffle.rectangles U V)).ι.app (Opposite.op ⦋q⦌))))
  apply (cancel_mono ((inclusion (X ⊗ Y) (SmallRectangleShuffle.rectangles U V)).f q)).mp
  rw [zero_comp, Category.assoc, SmallCapCarrier.smallCap_inclusion, ← Category.assoc,
    SmallNormalizedCapShuffle.component_inclusion, Category.assoc,
    NormalizedCapShuffleLowDegree.component_cap_zero X Y a p j q hN hp φ hφ, comp_zero]

theorem component_cup_zero (a b d p j q : ℕ) (hd : a + b = d) (hN : d + q = p + j) (hp : p < a)
    (φ : singularCochainGroup (ZMod 2) X a)
    (hφ : DoldKan.DegeneraciesVanish (X := SingularNormalization.linearization X) φ)
    (ψ : singularCochainGroup (ZMod 2) (X ⊗ Y) b) :
    SmallNormalizedCapShuffle.component (X := X) (Y := Y) U V p j ≫
      SmallCapCarrier.smallCap (X ⊗ Y) (SmallRectangleShuffle.rectangles (X := X) (Y := Y) U V)
        d q (p + j) hN (CupOne.cup (X ⊗ Y) a b d hd
          (cochainPullback (CartesianMonoidalCategory.fst X Y) a φ) ψ) = 0 := by
  haveI : Mono ((inclusion (X ⊗ Y) (SmallRectangleShuffle.rectangles U V)).f q) :=
    inferInstanceAs (Mono ((sigmaConst.obj coeff).map
      (((X ⊗ Y).smallSingularSubcomplex (SmallRectangleShuffle.rectangles U V)).ι.app (Opposite.op ⦋q⦌))))
  apply (cancel_mono ((inclusion (X ⊗ Y) (SmallRectangleShuffle.rectangles U V)).f q)).mp
  rw [zero_comp, Category.assoc, SmallCapCarrier.smallCap_inclusion, ← Category.assoc,
    SmallNormalizedCapShuffle.component_inclusion, Category.assoc,
    ambient_cup_zero X Y a b d p j q hd hN hp φ hφ ψ, comp_zero]

end
end Finsler.SmallNormalizedCapShuffleLowDegree
