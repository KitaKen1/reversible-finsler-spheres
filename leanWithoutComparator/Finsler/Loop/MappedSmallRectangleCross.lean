module

public import Finsler.Loop.SmallNormalizedCapShuffle
public import Finsler.Loop.SingularCrossComponentNaturality
public import Finsler.Topology.SmallRetractionComparison

/-! The real coefficient-multiplied small external cross is strictly
natural under actual maps of the two factor covers and their rectangle
cover, even when the cover centers lie in a larger parameter space. -/

@[expose] public section
namespace Finsler.MappedSmallRectangleCross

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {X Y X' Y' : TopCat.{0}} {ι κ ι' κ' : Type}
  (U : ι → Set X) (V : κ → Set Y) (U' : ι' → Set X') (V' : κ' → Set Y')
  (f : X ⟶ X') (g : Y ⟶ Y') (r : ι → ι') (s : κ → κ')
  (hf : ∀ i, Set.MapsTo f (U i) (U' (r i))) (hg : ∀ j, Set.MapsTo g (V j) (V' (s j)))

def rectangleMap := SmallRetractionComparison.map
  (SmallRectangleShuffle.rectangles U V) (SmallRectangleShuffle.rectangles U' V') (f ⊗ₘ g)
  (fun ij => (r ij.1, s ij.2)) (fun ij _ hz => ⟨hf ij.1 hz.1, hg ij.2 hz.2⟩)

theorem rectangle_source : rectangleMap U V U' V' f g r s hf hg ≫
    inclusion (X' ⊗ Y') (SmallRectangleShuffle.rectangles U' V') =
    inclusion (X ⊗ Y) (SmallRectangleShuffle.rectangles U V) ≫ push (f ⊗ₘ g) :=
  SmallRetractionComparison.map_inclusion _ _ _ _ _

theorem component (p q : ℕ) :
    ((SmallRetractionComparison.map U U' f r hf).f p ⊗ₘ (SmallRetractionComparison.map V V' g s hg).f q) ≫
      SmallNormalizedCapShuffle.component U' V' p q =
    SmallNormalizedCapShuffle.component U V p q ≫ (rectangleMap U V U' V' f g r s hf hg).f (p + q) := by
  have : Mono ((inclusion (X' ⊗ Y') (SmallRectangleShuffle.rectangles U' V')).f (p + q)) :=
    inferInstanceAs (Mono ((sigmaConst.obj coeff).map
      (((X' ⊗ Y').smallSingularSubcomplex (SmallRectangleShuffle.rectangles U' V')).ι.app (Opposite.op ⦋p + q⦌))))
  apply (cancel_mono ((inclusion (X' ⊗ Y') (SmallRectangleShuffle.rectangles U' V')).f (p + q))).mp
  have hu := congrArg (fun h => h.f p) (SmallRetractionComparison.map_inclusion U U' f r hf)
  have hv := congrArg (fun h => h.f q) (SmallRetractionComparison.map_inclusion V V' g s hg)
  simp only [HomologicalComplex.comp_f] at hu hv
  rw [Category.assoc, SmallNormalizedCapShuffle.component_inclusion,
    ← Category.assoc, tensorHom_comp_tensorHom, hu, hv,
    ← tensorHom_comp_tensorHom, Category.assoc, SingularCrossComponentNaturality.component,
    ← Category.assoc, ← SmallNormalizedCapShuffle.component_inclusion,
    Category.assoc, ← HomologicalComplex.comp_f, ← rectangle_source, HomologicalComplex.comp_f, Category.assoc]

end
end Finsler.MappedSmallRectangleCross
