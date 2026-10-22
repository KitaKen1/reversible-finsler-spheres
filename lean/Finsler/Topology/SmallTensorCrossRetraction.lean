module

public import Finsler.Topology.TensorTimePrismComparison

/-! On tensor products of already-small chains, both actual subdivision
orders equal the genuine small cross product. In particular the actual
two time-endpoint maps have identical outputs in both orders. -/

@[expose] public section
namespace Finsler.SmallTensorCrossRetraction

open CategoryTheory MonoidalCategory AlgebraicTopology HomologicalComplex
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ v, IsOpen (V v)) (hcV : ⋃ v, V v = Set.univ)

theorem cross_then_retract :
    (inclusion X U ⊗ₘ inclusion Y V) ≫ SmallRectangleCross.ambient X Y ≫
      FactorwiseSubdivisionComparison.productRetraction U V hU hcU hV hcV =
    SmallRectangleCross.cross U V := by
  rw [← Category.assoc, ← SmallRectangleCross.cross_inclusion, Category.assoc]
  change _ ≫ (inclusion (X ⊗ Y) (SmallRectangleShuffle.rectangles U V) ≫
    smallSingularRetraction (X := X ⊗ Y) coeff (SmallRectangleShuffle.rectangles U V)
      (FactorwiseSubdivisionComparison.rectangles_open U V hU hV)
      (FactorwiseSubdivisionComparison.rectangles_cover U V hcU hcV)) = _
  rw [ι_comp_smallSingularRetraction, Category.comp_id]

theorem factorwise :
    (inclusion X U ⊗ₘ inclusion Y V) ≫
      FactorwiseSubdivisionComparison.factorwise U V hU hcU hV hcV =
    SmallRectangleCross.cross U V := by
  dsimp only [FactorwiseSubdivisionComparison.factorwise]
  rw [← Category.assoc, tensorHom_comp_tensorHom,
    ι_comp_smallSingularRetraction, ι_comp_smallSingularRetraction,
    id_tensorHom_id, Category.id_comp]

end
end Finsler.SmallTensorCrossRetraction
