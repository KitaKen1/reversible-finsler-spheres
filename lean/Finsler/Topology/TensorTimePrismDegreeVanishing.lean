module

public import Finsler.Topology.TensorTimePrismVanishing

/-! Transport the genuine tensor-time vanishing to the actual cap degree.
The cast stays explicit, so no equality of different chain groups is
silently assumed. The prism chain itself need not be a cycle. -/

@[expose] public section
namespace Finsler.TensorTimePrismDegreeVanishing

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem factorwise_zero {X Y : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set (ClosedInterval × Y))
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ v, IsOpen (V v)) (hcV : ⋃ v, V v = Set.univ)
    (j k N : ℕ) (ht : j + k + 1 = N) {M : ModuleCat.{0} (ZMod 2)}
    (g : (small (X ⊗ TopCat.of (ClosedInterval × Y))
      (SmallRectangleShuffle.rectangles (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V)).X N ⟶ M)
    (hz : ιTensorObj (small X U) (small (TopCat.of (ClosedInterval × Y)) V)
      j (k + 1) N (by omega) ≫
      (SmallRectangleCross.cross (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V).f N ≫ g = 0) :
    ιTensorObj (small X U) (small Y (CommonPrismRefinement.endpointCover Y V)) j k (j + k) rfl ≫
      (TensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (j + k) (j + k + 1) ≫
      (FactorwiseSubdivisionComparison.factorwise (X := X) (Y := TopCat.of (ClosedInterval × Y))
        U V hU hcU hV hcV).f (j + k + 1) ≫
      eqToHom (congrArg (small (X ⊗ TopCat.of (ClosedInterval × Y))
        (SmallRectangleShuffle.rectangles (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V)).X ht) ≫ g = 0 := by
  subst N
  simpa only [eqToHom_refl, Category.id_comp] using
    TensorTimePrismVanishing.factorwise_zero (X := X) (Y := Y) U V hU hcU hV hcV j k g hz

end
end Finsler.TensorTimePrismDegreeVanishing
