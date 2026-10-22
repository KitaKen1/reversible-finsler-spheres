module

public import Finsler.Topology.TensorTimePrismComparison

/-! The actual second-input time prism preserves the first degree.
Thus zero of the fixed (j,k+1) small-cross summand kills its actual
factorwise approximation on (j,k), without requiring a closed prism. -/

@[expose] public section
namespace Finsler.TensorTimePrismVanishing

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem factorwise_zero {X Y : TopCat.{0}} {ι κ : Type*}
    (U : ι → Set X) (V : κ → Set (ClosedInterval × Y))
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ v, IsOpen (V v)) (hcV : ⋃ v, V v = Set.univ)
    (j k : ℕ) {M : ModuleCat.{0} (ZMod 2)}
    (g : (small (X ⊗ TopCat.of (ClosedInterval × Y))
      (SmallRectangleShuffle.rectangles (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V)).X (j + k + 1) ⟶ M)
    (hz : ιTensorObj (small X U) (small (TopCat.of (ClosedInterval × Y)) V)
      j (k + 1) (j + k + 1) (by omega) ≫ (SmallRectangleCross.cross (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V).f (j + k + 1) ≫ g = 0) :
    ιTensorObj (small X U) (small Y (CommonPrismRefinement.endpointCover Y V)) j k (j + k) rfl ≫
      (TensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom (j + k) (j + k + 1) ≫
      (FactorwiseSubdivisionComparison.factorwise (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V hU hcU hV hcV).f (j + k + 1) ≫ g = 0 := by
  let rx := smallSingularRetraction (X := X) coeff U hU hcU
  let ry := smallSingularRetraction (X := TopCat.of (ClosedInterval × Y)) coeff V hV hcV
  have hi : ιTensorObj (chains X) (chains (TopCat.of (ClosedInterval × Y)))
      j (k + 1) (j + k + 1) (by omega) ≫ (rx ⊗ₘ ry).f (j + k + 1) =
      (rx.f j ⊗ₘ ry.f (k + 1)) ≫
        ιTensorObj (small X U) (small (TopCat.of (ClosedInterval × Y)) V)
          j (k + 1) (j + k + 1) (by omega) :=
    HomologicalComplex.ι_tensorHom rx ry j (k + 1) (j + k + 1) (by omega)
  have hnat : ιTensorObj (chains X) (chains (TopCat.of (ClosedInterval × Y)))
      j (k + 1) (j + k + 1) (by omega) ≫
      (FactorwiseSubdivisionComparison.factorwise (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V hU hcU hV hcV).f (j + k + 1) =
      (rx.f j ⊗ₘ ry.f (k + 1)) ≫
        ιTensorObj (small X U) (small (TopCat.of (ClosedInterval × Y)) V)
          j (k + 1) (j + k + 1) (by omega) ≫ (SmallRectangleCross.cross (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V).f (j + k + 1) := by
    change _ ≫ ((rx ⊗ₘ ry).f (j + k + 1) ≫ (SmallRectangleCross.cross (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V).f (j + k + 1)) = _
    rw [← Category.assoc, hi, Category.assoc]
  have hx : (inclusion X U).f j ≫ rx.f j = 𝟙 ((small X U).X j) := by
    change (inclusion X U ≫ rx).f j = _
    rw [ι_comp_smallSingularRetraction]
    rfl
  have hraw : ((inclusion X U).f j ⊗ₘ (CommonPrismRefinement.prism Y V).hom k (k + 1)) ≫
      ιTensorObj (chains X) (chains (TopCat.of (ClosedInterval × Y)))
        j (k + 1) (j + k + 1) (by omega) ≫
      (FactorwiseSubdivisionComparison.factorwise (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V hU hcU hV hcV).f (j + k + 1) ≫ g = 0 := by
    rw [← Category.assoc
      (ιTensorObj (chains X) (chains (TopCat.of (ClosedInterval × Y)))
        j (k + 1) (j + k + 1) (by omega))
      ((FactorwiseSubdivisionComparison.factorwise (X := X) (Y := TopCat.of (ClosedInterval × Y))
        U V hU hcU hV hcV).f (j + k + 1)) g, hnat]
    simp only [← Category.assoc]
    rw [tensorHom_comp_tensorHom, hx]
    simpa only [Category.assoc, hz, comp_zero]
  have he := congrArg (fun f => f ≫
    (FactorwiseSubdivisionComparison.factorwise (X := X) (Y := TopCat.of (ClosedInterval × Y)) U V hU hcU hV hcV).f (j + k + 1) ≫ g)
      (TensorTimePrismComparison.on_summand (X := X) (Y := Y) U V j k)
  simpa only [Category.assoc, Linear.units_smul_comp, hraw, smul_zero] using he

end
end Finsler.TensorTimePrismVanishing
