module

public import Finsler.Loop.FirstFactorSectionedPrismSummand
public import Finsler.Loop.SmallNormalizedCapShuffle
public import Finsler.Topology.FactorwiseSubdivisionComparison

/-! The actual sectioned first-factor time prism followed by factorwise
subdivision and the small cross, with explicit native degree transports. -/

@[expose] public section
namespace Finsler.FirstFactorSectionedSmallCross

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology TauCeti
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem summand_map {C D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    (f : C ⊗ D ⟶ E) (j k N : ℕ) (hN : j + k = N) :
    ιTensorObj C D j k N hN ≫ f.f N =
      (ιTensorObj C D j k (j + k) rfl ≫ f.f (j + k)) ≫
        eqToHom (congrArg E.X hN) := by
  subst N
  simp only [eqToHom_refl, Category.comp_id]

variable {X Y : TopCat.{0}} {ι κ : Type}
  (U : ι → Set (ClosedInterval × X)) (V : κ → Set Y)
  (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
  (hV : ∀ i, IsOpen (V i)) (hcV : ⋃ i, V i = Set.univ)

def timePrefix (j L : ℕ) (hL : j + 1 = L) :=
  FirstFactorSectionedPrismSummand.firstPrefix (X := X) U hU hcU j ≫
    eqToHom (congrArg (small (TopCat.of (ClosedInterval × X)) U).X hL)

theorem on_summand (j k N : ℕ) (hN : j + k = N) :
    ιTensorObj (chains X) (chains Y) j k N hN ≫
      (FirstFactorSectionedPrismSummand.inputRetraction (X := X) (Y := Y) U V hU hcU hV hcV).f N ≫
      (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom N (N + 1) ≫
      (FactorwiseSubdivisionComparison.factorwise (X := TopCat.of (ClosedInterval × X)) (Y := Y)
        U V hU hcU hV hcV).f (N + 1) =
    (FirstFactorSectionedPrismSummand.firstPrefix (X := X) U hU hcU j ⊗ₘ
      (smallSingularRetraction (X := Y) coeff V hV hcV).f k) ≫
      SmallNormalizedCapShuffle.component (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V (j + 1) k ≫
      eqToHom (congrArg (small (TopCat.of (ClosedInterval × X) ⊗ Y)
        (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V)).X (show (j + 1) + k = N + 1 by omega)) := by
  subst N
  have hs := congrArg (fun f => f ≫
    (SmallRectangleCross.cross (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V).f (j + k + 1))
    (FirstFactorSectionedPrismSummand.on_summand (X := X) (Y := Y) U V hU hcU hV hcV j k)
  have ht := summand_map
    (SmallRectangleCross.cross (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V)
    (j + 1) k (j + k + 1) (by omega)
  simp only [Category.assoc] at hs
  simp only [Category.assoc] at ht
  calc
    _ = (FirstFactorSectionedPrismSummand.firstPrefix (X := X) U hU hcU j ⊗ₘ
      (smallSingularRetraction (X := Y) coeff V hV hcV).f k) ≫
      ιTensorObj (small (TopCat.of (ClosedInterval × X)) U) (small Y V)
        (j + 1) k (j + k + 1) (by omega) ≫
      (SmallRectangleCross.cross (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V).f (j + k + 1) := by
        simpa only [FactorwiseSubdivisionComparison.factorwise,
          FirstFactorSectionedPrismSummand.cylinderRetraction, HomologicalComplex.comp_f,
          Category.assoc] using hs
    _ = _ := by rw [ht]; rfl

theorem on_summand_regraded (j k N L : ℕ) (hN : j + k = N) (hL : j + 1 = L) :
    ιTensorObj (chains X) (chains Y) j k N hN ≫
      (FirstFactorSectionedPrismSummand.inputRetraction (X := X) (Y := Y) U V hU hcU hV hcV).f N ≫
      (FirstFactorTensorTimePrismComparison.prism (X := X) (Y := Y) U V).hom N (N + 1) ≫
      (FactorwiseSubdivisionComparison.factorwise (X := TopCat.of (ClosedInterval × X)) (Y := Y)
        U V hU hcU hV hcV).f (N + 1) =
    (timePrefix (X := X) U hU hcU j L hL ⊗ₘ (smallSingularRetraction (X := Y) coeff V hV hcV).f k) ≫
      SmallNormalizedCapShuffle.component (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V L k ≫
      eqToHom (congrArg (small (TopCat.of (ClosedInterval × X) ⊗ Y)
        (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V)).X (show L + k = N + 1 by omega)) := by
  subst L
  simpa only [timePrefix, eqToHom_refl, Category.comp_id] using
    on_summand (X := X) (Y := Y) U V hU hcU hV hcV j k N hN

end
end Finsler.FirstFactorSectionedSmallCross
