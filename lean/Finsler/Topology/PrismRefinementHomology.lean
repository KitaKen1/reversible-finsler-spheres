module

public import Finsler.Topology.CommonPrismRefinement
public import Finsler.Topology.SmallInclusionHomologyCancellation

/-! Compare source-before-map and target-after-map small approximations
for actual time models inside their genuine target complex. The relative
prism correction is defined on common input cycles, and the actual
small-source homology section removes the input refinement. -/

@[expose] public section
namespace Finsler.PrismRefinementHomology

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

theorem homology_eq (X Y : TopCat.{0}) {ι κ : Type*}
    (U : ι → Set (ClosedInterval × X)) (V : κ → Set Y)
    (hU : ∀ i, IsOpen (U i)) (hcU : ⋃ i, U i = Set.univ)
    (hV : ∀ j, IsOpen (V j)) (hcV : ⋃ j, V j = Set.univ)
    (f : TopCat.of (ClosedInterval × X) ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
    (u : ∀ q, (small Y V).X (d + q + 1) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      (small Y V).d (d + q + 2) (d + q + 1) ≫ u q)
    (a b : DegreeLoweringHomology.Map (chains X) E d)
    (ha : ∀ q, a.component q = AnnularTimeTrim.prism X (d + q) ≫
      (push f ≫ TauCeti.smallSingularRetraction (X := Y) coeff V hV hcV).f (d + q + 1) ≫ u q)
    (hb : ∀ q, b.component q = AnnularTimeTrim.prism X (d + q) ≫
      (TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcU ≫
        SmallRetractionComparison.map (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V f r hf).f
          (d + q + 1) ≫ u q) (q : ℕ) : a.homology q = b.homology q := by
  let S := CommonPrismRefinement.endpointCover X U
  let W : (small X S).cycles (d + q) ⟶ E.X (q + 1) :=
    (small X S).iCycles (d + q) ≫ (inclusion X S).f (d + q) ≫ AnnularTimeTrim.prism X (d + q) ≫
      (SmallRetractionComparison.comparison (X := TopCat.of (ClosedInterval × X)) (Y := Y)
        U V hU hcU hV hcV f r hf).hom (d + q + 1) (d + q + 2) ≫ u (q + 1)
  apply SmallInclusionHomologyCancellation.eq_of_small_boundary X S
    (CommonPrismRefinement.endpointCover_open X U hU) (CommonPrismRefinement.endpointCover_univ X U hcU)
    E d a b q W
  have hh := CommonPrismRefinement.filtered_prism_comparison X U V hU hcU hV hcV f r hf E d u hu q
  simpa only [ha, hb, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc, W] using hh

end
end Finsler.PrismRefinementHomology
