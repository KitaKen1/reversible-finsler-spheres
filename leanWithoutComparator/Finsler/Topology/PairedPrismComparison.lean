module

public import Finsler.Topology.CommonPrismRefinement
public import Finsler.Topology.SmallFilteredMapAgreement

/-! If two original parameter maps give identical filtered outputs on
one actual source refinement, their original time-prism outputs differ
by the explicit difference of their two actual retraction-naturality
comparisons. All comparison chains take values in the given filtered
target complex, and the noncycle time-prism boundary terms vanish. -/

@[expose] public section
namespace Finsler.PairedPrismComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem paired_boundary (X : TopCat.{0}) {ι κ : Type*}
    (U : ι → Set (ClosedInterval × X)) (Y : TopCat.{0}) (V : κ → Set Y)
    (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
    (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)
    (f₀ f₁ : TopCat.of (ClosedInterval × X) ⟶ Y) (r₀ r₁ : ι → κ)
    (hf₀ : ∀ i, Set.MapsTo f₀ (U i) (V (r₀ i))) (hf₁ : ∀ i, Set.MapsTo f₁ (U i) (V (r₁ i)))
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
    (u₀ u₁ : ∀ q, (small Y V).X (d + q + 1) ⟶ E.X q)
    (hu₀ : ∀ q, u₀ (q + 1) ≫ E.d (q + 1) q = (small Y V).d (d + q + 2) (d + q + 1) ≫ u₀ q)
    (hu₁ : ∀ q, u₁ (q + 1) ≫ E.d (q + 1) q = (small Y V).d (d + q + 2) (d + q + 1) ≫ u₁ q)
    (he : ∀ q, (SmallRetractionComparison.map (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V f₀ r₀ hf₀).f (d + q + 1) ≫ u₀ q =
      (SmallRetractionComparison.map (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V f₁ r₁ hf₁).f (d + q + 1) ≫ u₁ q) (q : ℕ) :
    ((small X (CommonPrismRefinement.endpointCover X U)).iCycles (d + q) ≫
      (inclusion X (CommonPrismRefinement.endpointCover X U)).f (d + q) ≫ AnnularTimeTrim.prism X (d + q)) ≫
      (((push f₀ ≫ smallSingularRetraction (X := Y) coeff V hV hcoverV).f (d + q + 1) ≫ u₀ q) -
        ((push f₁ ≫ smallSingularRetraction (X := Y) coeff V hV hcoverV).f (d + q + 1) ≫ u₁ q)) =
      ((small X (CommonPrismRefinement.endpointCover X U)).iCycles (d + q) ≫
        (inclusion X (CommonPrismRefinement.endpointCover X U)).f (d + q) ≫ AnnularTimeTrim.prism X (d + q) ≫
        ((SmallRetractionComparison.comparison (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hU hcoverU hV hcoverV f₀ r₀ hf₀).hom (d + q + 1) (d + q + 2) ≫
          u₀ (q + 1) -
        (SmallRetractionComparison.comparison (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hU hcoverU hV hcoverV f₁ r₁ hf₁).hom (d + q + 1) (d + q + 2) ≫
          u₁ (q + 1))) ≫ E.d (q + 1) q := by
  have h₀ := CommonPrismRefinement.filtered_prism_comparison X U V hU hcoverU hV hcoverV f₀ r₀ hf₀ E d u₀ hu₀ q
  have h₁ := CommonPrismRefinement.filtered_prism_comparison X U V hU hcoverU hV hcoverV f₁ r₁ hf₁ E d u₁ hu₁ q
  simp only [HomologicalComplex.comp_f, Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc] at h₀ h₁ ⊢
  rw [he q] at h₀
  have hh := congrArg₂ (fun a b => a - b) h₀ h₁
  convert hh using 1 <;> abel

end
end Finsler.PairedPrismComparison
