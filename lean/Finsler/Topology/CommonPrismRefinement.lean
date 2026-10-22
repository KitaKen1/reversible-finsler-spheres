module

public import Finsler.Topology.PullbackPairCover
public import Finsler.Topology.RelativeSmallRetraction
public import Finsler.Topology.AnnularTimeTrim

/-! Pull back the source cover along both actual time endpoints. This
gives an open full cover of the original loop-parameter space. Its time
prism has endpoints already small in the cylinder cover, so retraction
naturality compares the full prism after a closed filtered cap without
assuming that the time-prism chain is a cycle. -/

@[expose] public section
namespace Finsler.CommonPrismRefinement

open CategoryTheory AlgebraicTopology
open Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality TauCeti

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

variable (X : TopCat.{0}) {ι : Type*} (U : ι → Set (ClosedInterval × X))

def endpointCover : ι × ι → Set X :=
  PullbackPairCover.cover (X := X) (Y := TopCat.of (ClosedInterval × X)) (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)

theorem endpointCover_open (hU : ∀ i, IsOpen (U i)) (ij : ι × ι) : IsOpen (endpointCover X U ij) :=
  PullbackPairCover.isOpen (X := X) (Y := TopCat.of (ClosedInterval × X)) (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1) hU hU ij

theorem endpointCover_univ (hU : ⋃ i, U i = Set.univ) : ⋃ ij, endpointCover X U ij = Set.univ :=
  PullbackPairCover.covers (X := X) (Y := TopCat.of (ClosedInterval × X)) (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1) hU hU

def prism : Homotopy
    (inclusion X (endpointCover X U) ≫ push (AnnularTimeTrim.slice X 0))
    (inclusion X (endpointCover X U) ≫ push (AnnularTimeTrim.slice X 1)) :=
  ((AnnularTimeTrim.cylinder X).toSSet.chainComplexMap coeff).compLeft (inclusion X (endpointCover X U))

theorem prism_hom (j : ℕ) : (prism X U).hom j (j + 1) =
    (inclusion X (endpointCover X U)).f j ≫ AnnularTimeTrim.prism X j := rfl

theorem filtered_prism_comparison {Y : TopCat.{0}} {κ : Type*} (V : κ → Set Y)
    (hU : ∀ i, IsOpen (U i)) (hcoverU : ⋃ i, U i = Set.univ)
    (hV : ∀ j, IsOpen (V j)) (hcoverV : ⋃ j, V j = Set.univ)
    (f : TopCat.of (ClosedInterval × X) ⟶ Y) (r : ι → κ)
    (hf : ∀ i, Set.MapsTo f (U i) (V (r i)))
    (E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ) (d : ℕ)
    (u : ∀ q, (small Y V).X (d + q + 1) ⟶ E.X q)
    (hu : ∀ q, u (q + 1) ≫ E.d (q + 1) q =
      (small Y V).d (d + q + 2) (d + q + 1) ≫ u q) (q : ℕ) :
    ((small X (endpointCover X U)).iCycles (d + q) ≫
      (inclusion X (endpointCover X U)).f (d + q) ≫ AnnularTimeTrim.prism X (d + q)) ≫
      (((push f ≫ smallSingularRetraction (X := Y) coeff V hV hcoverV).f (d + q + 1) -
        (smallSingularRetraction (X := TopCat.of (ClosedInterval × X)) coeff U hU hcoverU ≫ SmallRetractionComparison.map (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V f r hf).f (d + q + 1)) ≫ u q) =
      ((small X (endpointCover X U)).iCycles (d + q) ≫
        (inclusion X (endpointCover X U)).f (d + q) ≫ AnnularTimeTrim.prism X (d + q) ≫
        (SmallRetractionComparison.comparison (X := TopCat.of (ClosedInterval × X)) (Y := Y) U V hU hcoverU hV hcoverV f r hf).hom (d + q + 1) (d + q + 2) ≫
        u (q + 1)) ≫ E.d (q + 1) q := by
  let e₀ : small X (endpointCover X U) ⟶ small (TopCat.of (ClosedInterval × X)) U := PullbackPairCover.leftMap (X := X) (Y := TopCat.of (ClosedInterval × X)) (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  let e₁ : small X (endpointCover X U) ⟶ small (TopCat.of (ClosedInterval × X)) U := PullbackPairCover.rightMap (X := X) (Y := TopCat.of (ClosedInterval × X)) (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)
  have h₀ : inclusion X (endpointCover X U) ≫ push (AnnularTimeTrim.slice X 0) =
      e₀ ≫ inclusion (TopCat.of (ClosedInterval × X)) U :=
    (PullbackPairCover.leftMap_inclusion (X := X) (Y := TopCat.of (ClosedInterval × X)) (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)).symm
  have h₁ : inclusion X (endpointCover X U) ≫ push (AnnularTimeTrim.slice X 1) =
      e₁ ≫ inclusion (TopCat.of (ClosedInterval × X)) U :=
    (PullbackPairCover.rightMap_inclusion (X := X) (Y := TopCat.of (ClosedInterval × X)) (Z := TopCat.of (ClosedInterval × X)) U U (AnnularTimeTrim.slice X 0) (AnnularTimeTrim.slice X 1)).symm
  simpa only [prism_hom, Category.assoc] using
    RelativeSmallRetraction.prism_boundary (X := TopCat.of (ClosedInterval × X)) (Y := Y)
      (A := small X (endpointCover X U)) (E := E) U V hU hcoverU hV hcoverV f r hf
      (prism X U) e₀ e₁ h₀ h₁ d u hu q

end
end Finsler.CommonPrismRefinement
