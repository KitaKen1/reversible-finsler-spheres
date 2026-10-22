module

public import Finsler.Topology.FirstHalfAnnularTimeInputs
public import Finsler.Topology.SmallCoverRefinement

/-! A smaller genuine rectangle scale refines the actual final-face
cover and maps to the original outer rectangle cover. This permits a
common source refinement while leaving the original outer caps fixed. -/

@[expose] public section
namespace Finsler.FirstHalfFaceRefinement

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (X : Type) [PseudoMetricSpace X] [CompactSpace X] {η θ : ℝ} (h : η ≤ θ)

include h

theorem cover_mono (center : Outer X) :
    FirstHalfInteriorCapDomain.faceCover X η center ⊆ FirstHalfInteriorCapDomain.faceCover X θ center :=
  fun _ hz => JoinedRectangleRefinement.rectangleCover_mono h center hz

def map : small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η) ⟶
    small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X θ) :=
  SmallCoverRefinement.map (TopCat.of (ClosedInterval × X))
    (FirstHalfInteriorCapDomain.faceCover X η) (FirstHalfInteriorCapDomain.faceCover X θ)
    (fun center => ⟨center, cover_mono X h center⟩)

theorem map_inclusion : map X h ≫
    inclusion (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X θ) =
      inclusion (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η) :=
  SmallCoverRefinement.map_inclusion (TopCat.of (ClosedInterval × X))
    (FirstHalfInteriorCapDomain.faceCover X η) (FirstHalfInteriorCapDomain.faceCover X θ) _

def toOuter : small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η) ⟶
    small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X θ) :=
  SmallRetractionComparison.map (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
    (FirstHalfInteriorCapDomain.faceCover X η) (JoinedFilteredCap.rectangleCover X θ)
    (planeFace (TopCat.of X) 1) id (fun center z hz =>
      JoinedRectangleRefinement.rectangleCover_mono h center hz)

theorem toOuter_inclusion : toOuter X h ≫ inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X θ) =
    inclusion (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η) ≫ push (planeFace (TopCat.of X) 1) :=
  SmallRetractionComparison.map_inclusion (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
    (FirstHalfInteriorCapDomain.faceCover X η) (JoinedFilteredCap.rectangleCover X θ)
    (planeFace (TopCat.of X) 1) id _

end
end Finsler.FirstHalfFaceRefinement
