module

public import Finsler.Topology.JoinedRefinedComparisons

/-! Literal original parameter-map identities at the endpoint faces
that connect the actual time triangle to the two trimming squares. -/

@[expose] public section
namespace Finsler.JoinedEndpointMaps

open CategoryTheory MonoidalCategory AlgebraicTopology
open Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.JoinedComparisonAdequacy Finsler.JoinedComparisonSource Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def cylinderFlip (X : TopCat.{0}) : TopCat.of (ClosedInterval × X) ⟶ X ⊗ TopCat.I :=
  TopCat.ofHom ⟨fun z => (z.2, ULift.up z.1),
    continuous_snd.prodMk (continuous_uliftUp.comp continuous_fst)⟩

def firstHalf (X : TopCat.{0}) : TopCat.of (ClosedInterval × X) ⟶ TopCat.of (Outer X) :=
  cylinderFlip X ≫ (X ◁ IntervalTriangle.firstMap) ≫ triangleLift X

def secondHalf (X : TopCat.{0}) : TopCat.of (ClosedInterval × X) ⟶ TopCat.of (Outer X) :=
  cylinderFlip X ≫ (X ◁ IntervalTriangle.secondMap) ≫ triangleLift X

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)

theorem first_start : firstHalf (TopCat.of X) ≫ JoinedFamilyNaturality.globalMap u a ha ha1 0 =
    planeFace (TopCat.of X) 0 ≫ JoinedFamilyNaturality.globalMap u a ha ha1 1 := by
  ext z : 1
  change JoinedHalfCollars.firstFamily u (z.1, z.2) =
    JoinedHalfCollars.firstFamily u (InteriorTimeSlide.slide a ha ha1 (0, z.1), z.2)
  rw [InteriorTimeSlide.slide_zero]

theorem second_start : secondHalf (TopCat.of X) ≫ JoinedFamilyNaturality.globalMap u a ha ha1 0 =
    planeFace (TopCat.of X) 0 ≫ JoinedFamilyNaturality.globalMap u a ha ha1 2 := by
  ext z : 1
  change JoinedHalfCollars.secondFamily u (z.1, z.2) =
    JoinedHalfCollars.secondFamily u (InteriorTimeSlide.slide a ha ha1 (0, z.1), z.2)
  rw [InteriorTimeSlide.slide_zero]

theorem first_end : planeFace (TopCat.of X) 1 ≫ JoinedFamilyNaturality.globalMap u a ha ha1 1 =
    CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha ha1 := by
  ext z : 1
  change JoinedHalfCollars.firstFamily u (InteriorTimeSlide.slide a ha ha1 (1, z.1), z.2) =
    JoinedHalfCollars.firstFamily u (InteriorTimeSlide.trimTime a ha ha1 z.1, z.2)
  rw [InteriorTimeSlide.slide_one]

theorem second_end : planeFace (TopCat.of X) 1 ≫ JoinedFamilyNaturality.globalMap u a ha ha1 2 =
    CylinderTimeTrim.trimmedMap (JoinedHalfCollars.secondFamily u) a ha ha1 := by
  ext z : 1
  change JoinedHalfCollars.secondFamily u (InteriorTimeSlide.slide a ha ha1 (1, z.1), z.2) =
    JoinedHalfCollars.secondFamily u (InteriorTimeSlide.trimTime a ha ha1 z.1, z.2)
  rw [InteriorTimeSlide.slide_one]

end
end Finsler.JoinedEndpointMaps
