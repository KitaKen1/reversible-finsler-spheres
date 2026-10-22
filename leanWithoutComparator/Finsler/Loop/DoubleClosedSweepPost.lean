module

public import Finsler.Loop.DoubleClosedSweepProjection
public import Finsler.Loop.ClosedSweepPost

/-! Project the genuine two-sweep input into any actual target pair
after a specified continuous output map. The source, time order and
relative quotient remain explicit. -/
@[expose] public section
namespace Finsler.DoubleClosedSweepPost
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable {X Y Z W : TopCat.{0}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (H : TopCat.Homotopy f f) (K : TopCat.Homotopy g g) (l : Z ⟶ W)

def post := TopCat.Homotopy.comp (TopCat.Homotopy.refl l) K

theorem square_evaluation :
    DoubleClosedSweepProjection.squareEvaluation H (post K l) =
      DoubleClosedSweepProjection.squareEvaluation H K ≫ l := by
  apply TopCat.ext
  intro z
  rfl

variable (B : Set W)
    (hB : Set.MapsTo (DoubleClosedSweepProjection.squareEvaluation H K ≫ l)
      (DoubleRelativeTimeCylinder.squareBoundary X) B)

include hB in
theorem post_faces :
    Set.MapsTo (DoubleClosedSweepProjection.squareEvaluation H (post K l))
      (DoubleRelativeTimeCylinder.squareBoundary X) B := by
  rw [square_evaluation]
  exact hB

def pairMap : DoubleRelativeTimeCylinder.squarePair X ⟶ TopPair.ofSubset (X := W) B :=
  DoubleClosedSweepProjection.pairMap H (post K l) B (post_faces H K l B hB)

private theorem subsetMap_congr {A D : TopCat.{0}} (U : Set A) (V : Set D) (a b : A ⟶ D)
    (ha : Set.MapsTo a U V) (hb : Set.MapsTo b U V) (he : a = b) :
    TopPair.ofSubsetMap (B := U) (B' := V) a ha = TopPair.ofSubsetMap (B := U) (B' := V) b hb := by
  subst b
  rfl

theorem pairMap_eq :
    pairMap H K l B hB =
      TopPair.ofSubsetMap (B := DoubleRelativeTimeCylinder.squareBoundary X) (B' := B)
        (DoubleClosedSweepProjection.squareEvaluation H K ≫ l) hB :=
  subsetMap_congr _ _ _ _ _ _ (square_evaluation H K l)

theorem homology_projection (q : ℕ) :
    DoubleRelativeTimeCylinder.homology X q ≫
      TopPair.singularHomologyMap (pairMap H K l B hB) coeff (q + 2) =
    SelfHomotopySweep.homology (H.toSSet.chainComplexMap coeff) q ≫
      SelfHomotopySweep.homology (K.toSSet.chainComplexMap coeff) (q + 1) ≫
      homologyPushZMod2 l (q + 2) ≫
      HomologicalComplex.homologyMap ((TopPair.ofSubset (X := W) B).singularChainComplexπ coeff) (q + 2) := by
  have he := DoubleClosedSweepProjection.homology H (post K l) B (post_faces H K l B hB) q
  change DoubleRelativeTimeCylinder.homology X q ≫
    TopPair.singularHomologyMap (pairMap H K l B hB) coeff (q + 2) = _ at he
  rw [post, ClosedSweepPost.homology] at he
  simpa only [Category.assoc] using he

end
end Finsler.DoubleClosedSweepPost
