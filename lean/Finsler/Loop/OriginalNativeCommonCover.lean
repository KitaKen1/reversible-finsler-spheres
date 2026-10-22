module

public import Finsler.Loop.JoinTimeCommonRefinement
public import Finsler.Topology.OriginalSecondHalfUniformOperation
public import Finsler.Topology.SmallRefinementComparison
public import Finsler.Topology.CommonPrismRefinement

/-! A genuine common open/full source refinement for the original
factorwise triple cap and the native two-cap face. The first join cap
lands directly in the latter small-chain complex. Both actual time
endpoints share a further open/full input cover. -/

@[expose] public section
namespace Finsler.OriginalNativeCommonCover

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.RelativeCapAssociativity

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1300000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R η σ κ : ℝ)

def oldCover : (P × (ClosedInterval × Q)) → Set (P × (ClosedInterval × Q)) :=
  SmallRectangleShuffle.rectangles (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
    (OriginalSecondHalfUniformOperation.leftCover α σ κ)
    (OriginalSecondHalfUniformOperation.rightCover β σ κ)

def cover : (Option (JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) ×
    (P × (ClosedInterval × Q))) → Set (P × (ClosedInterval × Q)) :=
  fun c => JoinTimeCommonRefinement.cover α β R η κ c.1 ∩ oldCover α β σ κ c.2

theorem oldCover_open (c : P × (ClosedInterval × Q)) : IsOpen (oldCover α β σ κ c) :=
  FactorwiseSubdivisionComparison.rectangles_open (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
    (OriginalSecondHalfUniformOperation.leftCover α σ κ)
    (OriginalSecondHalfUniformOperation.rightCover β σ κ)
    (OriginalSecondHalfUniformOperation.left_open α σ κ)
    (OriginalSecondHalfUniformOperation.right_open β σ κ) c

theorem oldCover_univ (hσ : 0 < σ) (hκ : 0 < κ) : ⋃ c, oldCover α β σ κ c = Set.univ :=
  FactorwiseSubdivisionComparison.rectangles_cover (X := TopCat.of P) (Y := TopCat.of (ClosedInterval × Q))
    (OriginalSecondHalfUniformOperation.leftCover α σ κ)
    (OriginalSecondHalfUniformOperation.rightCover β σ κ)
    (OriginalSecondHalfUniformOperation.left_covers α hσ hκ)
    (OriginalSecondHalfUniformOperation.right_covers β hσ hκ)

theorem cover_open (c : Option (JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) ×
    (P × (ClosedInterval × Q))) : IsOpen (cover α β R η σ κ c) :=
  (JoinTimeCommonRefinement.cover_open α β R η κ c.1).inter (oldCover_open α β σ κ c.2)

theorem cover_univ (hη : 0 < η) (hσ : 0 < σ) (hκ : 0 < κ) (hκR : κ < R) :
    ⋃ c, cover α β R η σ κ c = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
    ((JoinTimeCommonRefinement.cover_univ α β R η hη hκR).symm ▸ Set.mem_univ z)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ((oldCover_univ α β σ κ hσ hκ).symm ▸ Set.mem_univ z)
  exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

def toNativeCover : small (TopCat.of (P × (ClosedInterval × Q))) (cover α β R η σ κ) ⟶
    small (TopCat.of (P × (ClosedInterval × Q))) (JoinTimeCommonRefinement.cover α β R η κ) :=
  SmallRefinementComparison.refinement (X := TopCat.of (P × (ClosedInterval × Q)))
    (cover α β R η σ κ) (JoinTimeCommonRefinement.cover α β R η κ) Prod.fst (fun _ _ hz => hz.1)

theorem toNativeCover_inclusion : toNativeCover α β R η σ κ ≫
    inclusion (TopCat.of (P × (ClosedInterval × Q))) (JoinTimeCommonRefinement.cover α β R η κ) =
      inclusion (TopCat.of (P × (ClosedInterval × Q))) (cover α β R η σ κ) :=
  SmallRefinementComparison.refinement_inclusion (X := TopCat.of (P × (ClosedInterval × Q)))
    (cover α β R η σ κ) (JoinTimeCommonRefinement.cover α β R η κ) Prod.fst (fun _ _ hz => hz.1)

def toOriginal : small (TopCat.of (P × (ClosedInterval × Q))) (cover α β R η σ κ) ⟶
    small (TopCat.of (P × (ClosedInterval × Q))) (oldCover α β σ κ) :=
  SmallRefinementComparison.refinement (X := TopCat.of (P × (ClosedInterval × Q)))
    (cover α β R η σ κ) (oldCover α β σ κ) Prod.snd (fun _ _ hz => hz.2)

theorem toOriginal_inclusion : toOriginal α β R η σ κ ≫
    inclusion (TopCat.of (P × (ClosedInterval × Q))) (oldCover α β σ κ) =
      inclusion (TopCat.of (P × (ClosedInterval × Q))) (cover α β R η σ κ) :=
  SmallRefinementComparison.refinement_inclusion (X := TopCat.of (P × (ClosedInterval × Q)))
    (cover α β R η σ κ) (oldCover α β σ κ) Prod.snd (fun _ _ hz => hz.2)

def cap (hn : 1 ≤ n) (hκ : 0 < κ) :
    DegreeLoweringHomology.Map
      (small (TopCat.of (P × (ClosedInterval × Q))) (cover α β R η σ κ))
      (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)) n :=
  (JoinTimeCommonRefinement.cap α β R η hn hκ).pre (toNativeCover α β R η σ κ)

theorem cap_source (hn : 1 ≤ n) (hκ : 0 < κ) (q : ℕ) :
    (cap α β R η σ κ hn hκ).component q ≫
      (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) ≫
          push (JoinTimeCommonRefinement.source α β R)).f q =
      (inclusion (TopCat.of (P × (ClosedInterval × Q))) (cover α β R η σ κ)).f (n + q) ≫
        absoluteChain (TopCat.of (P × (ClosedInterval × Q))) n q (n + q) rfl
          (CompactJoinCocycle.timeCocycle α β hn hκ) := by
  dsimp only [cap, DegreeLoweringHomology.Map.pre]
  rw [Category.assoc, JoinTimeCommonRefinement.cap_source, ← Category.assoc,
    ← HomologicalComplex.comp_f, toNativeCover_inclusion]

def inputCover := CommonPrismRefinement.endpointCover (TopCat.of (P × Q))
  (fun c => OriginalSecondHalfTimeOperation.reorder (P := P) (Q := Q) ⁻¹' cover α β R η σ κ c)

theorem inputCover_open (c) : IsOpen (inputCover α β R η σ κ c) :=
  CommonPrismRefinement.endpointCover_open (TopCat.of (P × Q)) _
    (fun i => (cover_open α β R η σ κ i).preimage
      (OriginalSecondHalfTimeOperation.reorder (P := P) (Q := Q)).hom.continuous) c

theorem inputCover_univ (hη : 0 < η) (hσ : 0 < σ) (hκ : 0 < κ) (hκR : κ < R) :
    ⋃ c, inputCover α β R η σ κ c = Set.univ := by
  apply CommonPrismRefinement.endpointCover_univ
  rw [← Set.preimage_iUnion, cover_univ α β R η σ κ hη hσ hκ hκR, Set.preimage_univ]

end
end Finsler.OriginalNativeCommonCover
