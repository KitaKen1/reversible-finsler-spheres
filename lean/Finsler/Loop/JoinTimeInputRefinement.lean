module

public import Finsler.Loop.WholeIntervalJoinFirstIdentity
public import Finsler.Loop.TimeCoverRefinementComparison

/-! One genuine open/full input cover is spatially join-small and has
both original time endpoints in the actual fine cylinder cover. All
refinement and endpoint maps are constructed with their inclusion squares. -/

@[expose] public section
namespace Finsler.JoinTimeInputRefinement

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R η σ κ : ℝ)

abbrev FineIndex := Option (JoinedComparisonAdequacy.Outer (CompactNearJoinParameters.tube α β R)) ×
  (P × (ClosedInterval × Q))

def endpointCover : (FineIndex α β R × FineIndex α β R) → Set (P × Q) :=
  PullbackPairCover.cover (X := TopCat.of (P × Q))
    (Y := TopCat.of (P × (ClosedInterval × Q))) (Z := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover α β R η σ κ)
    (OriginalSecondHalfEndpointZero.face 0) (OriginalSecondHalfEndpointZero.face 1)

def cover : ((P × Q) × (FineIndex α β R × FineIndex α β R)) → Set (P × Q) :=
  fun i => CompactJoinCapLocalization.cover α β κ i.1 ∩ endpointCover α β R η σ κ i.2

theorem endpointCover_open (i) : IsOpen (endpointCover α β R η σ κ i) :=
  PullbackPairCover.isOpen (X := TopCat.of (P × Q))
    (Y := TopCat.of (P × (ClosedInterval × Q))) (Z := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover α β R η σ κ)
    (OriginalSecondHalfEndpointZero.face 0) (OriginalSecondHalfEndpointZero.face 1)
    (OriginalNativeCommonCover.cover_open α β R η σ κ) (OriginalNativeCommonCover.cover_open α β R η σ κ) i

theorem endpointCover_univ (hη : 0 < η) (hσ : 0 < σ) (hκ : 0 < κ) (hκR : κ < R) :
    ⋃ i, endpointCover α β R η σ κ i = Set.univ :=
  PullbackPairCover.covers (X := TopCat.of (P × Q))
    (Y := TopCat.of (P × (ClosedInterval × Q))) (Z := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover α β R η σ κ)
    (OriginalSecondHalfEndpointZero.face 0) (OriginalSecondHalfEndpointZero.face 1)
    (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ hκR)
    (OriginalNativeCommonCover.cover_univ α β R η σ κ hη hσ hκ hκR)

theorem cover_open (i) : IsOpen (cover α β R η σ κ i) :=
  (CompactJoinCapLocalization.cover_open α β κ i.1).inter (endpointCover_open α β R η σ κ i.2)

theorem cover_univ (hη : 0 < η) (hσ : 0 < σ) (hκ : 0 < κ) (hκR : κ < R) :
    ⋃ i, cover α β R η σ κ i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ((CompactJoinCapLocalization.cover_univ α β hκ).symm ▸ Set.mem_univ z)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ((endpointCover_univ α β R η σ κ hη hσ hκ hκR).symm ▸ Set.mem_univ z)
  exact Set.mem_iUnion.mpr ⟨(i, j), hi, hj⟩

def spatial : small (TopCat.of (P × Q)) (cover α β R η σ κ) ⟶
    small (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ) :=
  SmallRefinementComparison.refinement (X := TopCat.of (P × Q)) (cover α β R η σ κ)
    (CompactJoinCapLocalization.cover α β κ) Prod.fst (fun _ _ hz => hz.1)

theorem spatial_inclusion : spatial α β R η σ κ ≫
    inclusion (TopCat.of (P × Q)) (CompactJoinCapLocalization.cover α β κ) =
      inclusion (TopCat.of (P × Q)) (cover α β R η σ κ) :=
  SmallRefinementComparison.refinement_inclusion (X := TopCat.of (P × Q)) (cover α β R η σ κ)
    (CompactJoinCapLocalization.cover α β κ) Prod.fst (fun _ _ hz => hz.1)

def endpoints : small (TopCat.of (P × Q)) (cover α β R η σ κ) ⟶
    small (TopCat.of (P × Q)) (endpointCover α β R η σ κ) :=
  SmallRefinementComparison.refinement (X := TopCat.of (P × Q)) (cover α β R η σ κ)
    (endpointCover α β R η σ κ) Prod.snd (fun _ _ hz => hz.2)

theorem endpoints_inclusion : endpoints α β R η σ κ ≫
    inclusion (TopCat.of (P × Q)) (endpointCover α β R η σ κ) =
      inclusion (TopCat.of (P × Q)) (cover α β R η σ κ) :=
  SmallRefinementComparison.refinement_inclusion (X := TopCat.of (P × Q)) (cover α β R η σ κ)
    (endpointCover α β R η σ κ) Prod.snd (fun _ _ hz => hz.2)

def zero : small (TopCat.of (P × Q)) (cover α β R η σ κ) ⟶
    small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ) :=
  endpoints α β R η σ κ ≫ PullbackPairCover.leftMap (X := TopCat.of (P × Q))
    (Y := TopCat.of (P × (ClosedInterval × Q))) (Z := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover α β R η σ κ)
    (OriginalSecondHalfEndpointZero.face 0) (OriginalSecondHalfEndpointZero.face 1)

def one : small (TopCat.of (P × Q)) (cover α β R η σ κ) ⟶
    small (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ) :=
  endpoints α β R η σ κ ≫ PullbackPairCover.rightMap (X := TopCat.of (P × Q))
    (Y := TopCat.of (P × (ClosedInterval × Q))) (Z := TopCat.of (P × (ClosedInterval × Q)))
    (OriginalNativeCommonCover.cover α β R η σ κ) (OriginalNativeCommonCover.cover α β R η σ κ)
    (OriginalSecondHalfEndpointZero.face 0) (OriginalSecondHalfEndpointZero.face 1)

theorem zero_inclusion : zero α β R η σ κ ≫
    inclusion (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ) =
      inclusion (TopCat.of (P × Q)) (cover α β R η σ κ) ≫ push (OriginalSecondHalfEndpointZero.face 0) := by
  rw [zero, Category.assoc, PullbackPairCover.leftMap_inclusion]
  simpa only [endpointCover, Category.assoc] using congrArg (fun f => f ≫ push (OriginalSecondHalfEndpointZero.face 0))
    (endpoints_inclusion α β R η σ κ)

theorem one_inclusion : one α β R η σ κ ≫
    inclusion (TopCat.of (P × (ClosedInterval × Q))) (OriginalNativeCommonCover.cover α β R η σ κ) =
      inclusion (TopCat.of (P × Q)) (cover α β R η σ κ) ≫ push (OriginalSecondHalfEndpointZero.face 1) := by
  rw [one, Category.assoc, PullbackPairCover.rightMap_inclusion]
  simpa only [endpointCover, Category.assoc] using congrArg (fun f => f ≫ push (OriginalSecondHalfEndpointZero.face 1))
    (endpoints_inclusion α β R η σ κ)

end
end Finsler.JoinTimeInputRefinement
