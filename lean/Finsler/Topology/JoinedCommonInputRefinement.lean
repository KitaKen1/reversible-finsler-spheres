module

public import Finsler.Topology.FinitePullbackCover
public import Finsler.Topology.JoinedEndpointFilteredAgreement
public import Finsler.Topology.PairedPrismComparison

/-! One actual cylinder cover simultaneously controls the middle,
both half-time faces, and both square faces. Pulling it back along the
two time endpoints gives one common base input cover for both prisms.
All covers are chosen before any tested cochain or degree. -/

@[expose] public section
namespace Finsler.JoinedCommonInputRefinement

open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.JoinedComparisonAdequacy
open Finsler.JoinedEndpointMaps Finsler.JoinedRefinedComparisons Finsler.JoinedComparisonSource

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

def maps (X : TopCat.{0}) : Fin 5 → (TopCat.of (ClosedInterval × X) ⟶ TopCat.of (Outer X)) :=
  ![cylinderFlip X ≫ triangleLift X, firstHalf X, secondHalf X, planeFace X 0, planeFace X 1]

def cover (X : Type) [PseudoMetricSpace X] (η : ℝ) :=
  FinitePullbackCover.cover (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
    (JoinedFilteredCap.rectangleCover X η) (maps (TopCat.of X))

def inputCover (X : Type) [PseudoMetricSpace X] (η : ℝ) :=
  CommonPrismRefinement.endpointCover (TopCat.of X) (cover X η)

private theorem rectangles_open (X : Type) [PseudoMetricSpace X] (η : ℝ) (center : Outer X) :
    IsOpen (JoinedFilteredCap.rectangleCover X η center) :=
  (PairDistanceCover.cover_open id continuous_id η center.1).prod
    (PairDistanceCover.cover_open id continuous_id η center.2)

private theorem rectangles_univ (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    ⋃ center, JoinedFilteredCap.rectangleCover X η center = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  refine Set.mem_iUnion.mpr ⟨z, ?_, ?_⟩
  · change dist z.1 z.1 < η
    simpa only [dist_self] using hη
  · change dist z.2 z.2 < η
    simpa only [dist_self] using hη

theorem cover_open (X : Type) [PseudoMetricSpace X] (η : ℝ) (c : Fin 5 → Outer X) :
    IsOpen (cover X η c) :=
  FinitePullbackCover.isOpen (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
    (JoinedFilteredCap.rectangleCover X η) (maps (TopCat.of X)) (rectangles_open X η) c

theorem cover_univ (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    ⋃ c, cover X η c = Set.univ :=
  FinitePullbackCover.covers (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
    (JoinedFilteredCap.rectangleCover X η) (maps (TopCat.of X)) (rectangles_univ X η hη)

theorem inputCover_open (X : Type) [PseudoMetricSpace X] (η : ℝ)
    (c : (Fin 5 → Outer X) × (Fin 5 → Outer X)) : IsOpen (inputCover X η c) :=
  CommonPrismRefinement.endpointCover_open (TopCat.of X) (cover X η) (cover_open X η) c

theorem inputCover_univ (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    ⋃ c, inputCover X η c = Set.univ :=
  CommonPrismRefinement.endpointCover_univ (TopCat.of X) (cover X η) (cover_univ X η hη)

theorem half_outputs_eq {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
    (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (η : ℝ) (B : Set (SphereLoop n)) (N q : ℕ)
    (c : (chains (Finsler.SelfCutThomCocycle.parameters n)).X N ⟶ (chains (TopCat.of (SphereLoop n))).X q)
    (d : Fin 3 → ((small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X N ⟶ (chains (TopCat.of B)).X q))
    (hd : ∀ i, d i ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) B)).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f N ≫
        (push (JoinedFamilyNaturality.globalMap u a ha ha1 i)).f N ≫ c) (i : Fin 2) :
    (FinitePullbackCover.map (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
      (JoinedFilteredCap.rectangleCover X η) (maps (TopCat.of X)) ⟨i.val + 1, by omega⟩).f N ≫ d 0 =
    (FinitePullbackCover.map (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
      (JoinedFilteredCap.rectangleCover X η) (maps (TopCat.of X)) 3).f N ≫ d i.succ := by
  have he : maps (TopCat.of X) ⟨i.val + 1, by omega⟩ ≫ JoinedFamilyNaturality.globalMap u a ha ha1 0 =
      maps (TopCat.of X) 3 ≫ JoinedFamilyNaturality.globalMap u a ha ha1 i.succ := by
    fin_cases i
    · exact first_start u a ha ha1
    · exact second_start u a ha ha1
  exact SmallFilteredMapAgreement.outputs_eq
    (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X)) (Z := TopCat.of (Outer X))
    (P := Finsler.SelfCutThomCocycle.parameters n) (L := TopCat.of (SphereLoop n))
    (cover X η) (JoinedFilteredCap.rectangleCover X η) (JoinedFilteredCap.rectangleCover X η)
    (maps (TopCat.of X) ⟨i.val + 1, by omega⟩) (maps (TopCat.of X) 3)
    (JoinedFamilyNaturality.globalMap u a ha ha1 0) (JoinedFamilyNaturality.globalMap u a ha ha1 i.succ)
    (fun center => center ⟨i.val + 1, by omega⟩) (fun center => center 3)
    (FinitePullbackCover.maps _ _ _) (FinitePullbackCover.maps _ _ _) he B N q c
    (d 0) (d i.succ) (hd 0) (hd i.succ)

end
end Finsler.JoinedCommonInputRefinement
