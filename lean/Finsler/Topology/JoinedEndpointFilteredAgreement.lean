module

public import Finsler.Topology.PullbackPairCover
public import Finsler.Topology.SmallFilteredMapAgreement
public import Finsler.Topology.JoinedEndpointMaps

/-! The actual triangle half-time and trimming-square start maps have
common open full pullback covers, selected before all cochains. On those
genuine refinements their original filtered output lifts agree literally
on all chains, including chains with nonzero boundary. -/

@[expose] public section
namespace Finsler.JoinedEndpointFilteredAgreement

open CategoryTheory AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.JoinedComparisonAdequacy
open Finsler.JoinedEndpointMaps Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

def commonFirst (X : Type) [PseudoMetricSpace X] (η : ℝ) :=
  PullbackPairCover.cover (JoinedFilteredCap.rectangleCover X η) (JoinedFilteredCap.rectangleCover X η)
    (firstHalf (TopCat.of X)) (planeFace (TopCat.of X) 0)

def commonSecond (X : Type) [PseudoMetricSpace X] (η : ℝ) :=
  PullbackPairCover.cover (JoinedFilteredCap.rectangleCover X η) (JoinedFilteredCap.rectangleCover X η)
    (secondHalf (TopCat.of X)) (planeFace (TopCat.of X) 0)

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

theorem commonFirst_open (X : Type) [PseudoMetricSpace X] (η : ℝ) (ij : Outer X × Outer X) :
    IsOpen (commonFirst X η ij) :=
  PullbackPairCover.isOpen _ _ _ _ (rectangles_open X η) (rectangles_open X η) ij

theorem commonSecond_open (X : Type) [PseudoMetricSpace X] (η : ℝ) (ij : Outer X × Outer X) :
    IsOpen (commonSecond X η ij) :=
  PullbackPairCover.isOpen _ _ _ _ (rectangles_open X η) (rectangles_open X η) ij

theorem commonFirst_univ (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    ⋃ ij, commonFirst X η ij = Set.univ :=
  PullbackPairCover.covers _ _ _ _ (rectangles_univ X η hη) (rectangles_univ X η hη)

theorem commonSecond_univ (X : Type) [PseudoMetricSpace X] (η : ℝ) (hη : 0 < η) :
    ⋃ ij, commonSecond X η ij = Set.univ :=
  PullbackPairCover.covers _ _ _ _ (rectangles_univ X η hη) (rectangles_univ X η hη)

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
  (η : ℝ) (B : Set (SphereLoop n)) (N q : ℕ)
  (c : (chains (Finsler.SelfCutThomCocycle.parameters n)).X N ⟶ (chains (TopCat.of (SphereLoop n))).X q)
  (d₀ : (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X N ⟶ (chains (TopCat.of B)).X q)
  (h₀ : d₀ ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) B)).f q =
    (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f N ≫
      (push (JoinedFamilyNaturality.globalMap u a ha ha1 0)).f N ≫ c)

include h₀

theorem first_outputs_eq
    (d₁ : (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X N ⟶ (chains (TopCat.of B)).X q)
    (h₁ : d₁ ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) B)).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f N ≫
        (push (JoinedFamilyNaturality.globalMap u a ha ha1 1)).f N ≫ c) :
    (PullbackPairCover.leftMap (JoinedFilteredCap.rectangleCover X η) (JoinedFilteredCap.rectangleCover X η)
      (firstHalf (TopCat.of X)) (planeFace (TopCat.of X) 0)).f N ≫ d₀ =
    (PullbackPairCover.rightMap (JoinedFilteredCap.rectangleCover X η) (JoinedFilteredCap.rectangleCover X η)
      (firstHalf (TopCat.of X)) (planeFace (TopCat.of X) 0)).f N ≫ d₁ :=
  SmallFilteredMapAgreement.outputs_eq
    (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X)) (Z := TopCat.of (Outer X))
    (P := Finsler.SelfCutThomCocycle.parameters n) (L := TopCat.of (SphereLoop n)) (commonFirst X η)
    (JoinedFilteredCap.rectangleCover X η) (JoinedFilteredCap.rectangleCover X η)
    (firstHalf (TopCat.of X)) (planeFace (TopCat.of X) 0)
    (JoinedFamilyNaturality.globalMap u a ha ha1 0) (JoinedFamilyNaturality.globalMap u a ha ha1 1)
    Prod.fst Prod.snd (PullbackPairCover.maps_left _ _ _ _) (PullbackPairCover.maps_right _ _ _ _)
    (first_start u a ha ha1) B N q c d₀ d₁ h₀ h₁

theorem second_outputs_eq
    (d₂ : (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).X N ⟶ (chains (TopCat.of B)).X q)
    (h₂ : d₂ ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) B)).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η)).f N ≫
        (push (JoinedFamilyNaturality.globalMap u a ha ha1 2)).f N ≫ c) :
    (PullbackPairCover.leftMap (JoinedFilteredCap.rectangleCover X η) (JoinedFilteredCap.rectangleCover X η)
      (secondHalf (TopCat.of X)) (planeFace (TopCat.of X) 0)).f N ≫ d₀ =
    (PullbackPairCover.rightMap (JoinedFilteredCap.rectangleCover X η) (JoinedFilteredCap.rectangleCover X η)
      (secondHalf (TopCat.of X)) (planeFace (TopCat.of X) 0)).f N ≫ d₂ :=
  SmallFilteredMapAgreement.outputs_eq
    (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X)) (Z := TopCat.of (Outer X))
    (P := Finsler.SelfCutThomCocycle.parameters n) (L := TopCat.of (SphereLoop n)) (commonSecond X η)
    (JoinedFilteredCap.rectangleCover X η) (JoinedFilteredCap.rectangleCover X η)
    (secondHalf (TopCat.of X)) (planeFace (TopCat.of X) 0)
    (JoinedFamilyNaturality.globalMap u a ha ha1 0) (JoinedFamilyNaturality.globalMap u a ha ha1 2)
    Prod.fst Prod.snd (PullbackPairCover.maps_left _ _ _ _) (PullbackPairCover.maps_right _ _ _ _)
    (second_start u a ha ha1) B N q c d₀ d₂ h₀ h₂

end
end Finsler.JoinedEndpointFilteredAgreement
