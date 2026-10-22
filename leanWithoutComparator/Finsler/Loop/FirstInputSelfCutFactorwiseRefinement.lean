module

public import Finsler.Loop.CompactFactorCoverRefinement
public import Finsler.Loop.FirstInputSelfCutCover
public import Finsler.Loop.OriginalFirstHalfFactorwiseCover

/-! One actual metric scale simultaneously refines the real joint
cover, the first-input proper-cut carrier cover and beta's actual
output-join cover. All choices precede tested data. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutFactorwiseRefinement

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem exists_refinement {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η κ ρ : ℝ)
    (hr : r < 1) (hη : 0 < η) (hκ : 0 < κ) (hκR : κ < R) (hρr : ρ < r) {b : ℝ} (hb : 0 < b) :
    ∃ σ > 0, σ ≤ b ∧
      ∃ (index : (ClosedInterval × P) × Q → Option (Option (FirstInputRotationCochains.space α β R r)))
        (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r)) (otherIndex : Q → Q),
      (∀ c, Set.MapsTo (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)
        (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × P)) (Y := TopCat.of Q)
          (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) c)
        (OriginalFirstHalfJointCover.cover α β R r η κ ρ (index c))) ∧
      (∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ FirstInputSelfCutCover.cover α r hr κ ρ (firstIndex c)) ∧
      (∀ c, OriginalFirstHalfFactorwiseCover.other σ c ⊆
        OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ (otherIndex c)) := by
  exact CompactFactorCoverRefinement.exists_simultaneous
    (FirstInputSelfCutCover.cover α r hr κ ρ)
    (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (FirstInputSelfCutCover.cover_open α r hr κ ρ) (FirstInputSelfCutCover.cover_univ α r hr κ hκ hρr)
    (PairDistanceCover.cover_open _ (H1AlignmentHomotopy.basepoint_continuous.comp β.continuous) _)
    (PairDistanceCover.cover_univ _ (div_pos hκ (by norm_num)))
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (OriginalFirstHalfNormalizationExternalShuffle.reorder α β).hom hb

end Finsler.FirstInputSelfCutFactorwiseRefinement
