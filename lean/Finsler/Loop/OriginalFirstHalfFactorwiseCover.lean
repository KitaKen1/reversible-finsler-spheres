module

public import Finsler.Loop.CompactRectangleCoverRefinement
public import Finsler.Loop.OriginalFirstHalfJointCover
public import Finsler.Loop.OriginalFirstHalfNormalizationExternalShuffle
public import Finsler.Topology.FactorwiseSubdivisionComparison

/-! Actual factorwise cylinder/second-input covers subordinate to the
original joint cover through its literal coordinate reorder. The cover
and scale contain no tested degree, cochain or length thresholds. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfFactorwiseCover

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfCupOneCochains

set_option autoImplicit false

def first {P : Type} [PseudoMetricSpace P] (σ : ℝ) :
    (ClosedInterval × P) → Set (ClosedInterval × P) := PairDistanceCover.cover id σ

def other {Q : Type} [PseudoMetricSpace Q] (σ : ℝ) : Q → Set Q := PairDistanceCover.cover id σ

theorem first_open {P : Type} [PseudoMetricSpace P] (σ : ℝ) (i : ClosedInterval × P) :
    IsOpen (first σ i) := PairDistanceCover.cover_open id continuous_id σ i

theorem first_univ {P : Type} [PseudoMetricSpace P] {σ : ℝ} (hσ : 0 < σ) :
    ⋃ i, first (P := P) σ i = Set.univ := PairDistanceCover.cover_univ id hσ

theorem other_open {Q : Type} [PseudoMetricSpace Q] (σ : ℝ) (i : Q) :
    IsOpen (other σ i) := PairDistanceCover.cover_open id continuous_id σ i

theorem other_univ {Q : Type} [PseudoMetricSpace Q] {σ : ℝ} (hσ : 0 < σ) :
    ⋃ i, other (Q := Q) σ i = Set.univ := PairDistanceCover.cover_univ id hσ

theorem exists_refinement {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r η κ ρ : ℝ)
    (hη : 0 < η) (hκR : κ < R) (hρr : ρ < r) {b : ℝ} (hb : 0 < b) :
    ∃ σ > 0, σ ≤ b ∧ ∃ index : (ClosedInterval × P) × Q →
      Option (Option (FirstInputRotationCochains.space α β R r)),
      ∀ c, Set.MapsTo (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)
        (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × P)) (Y := TopCat.of Q)
          (first σ) (other σ) c) (OriginalFirstHalfJointCover.cover α β R r η κ ρ (index c)) := by
  exact CompactRectangleCoverRefinement.exists_refinement
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_open α β R r η κ ρ)
    (OriginalFirstHalfJointCover.cover_univ α β R r η hη hκR hρr)
    (OriginalFirstHalfNormalizationExternalShuffle.reorder α β).hom hb

end Finsler.OriginalFirstHalfFactorwiseCover
