module

public import Finsler.Loop.BoundedCarrierJoinCap
public import Finsler.Topology.FactorwiseSubdivisionComparison

/-! The actual proper-centered pullback rectangles form a genuine open
full cover of the bounded-kept/beta pair space, including empty spaces.
Its real retraction extends the constructed closed cap to all inputs
and is literally inverse on the original small chains. -/

@[expose] public section
namespace Finsler.BoundedCarrierJoinCover

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (B κ : ℝ)

theorem isOpen (i : CompactRotatedCutData.source α r × Q) : IsOpen (BoundedCarrierJoinCap.rectangles α β r hr F B κ i) :=
  FactorwiseSubdivisionComparison.rectangles_open
    (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
    (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)
    (FirstInputSelfCutBoundedSpace.carrier_open α r hr F B κ)
    (PairDistanceCover.cover_open _ (H1AlignmentHomotopy.basepoint_continuous.comp β.continuous) _) i

theorem covers (hκ : 0 < κ) : ⋃ i, BoundedCarrierJoinCap.rectangles α β r hr F B κ i = Set.univ :=
  FactorwiseSubdivisionComparison.rectangles_cover
    (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
    (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)
    (FirstInputSelfCutBoundedSpace.carrier_univ α r hr F B hκ)
    (PairDistanceCover.cover_univ _ (div_pos hκ (by norm_num)))

def retraction (hκ : 0 < κ) := smallSingularRetraction
  (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) coeff
  (BoundedCarrierJoinCap.rectangles α β r hr F B κ) (isOpen α β r hr F B κ) (covers α β r hr F B κ hκ)

variable (R : ℝ) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

def unrefined := (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).pre
  (retraction α β r hr F B κ hκ)

theorem on_small (k : ℕ) :
    (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (BoundedCarrierJoinCap.rectangles α β r hr F B κ)).f ((m + 1) + k) ≫
      (unrefined α β r hr F B κ R hκ hκR).component k =
    (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).component k := by
  have he : inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (BoundedCarrierJoinCap.rectangles α β r hr F B κ) ≫ retraction α β r hr F B κ hκ = 𝟙 _ :=
    ι_comp_smallSingularRetraction coeff (BoundedCarrierJoinCap.rectangles α β r hr F B κ)
      (isOpen α β r hr F B κ) (covers α β r hr F B κ hκ)
  change _ ≫ ((retraction α β r hr F B κ hκ).f ((m + 1) + k) ≫ _) = _
  rw [← Category.assoc, ← HomologicalComplex.comp_f, he, HomologicalComplex.id_f, Category.id_comp]

end
end Finsler.BoundedCarrierJoinCover
