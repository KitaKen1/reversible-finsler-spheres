module

public import Finsler.Loop.SingleCapEmbeddingPullback
public import Finsler.Loop.BoundedKeptProductInputs
public import Finsler.Loop.SmallNormalizedCapShuffle

/-! The actual bounded kept carrier uses pullbacks of the original
proper-cut-centered balls. Their rectangle cap lifts into the real
bounded near tube, without choosing centers in a possibly empty
bounded space. Its image is the original proper localized join cap. -/

@[expose] public section
namespace Finsler.BoundedCarrierJoinCap

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.FarNormalizedDiagonalCap
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (B : ℝ) (κ : ℝ)

def rectangles := SmallRectangleShuffle.rectangles
  (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
  (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)

theorem cover_maps (i : CompactRotatedCutData.source α r × Q) :
    Set.MapsTo (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) (rectangles α β r hr F B κ i)
      (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ i) := fun _ hz => hz

def properRectangle := SmallRetractionComparison.map (rectangles α β r hr F B κ)
  (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)
  (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) id (cover_maps α β r hr F B κ)

theorem rectangle_source : properRectangle α β r hr F B κ ≫
    inclusion (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ) =
    inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) (rectangles α β r hr F B κ) ≫
      push (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) :=
  SmallRetractionComparison.map_inclusion _ _ _ _ _

theorem proper_injective : Function.Injective (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) := by
  intro z w he
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun v => v.1.val) he
  · exact congrArg (fun v : CompactRotatedCutData.source α r × Q => v.2) he

theorem proper_mono (k : ℕ) : Mono ((push (BoundedKeptProductInputs.properPair α r hr F B (Q := Q))).f k) := by
  have : Mono (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) :=
    (TopCat.mono_iff_injective _).mpr (proper_injective α r hr F B (Q := Q))
  exact inferInstanceAs (Mono ((sigmaConst.obj coeff).map
    ((TopCat.toSSet.map (BoundedKeptProductInputs.properPair α r hr F B (Q := Q))).app (Opposite.op ⦋k⦌))))

variable (R : ℝ) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

def operation := SingleCapEmbeddingPullback.operation (rectangles α β r hr F B κ)
  (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)
  (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) id (cover_maps α β r hr F B κ)
  (CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β R) (m + 1)
  (CompactJoinCocycle.cocycle (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ)
  (proper_mono α r hr F B (Q := Q))
  (fun k σ hn => CompactJoinCapLocalization.parent_near (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ hκR k σ hn)
  (CompactJoinCocycle.cocycle_closed (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ)

theorem source (k : ℕ) : (operation α β r hr F B κ R hκ hκR).component k ≫
    (push (SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R))).f k =
    (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) (rectangles α β r hr F B κ)).f ((m + 1) + k) ≫
      absoluteChain (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) (m + 1) k ((m + 1) + k) rfl
        (CompactJoinCocycle.cocycle (BoundedKeptProductInputs.kept α r hr F B) β (dim_pos m) hκ) := by
  have he := SingleCapEmbeddingPullback.source (rectangles α β r hr F B κ)
    (CompactJoinCapLocalization.cover (OriginalFirstHalfCutOutputJoinData.kept α r hr) β κ)
    (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) id (cover_maps α β r hr F B κ)
    (CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β R) (m + 1)
    (CompactJoinCocycle.cocycle (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ)
    (proper_mono α r hr F B (Q := Q))
    (fun k σ hn => CompactJoinCapLocalization.parent_near (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ hκR k σ hn)
    (CompactJoinCocycle.cocycle_closed (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ) k
  rw [BoundedKeptProductInputs.cocycle] at he
  exact he

end
end Finsler.BoundedCarrierJoinCap
