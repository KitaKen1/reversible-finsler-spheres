module

public import Finsler.Loop.BoundedFarCarrierCap
public import Finsler.Loop.LiftedRepresentativeComparison
public import Finsler.Loop.BoundedCarrierJoinCover

/-! At the original fixed kappa/R, the actual normalized bounded join
cap and actual specified diagonal cap agree in the same closed bounded
near carrier. The genuine far-supported primitive cap lives there too;
no openness of that carrier is used. -/

@[expose] public section
namespace Finsler.BoundedJoinRepresentative

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (κ : ℝ) (hκ : 0 < κ) (hm : 1 ≤ m) (hκ2 : κ ≤ 2)

def farSet := NearFarCapComparison.far (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q)
  (fun x => basepoint (OriginalFirstHalfCutOutputJoinData.kept α r hr x)) (fun y => basepoint (β y)) κ

theorem far_maps : Set.MapsTo (DiagonalPullbackCut.pairEvaluation
    (StrictLengthProductFamilies.leftEvaluation (OriginalFirstHalfCutOutputJoinData.kept α r hr) (Q := Q))
    (StrictLengthProductFamilies.rightEvaluation β (P := CompactRotatedCutData.source α r)))
    (farSet α β r hr κ) (DiagonalAvoidanceCocycle.far (m + 1) κ) := by
  intro z hz
  change κ ≤ ‖basepoint (β z.2) - basepoint (OriginalFirstHalfCutOutputJoinData.kept α r hr z.1)‖
  have he : κ ≤ dist (basepoint (OriginalFirstHalfCutOutputJoinData.kept α r hr z.1)) (basepoint (β z.2)) := hz
  simpa only [dist_eq_norm, norm_sub_rev] using he

def specified := DiagonalPullbackCut.cocycle (dim_pos m)
  (StrictLengthProductFamilies.leftEvaluation (OriginalFirstHalfCutOutputJoinData.kept α r hr) (Q := Q))
  (StrictLengthProductFamilies.rightEvaluation β (P := CompactRotatedCutData.source α r))

theorem specified_closed : cochainCoboundary (ZMod 2) (OriginalFirstHalfCutProductCochains.space α r (Q := Q)) (m + 1)
    (specified α β r hr) = 0 := DiagonalPullbackCut.cocycle_closed (dim_pos m) _ _

include hκ in
theorem specified_far : cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
    (farSet α β r hr κ)) (m + 1) (specified α β r hr) = 0 :=
  FarNormalizedDiagonalCap.specified_supported m _ _ hκ (farSet α β r hr κ) (far_maps α β r hr κ)

def primitive := FarNormalizedDiagonalCap.primitive m
  (StrictLengthProductFamilies.leftEvaluation (OriginalFirstHalfCutOutputJoinData.kept α r hr) (Q := Q))
  (StrictLengthProductFamilies.rightEvaluation β (P := CompactRotatedCutData.source α r)) hκ hm hκ2

theorem primitive_far : cochainPullback (SupportedCap.subspaceMap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
    (farSet α β r hr κ)) m (primitive α β r hr κ hκ hm hκ2) = 0 :=
  FarNormalizedDiagonalCap.primitive_supported m _ _ hκ hm hκ2 (farSet α β r hr κ) (far_maps α β r hr κ)

theorem primitive_boundary : cochainCoboundary (ZMod 2) (OriginalFirstHalfCutProductCochains.space α r (Q := Q)) m
    (primitive α β r hr κ hκ hm hκ2) =
    CompactJoinCocycle.cocycle (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ - specified α β r hr := by
  have he := FarNormalizedDiagonalCap.primitive_boundary m
    (StrictLengthProductFamilies.leftEvaluation (OriginalFirstHalfCutOutputJoinData.kept α r hr) (Q := Q))
    (StrictLengthProductFamilies.rightEvaluation β (P := CompactRotatedCutData.source α r)) hκ hm hκ2
  rw [CompactNormalizedJoinCapComparison.cocycle_eq] at he
  exact he

variable (F : ReversibleMetric (m + 1)) (B R : ℝ) (hκR : 2 * κ ≤ R)

def specifiedOperation := BoundedFarCarrierCap.operation α β r hr F B κ R hκR (m + 1) (specified α β r hr)
  (specified_far α β r hr κ hκ) (specified_closed α β r hr)

def primitiveCap (q : ℕ) := BoundedFarCarrierCap.component α β r hr F B κ R hκR m (primitive α β r hr κ hκ hm hκ2)
  (primitive_far α β r hr κ hκ hm hκ2) q

theorem normalized_source (q : ℕ) : (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).component q ≫
    (push (SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R))).f q =
    (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (BoundedCarrierJoinCap.rectangles α β r hr F B κ)).f ((m + 1) + q) ≫
    RelativeCapAssociativity.absoluteChain (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (m + 1) q ((m + 1) + q) rfl
      (cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) (m + 1)
        (CompactJoinCocycle.cocycle (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ)) := by
  rw [BoundedKeptProductInputs.cocycle]
  exact BoundedCarrierJoinCap.source α β r hr F B κ R hκ hκR q

include hm hκ2 in
theorem homology_eq (q : ℕ) : (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).homology q =
    (specifiedOperation α β r hr κ hκ F B R hκR).homology q := by
  have hb : cochainCoboundary (ZMod 2) (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) m
      (cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) m (primitive α β r hr κ hκ hm hκ2)) =
    cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) (m + 1)
      (CompactJoinCocycle.cocycle (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ) -
    cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) (m + 1) (specified α β r hr) := by
    rw [DiagonalCutSwap.pullback_coboundary, primitive_boundary, DiagonalCutSwap.pullback_sub]
  exact LiftedRepresentativeComparison.homology_eq
    (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) (BoundedCarrierJoinCap.rectangles α β r hr F B κ)
    (chains (TopCat.of (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R)))
    (push (SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R)))
    (fun q => SupportedCap.subspacePush_mono _ _ q) m _ _ _ hb
    (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR) (specifiedOperation α β r hr κ hκ F B R hκR)
    (normalized_source α β r hr κ hκ F B R hκR)
    (BoundedFarCarrierCap.source α β r hr F B κ R hκR (m + 1) (specified α β r hr) (specified_far α β r hr κ hκ))
    (primitiveCap α β r hr κ hκ hm hκ2 F B R hκR)
    (BoundedFarCarrierCap.source α β r hr F B κ R hκR m (primitive α β r hr κ hκ hm hκ2)
      (primitive_far α β r hr κ hκ hm hκ2)) q

end
end Finsler.BoundedJoinRepresentative
