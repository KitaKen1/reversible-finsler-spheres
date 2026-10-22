module

public import Finsler.Loop.BoundedJoinRepresentative
public import Finsler.Loop.ClosedCarrierSupportedComparison

/-! The original fixed-scale normalized cap is compared in its own
closed bounded carrier with the specified diagonal cap in any smaller
positive open near neighborhood. No later product radius changes the
original kappa, R, input rectangles, or cap. -/

@[expose] public section
namespace Finsler.BoundedSpecifiedCapShrink

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FarNormalizedDiagonalCap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (B κ R : ℝ) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

theorem specified_pullback :
    cochainPullback (BoundedKeptProductInputs.properPair α r hr F B (Q := Q)) (m + 1)
      (BoundedJoinRepresentative.specified α β r hr) =
    DiagonalPullbackCut.cocycle (dim_pos m)
      (StrictLengthProductFamilies.leftEvaluation (BoundedKeptProductInputs.kept α r hr F B) (Q := Q))
      (StrictLengthProductFamilies.rightEvaluation β (P := FirstInputSelfCutBoundedSpace.bounded α r hr F B)) := by
  rw [BoundedJoinRepresentative.specified, ← DiagonalCutNaturality.cocycle_pullback]
  rfl

theorem specified_source (q : ℕ) :
    (BoundedJoinRepresentative.specifiedOperation α β r hr κ hκ F B R hκR).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
        (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R))).f q =
    (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (BoundedCarrierJoinCap.rectangles α β r hr F B κ)).f ((m + 1) + q) ≫
    RelativeCapAssociativity.absoluteChain (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (m + 1) q ((m + 1) + q) rfl
      (DiagonalPullbackCut.cocycle (dim_pos m)
        (StrictLengthProductFamilies.leftEvaluation (BoundedKeptProductInputs.kept α r hr F B) (Q := Q))
        (StrictLengthProductFamilies.rightEvaluation β (P := FirstInputSelfCutBoundedSpace.bounded α r hr F B))) := by
  have he := BoundedFarCarrierCap.source α β r hr F B κ R hκR (m + 1)
    (BoundedJoinRepresentative.specified α β r hr) (BoundedJoinRepresentative.specified_far α β r hr κ hκ) q
  rw [specified_pullback] at he
  exact he

variable (s : ℝ) (hs : 0 < s) (hsR : s ≤ R)

include hsR in
theorem near_sub : CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β s ⊆
    CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R := by
  intro z hz
  exact hz.le.trans hsR

include hs in
theorem diagonal_in_near (z : TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
    (hz : StrictLengthProductFamilies.leftEvaluation (BoundedKeptProductInputs.kept α r hr F B) z =
      StrictLengthProductFamilies.rightEvaluation β z) :
    z ∈ CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β s := by
  have hz' := congrArg Subtype.val hz
  change basepoint (BoundedKeptProductInputs.kept α r hr F B z.1) = basepoint (β z.2) at hz'
  change dist (basepoint (BoundedKeptProductInputs.kept α r hr F B z.1)) (basepoint (β z.2)) < s
  rw [hz', dist_self]
  exact hs

def intoCarrier := ClosedCarrierSupportedComparison.nearInclusion
  (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
  (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β s)
  (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R)
  (near_sub α β r hr F B R s hsR)

def smallOperation := DiagonalCutNaturality.operation (dim_pos m)
  (StrictLengthProductFamilies.leftEvaluation (BoundedKeptProductInputs.kept α r hr F B) (Q := Q))
  (StrictLengthProductFamilies.rightEvaluation β (P := FirstInputSelfCutBoundedSpace.bounded α r hr F B))
  (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β s)
  (CompactNormalizedJoinCapComparison.near_open _ _ s) (diagonal_in_near α β r hr F B s hs)

def specifiedUnrefined := (BoundedJoinRepresentative.specifiedOperation α β r hr κ hκ F B R hκR).pre
  (BoundedCarrierJoinCover.retraction α β r hr F B κ hκ)

theorem specified_homology (q : ℕ) :
    (specifiedUnrefined α β r hr F B κ R hκ hκR).homology q =
    ((smallOperation α β r hr F B s hs).post (push (intoCarrier α β r hr F B R s hsR))).homology q := by
  exact ClosedCarrierSupportedComparison.homology_eq
    (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
    (BoundedCarrierJoinCap.rectangles α β r hr F B κ)
    (DiagonalPullbackCut.exclusion
      (StrictLengthProductFamilies.leftEvaluation (BoundedKeptProductInputs.kept α r hr F B) (Q := Q))
      (StrictLengthProductFamilies.rightEvaluation β (P := FirstInputSelfCutBoundedSpace.bounded α r hr F B)))
    (CompactNormalizedJoinCapComparison.near (BoundedKeptProductInputs.kept α r hr F B) β s)
    (DiagonalPullbackCut.exclusion_open _ _) (CompactNormalizedJoinCapComparison.near_open _ _ s)
    (DiagonalPullbackCut.neighborhood_cover _ _ _ (diagonal_in_near α β r hr F B s hs))
    (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R) (near_sub α β r hr F B R s hsR)
    (m + 1) _ (DiagonalPullbackCut.cocycle_supported (dim_pos m) _ _)
    (DiagonalPullbackCut.cocycle_closed (dim_pos m) _ _)
    (BoundedJoinRepresentative.specifiedOperation α β r hr κ hκ F B R hκR)
    (specified_source α β r hr F B κ R hκ hκR)
    (BoundedCarrierJoinCover.isOpen α β r hr F B κ) (BoundedCarrierJoinCover.covers α β r hr F B κ hκ) q

theorem homology_eq (hm : 1 ≤ m) (hκ2 : κ ≤ 2) (q : ℕ) :
    (BoundedCarrierJoinCover.unrefined α β r hr F B κ R hκ hκR).homology q =
    ((smallOperation α β r hr F B s hs).post (push (intoCarrier α β r hr F B R s hsR))).homology q := by
  rw [BoundedCarrierJoinCover.unrefined, DegreeLoweringHomology.Map.pre_homology,
    BoundedJoinRepresentative.homology_eq α β r hr κ hκ hm hκ2 F B R hκR q]
  simpa only [specifiedUnrefined, DegreeLoweringHomology.Map.pre_homology] using
    specified_homology α β r hr F B κ R hκ hκR s hs hsR q

end
end Finsler.BoundedSpecifiedCapShrink
