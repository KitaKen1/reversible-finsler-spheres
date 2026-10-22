module

public import Finsler.Loop.BoundedCarrierJoinCap
public import Finsler.Loop.MappedSmallRectangleCross
public import Finsler.Loop.LocalizedCapCupComponentSource

/-! The actual bounded-kept rectangle cap and external cross map to the
original proper-cut rectangle cap by strict chain identities, including
all native degree transports. No bounded center is chosen. -/

@[expose] public section
namespace Finsler.BoundedCarrierJoinNaturality

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CompactH1Alignment
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.FarNormalizedDiagonalCap
open scoped Simplicial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (B κ R : ℝ) (hκ : 0 < κ) (hκR : 2 * κ ≤ R)

theorem cap (k : ℕ) : (BoundedCarrierJoinCap.properRectangle α β r hr F B κ).f ((m + 1) + k) ≫
    (CompactJoinCapLocalization.localized (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ hκR).component k =
    (BoundedCarrierJoinCap.operation α β r hr F B κ R hκ hκR).component k ≫
      (push (BoundedKeptProductInputs.properTube α β r hr F B R)).f k := by
  have : Mono ((push (SupportedCap.subspaceMap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
      (CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β R))).f k) :=
    SupportedCap.subspacePush_mono _ _ _
  apply (cancel_mono ((push (SupportedCap.subspaceMap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
    (CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β R))).f k)).mp
  have hj : (push (BoundedKeptProductInputs.properTube α β r hr F B R)).f k ≫
      (push (SupportedCap.subspaceMap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
        (CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β R))).f k =
    (push (SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
      (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R))).f k ≫
      (push (BoundedKeptProductInputs.properPair α r hr F B (Q := Q))).f k := by
    have he : BoundedKeptProductInputs.properTube α β r hr F B R ≫
        SupportedCap.subspaceMap (OriginalFirstHalfCutProductCochains.space α r (Q := Q))
          (CompactNearJoinParameters.tube (OriginalFirstHalfCutOutputJoinData.kept α r hr) β R) =
      SupportedCap.subspaceMap (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q))
        (CompactNearJoinParameters.tube (BoundedKeptProductInputs.kept α r hr F B) β R) ≫
          BoundedKeptProductInputs.properPair α r hr F B (Q := Q) := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      rfl
    have hf := congrArg (fun z => (push z).f k) he
    simpa only [push_comp, HomologicalComplex.comp_f] using hf
  have hn := RelativeCapBoundary.absolute_chain_natural (BoundedKeptProductInputs.properPair α r hr F B (Q := Q))
    (m + 1) k ((m + 1) + k) rfl
    (CompactJoinCocycle.cocycle (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ)
  rw [BoundedKeptProductInputs.cocycle] at hn
  change absoluteChain (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B × Q)) (m + 1) k ((m + 1) + k) rfl
      (CompactJoinCocycle.cocycle (BoundedKeptProductInputs.kept α r hr F B) β (dim_pos m) hκ) ≫
        (push (BoundedKeptProductInputs.properPair α r hr F B (Q := Q))).f k =
    (push (BoundedKeptProductInputs.properPair α r hr F B (Q := Q))).f ((m + 1) + k) ≫
      absoluteChain (OriginalFirstHalfCutProductCochains.space α r (Q := Q)) (m + 1) k ((m + 1) + k) rfl
        (CompactJoinCocycle.cocycle (OriginalFirstHalfCutOutputJoinData.kept α r hr) β (dim_pos m) hκ) at hn
  rw [Category.assoc, CompactJoinCapLocalization.source, ← Category.assoc,
    ← HomologicalComplex.comp_f, BoundedCarrierJoinCap.rectangle_source, HomologicalComplex.comp_f]
  rw [Category.assoc, ← hn, ← Category.assoc,
    ← BoundedCarrierJoinCap.source α β r hr F B κ R hκ hκR k]
  simp only [Category.assoc]
  rw [hj]

theorem maps_identity (Y : TopCat.{0}) {ι : Type} (U : ι → Set Y) (i : ι) :
    Set.MapsTo (𝟙 Y) (U i) (U (id i)) := fun _ hx => hx

theorem other_identity (Y : TopCat.{0}) {ι : Type} (U : ι → Set Y) (j : ℕ) :
    (SmallRetractionComparison.map U U (𝟙 Y) id (maps_identity Y U)).f j = 𝟙 ((small Y U).X j) := by
  have : Mono ((inclusion Y U).f j) :=
    inferInstanceAs (Mono ((sigmaConst.obj coeff).map
      ((Y.smallSingularSubcomplex U).ι.app (Opposite.op ⦋j⦌))))
  apply (cancel_mono ((inclusion Y U).f j)).mp
  have he := SmallRetractionComparison.map_inclusion U U (𝟙 Y) id (maps_identity Y U)
  rw [FarDiagonalCutComparison.push_identity, Category.comp_id] at he
  have hf := congrArg (fun z => z.f j) he
  rw [HomologicalComplex.comp_f] at hf
  exact hf.trans (Category.id_comp _).symm

theorem cross (i j : ℕ) :
    ((FirstInputSelfCutBoundedSpace.toProperSmall α r hr F B κ).f i ⊗ₘ
      𝟙 ((small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)).X j)) ≫
    SmallNormalizedCapShuffle.component (X := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y := TopCat.of Q)
      (FirstInputSelfCutCover.carrier α r hr κ)
      (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j =
    SmallNormalizedCapShuffle.component (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
      (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ)
      (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) i j ≫
      (BoundedCarrierJoinCap.properRectangle α β r hr F B κ).f (i + j) := by
  have he := MappedSmallRectangleCross.component
    (X := TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F B)) (Y := TopCat.of Q)
    (X' := OriginalFirstHalfCutNormalizedFactors.cutSpace α r) (Y' := TopCat.of Q)
    (FirstInputSelfCutBoundedSpace.carrier α r hr F B κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)
    (FirstInputSelfCutCover.carrier α r hr κ) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)
    (FirstInputSelfCutBoundedSpace.toCut α r hr F B) (𝟙 (TopCat.of Q)) id id
    (fun _ _ hz => hz) (maps_identity (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)) i j
  rw [other_identity (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) j] at he
  exact he

end
end Finsler.BoundedCarrierJoinNaturality
