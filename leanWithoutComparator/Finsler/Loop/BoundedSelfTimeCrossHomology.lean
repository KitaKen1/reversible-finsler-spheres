module

public import Finsler.Loop.DegreeLoweringCrossSummand
import all Finsler.Loop.DegreeLoweringCrossSummand
public import Finsler.Loop.BoundedSelfTimeHomologyInput
public import Finsler.Loop.BoundedSelfTimeFilteredJoin

/-! The real original retained time operation on homogeneous tensor
homology factors through the actual bounded sectioned self-time and
beta subdivision, followed by the genuine closed filtered join. Native
casts and the literal strict-length target are retained. -/

@[expose] public section
namespace Finsler.BoundedSelfTimeCrossHomology

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
  (hR : R ≤ 1 / 2) (hr : r < 1) {κ δ ρ : ℝ} (hκ : 0 < κ) (h2κR : 2 * κ ≤ R) (hκR : κ < R)
  (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a b A L η σ : ℝ) (hε : 0 < ε) (hη : 0 < η) (hσ : 0 < σ) (hρr : ρ < r)
  (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η (((m + 1) + (m + p)) + 1)
    (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR))
  (index : (ClosedInterval × P) × Q → Option (Option (FirstInputRotationCochains.space α β R r)))
  (hindex : ∀ c, Set.MapsTo (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)
    (SmallRectangleShuffle.rectangles (X := ambient α) (Y := TopCat.of Q)
      (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) c)
    (OriginalFirstHalfJointCover.cover α β R r η κ ρ (index c)))
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (otherIndex : Q → Q)
  (hother : ∀ c, OriginalFirstHalfFactorwiseCover.other σ c ⊆
    OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ (otherIndex c))

  (hRu : R < BoundedCarrierUniformRawJoin.radius α β r hr F hε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)
  (hab : a + b < A) (hβ : ∀ y, SobolevLength.length F (β y) < b)

def retainedOperation :=
  (OriginalFirstHalfFactorwiseNormalizedTime.operation α β R r hR hr h p T hκ hκR F (A - L + 5 * ε) η hη hρr
    goodN hT σ hσ index hindex).post
    (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F (A - L + 5 * ε)))

def filteredJoin := (BoundedCarrierExternalJoin.operation α β r hr F (a - L + 3 * ε) κ R hκ h2κR).post
  (push (BoundedCarrierFilteredOutput.joinMap α β r hr F hε R hR hRu (L := L) hab hβ))

theorem native_component (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    ((FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA true).component i ⊗ₘ
      (BoundedSelfTimeHomologyInput.otherChain κ σ hσ β otherIndex hother).f j) ≫
    ιTensorObj (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
      (small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)) i j ((m + 1) + k) hij ≫
      (filteredJoin α β R r hR hr hκ h2κR F ε a b A L hε hRu hab hβ).component k =
    ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) ≫
      (retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ hη hσ hρr goodN index hindex).component k := by
  have he := BoundedSelfTimeFilteredJoin.retained_component α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ
    hε hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ i j k hij
  rw [BoundedSelfCutTimeExternalJoin.closed_join_summand] at he
  simpa only [filteredJoin, retainedOperation, DegreeLoweringHomology.Map.post,
    BoundedSelfTimeFilteredJoin.originalComponent, BoundedSelfCutTimeExternalJoin.tensorInput,
    BoundedSelfTimeHomologyInput.other_component, Category.assoc] using he

theorem homology_factor (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) ≫
      (retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ hη hσ hρr goodN index hindex).homology k =
    ((FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA true).homology i ⊗ₘ
      homologyMap (BoundedSelfTimeHomologyInput.otherChain κ σ hσ β otherIndex hother) j) ≫
    homologyCross (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
      (small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)) i j ((m + 1) + k) hij ≫
      (filteredJoin α β R r hR hr hκ h2κR F ε a b A L hε hRu hab hβ).homology k := by
  exact DegreeLoweringCrossSummand.homology
    (chains (TopCat.of P)) (chains (TopCat.of Q))
    (small (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
      (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ))
    (small (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ))
    (chains (StrictLengthEnergyBridge.lengthSpace F (A - L + 5 * ε))) (m + p) (m + 1)
    (FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA true)
    (BoundedSelfTimeHomologyInput.otherChain κ σ hσ β otherIndex hother)
    (retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ hη hσ hρr goodN index hindex)
    (filteredJoin α β R r hR hr hκ h2κR F ε a b A L hε hRu hab hβ) i j k hij
    (native_component α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ hε hη hσ hρr goodN index hindex
      firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ i j k hij)

end
end Finsler.BoundedSelfTimeCrossHomology
