module

public import Finsler.Loop.BoundedCarrierFilteredOutput
public import Finsler.Loop.BoundedSelfCutTimeExternalJoin

/-! The actual bounded self-time/external-beta/closed-join component and
the original factorwise normalized time component agree as literal
chains in short(F,A-L+5epsilon). The raw-join radius is chosen before
all individual thresholds; no later product-radius hypothesis is used. -/

@[expose] public section
namespace Finsler.BoundedSelfTimeFilteredJoin

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.FirstInputSelfCutCochains Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

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

def originalComponent (i j k : ℕ) (hij : i + j = (m + 1) + k) :=
  ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j
    (((m + 1) + (m + p)) + k) (by omega) ≫
    (OriginalFirstHalfFactorwiseNormalizedTime.operation α β R r hR hr h p T hκ hκR F (A - L + 5 * ε) η hη hρr
      goodN hT σ hσ index hindex).component k

theorem near_component (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    BoundedSelfCutTimeExternalJoin.geometric α β R r hr hκ h2κR h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA otherIndex hother i j k hij ≫
      (push (BoundedKeptProductInputs.properTube α β r hr F (a - L + 3 * ε) R)).f k =
    originalComponent α β R r hR hr hκ hκR h p T hT F ε A L η σ hη hσ hρr goodN index hindex i j k hij ≫
      (push (OriginalFirstHalfCutOutputJoinBounded.toNear α β R r hR hr F (A - L + 5 * ε))).f k := by
  have he := (BoundedSelfCutTimeExternalJoin.to_proper α β R r hr hκ h2κR h p T hT F ε a L σ hσ hε hradius hsmall
    firstIndex hfirst hshortT hA otherIndex hother i j k hij).trans
    (FirstInputSelfCutTimeFactorization.component_eq α β R r hR hr hκ h2κR hκR h p T hT F (A - L + 5 * ε) η σ
      hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother i j k hij)
  simpa only [originalComponent, Category.assoc] using he

theorem retained_component (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    BoundedSelfCutTimeExternalJoin.geometric α β R r hr hκ h2κR h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA otherIndex hother i j k hij ≫
      (push (BoundedCarrierFilteredOutput.joinMap α β r hr F hε R hR hRu (L := L) hab hβ)).f k =
    originalComponent α β R r hR hr hκ hκR h p T hT F ε A L η σ hη hσ hρr goodN index hindex i j k hij ≫
      (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F (A - L + 5 * ε))).f k := by
  exact BoundedCarrierFilteredOutput.component_eq α β r hr F hε R hR hRu (L := L) hab hβ k _ _
    (near_component α β R r hR hr hκ h2κR hκR h p T hT F ε a A L η σ hε hη hσ hρr goodN index hindex
      firstIndex hfirst otherIndex hother hradius hsmall hshortT hA i j k hij)

end
end Finsler.BoundedSelfTimeFilteredJoin
