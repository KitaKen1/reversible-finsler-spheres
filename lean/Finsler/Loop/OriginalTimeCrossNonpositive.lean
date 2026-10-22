module

public import Finsler.Loop.BoundedSelfTimeCrossHomology
public import Finsler.Loop.DegreeLoweringCrossZero
public import Finsler.Loop.BoundedSelfTimeFilteredZero

/-! Carry the already proved literal nonpositive retained native zeros
through the genuine original closed time operation to actual homology
cross inputs, in the same short output and including degree zero. -/

@[expose] public section
namespace Finsler.OriginalTimeCrossNonpositive

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

include h2κR firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ in
theorem first_native (hB : a - L + 3 * ε ≤ 0) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) ≫
      (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
        hη hσ hρr goodN index hindex).component k = 0 := by
  have he := BoundedSelfTimeFilteredZero.first_nonpos α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ
    hε hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ hB i j k hij
  simpa only [BoundedSelfTimeCrossHomology.retainedOperation, DegreeLoweringHomology.Map.post,
    BoundedSelfTimeFilteredJoin.originalComponent, Category.assoc] using he

include h2κR firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ in
theorem first_homology (hB : a - L + 3 * ε ≤ 0) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) ≫
      (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
        hη hσ hρr goodN index hindex).homology k = 0 := by
  exact DegreeLoweringCrossZero.homology (chains (TopCat.of P)) (chains (TopCat.of Q))
    (chains (StrictLengthEnergyBridge.lengthSpace F (A - L + 5 * ε))) ((m + 1) + (m + p))
    (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
      hη hσ hρr goodN index hindex) ((m + p) + i) j k (by omega)
    (first_native α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ hε hη hσ hρr
      goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ hB i j k hij)

include h2κR firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ in
theorem beta_native (hb : b ≤ 0) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) ≫
      (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
        hη hσ hρr goodN index hindex).component k = 0 := by
  have he := BoundedSelfTimeFilteredZero.beta_nonpos α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ
    hε hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ hb i j k hij
  simpa only [BoundedSelfTimeCrossHomology.retainedOperation, DegreeLoweringHomology.Map.post,
    BoundedSelfTimeFilteredJoin.originalComponent, Category.assoc] using he

include h2κR firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ in
theorem beta_homology (hb : b ≤ 0) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    homologyCross (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j (((m + 1) + (m + p)) + k) (by omega) ≫
      (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
        hη hσ hρr goodN index hindex).homology k = 0 := by
  exact DegreeLoweringCrossZero.homology (chains (TopCat.of P)) (chains (TopCat.of Q))
    (chains (StrictLengthEnergyBridge.lengthSpace F (A - L + 5 * ε))) ((m + 1) + (m + p))
    (BoundedSelfTimeCrossHomology.retainedOperation α β R r hR hr hκ hκR h p T hT F ε A L η σ
      hη hσ hρr goodN index hindex) ((m + p) + i) j k (by omega)
    (beta_native α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ hε hη hσ hρr
      goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ hb i j k hij)

end
end Finsler.OriginalTimeCrossNonpositive
