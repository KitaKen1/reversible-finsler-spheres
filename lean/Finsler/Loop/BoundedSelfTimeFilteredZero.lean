module

public import Finsler.Loop.BoundedSelfTimeFilteredJoin
public import Finsler.Loop.BoundedSelfCutTimeZero

/-! The real retained original factorwise time component is zero in
its actual strict length target in either nonpositive input branch.
The before-threshold raw-join map and the proved filtered chain square
transport the actual geometric zero, including output degree zero. -/

@[expose] public section
namespace Finsler.BoundedSelfTimeFilteredZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalPreadditive HomologicalComplex AlgebraicTopology SphereOddDegree
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
theorem first_nonpos (hB : a - L + 3 * ε ≤ 0) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    BoundedSelfTimeFilteredJoin.originalComponent α β R r hR hr hκ hκR h p T hT F ε A L η σ hη hσ hρr goodN index hindex i j k hij ≫
      (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F (A - L + 5 * ε))).f k = 0 := by
  have he := BoundedSelfTimeFilteredJoin.retained_component α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ
    hε hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ i j k hij
  rw [BoundedSelfCutTimeZero.bounded_geometric_zero α β R r hr hκ h2κR h p T hT F ε a L σ hσ hε hradius hsmall
    firstIndex hfirst hshortT hA otherIndex hother hB i j k hij, zero_comp] at he
  exact he.symm

include h2κR firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ in
theorem beta_nonpos (hb : b ≤ 0) (i j k : ℕ) (hij : i + j = (m + 1) + k) :
    BoundedSelfTimeFilteredJoin.originalComponent α β R r hR hr hκ hκR h p T hT F ε A L η σ hη hσ hρr goodN index hindex i j k hij ≫
      (push (OriginalFirstHalfJointSupportedCap.retained α β R r hR hr F (A - L + 5 * ε))).f k = 0 := by
  have hz : BoundedSelfCutTimeExternalJoin.geometric α β R r hr hκ h2κR h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA otherIndex hother i j k hij = 0 := by
    rw [BoundedSelfCutTimeExternalJoin.geometric, BoundedSelfCutTimeExternalJoin.tensorInput,
      BoundedSelfCutTimeZero.other_zero β F σ hσ otherIndex hother hβ hb j, tensor_zero, zero_comp]
  have he := BoundedSelfTimeFilteredJoin.retained_component α β R r hR hr hκ h2κR hκR h p T hT F ε a b A L η σ
    hε hη hσ hρr goodN index hindex firstIndex hfirst otherIndex hother hRu hradius hsmall hshortT hA hab hβ i j k hij
  rw [hz, zero_comp] at he
  exact he.symm

end
end Finsler.BoundedSelfTimeFilteredZero
