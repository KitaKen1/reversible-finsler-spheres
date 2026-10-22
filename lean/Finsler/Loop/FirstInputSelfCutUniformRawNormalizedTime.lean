module

public import Finsler.Loop.FirstInputSelfCutUniformAllDegreesTime
public import Finsler.Loop.FirstInputSelfCutNormalizationTime
public import Finsler.Loop.FirstInputSelfCutLowDegreeTime
public import Finsler.Loop.FirstInputSelfCutTimeFactorization
public import Finsler.Loop.FirstInputSelfCutFactorwiseRefinement
public import Finsler.Loop.OriginalFirstHalfUniformNormalizedTensorTime
public import Finsler.Loop.OriginalFirstHalfNormalizedCutThenJoinTime
public import Finsler.Loop.OriginalFirstHalfCutThenJoinTime

/-! The actual separate single-input normalization/time comparison
shares the existing before-tested scales, homogeneous time factorization,
all low-degree zeros and same-length geometric retained comparison. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutUniformRawNormalizedTime

open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfJointSupportedCap Finsler.OriginalFirstHalfCupOrderCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem exists_uniform {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r < 1)
    (F : ReversibleMetric (m + 1)) (hε : 0 < ε) (hb : 0 < b)
    (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ u > 0, u ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < u →
      ∃ η : ℝ, ∃ hη : 0 < η, η ≤ b ∧ ∀ (κ : ℝ) (hκ : 0 < κ) (h2κR : 2 * κ ≤ R),
      ∃ hκR : κ < R, ∃ σ : ℝ, ∃ hσ : 0 < σ, σ ≤ b ∧
      ∃ index : (ClosedInterval × P) × Q → Option (Option (FirstInputRotationCochains.space α β R r)),
      ∃ hindex : ∀ c, Set.MapsTo (OriginalFirstHalfNormalizationExternalShuffle.reorder α β)
        (SmallRectangleShuffle.rectangles (X := TopCat.of (ClosedInterval × P)) (Y := TopCat.of Q)
          (OriginalFirstHalfFactorwiseCover.first σ) (OriginalFirstHalfFactorwiseCover.other σ) c)
        (OriginalFirstHalfJointCover.cover α β R r η κ ρ (index c)),
      ∃ firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r),
      ∃ hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ FirstInputSelfCutCover.cover α r hr κ ρ (firstIndex c),
      ∃ otherIndex : Q → Q,
      ∃ hother : ∀ c, OriginalFirstHalfFactorwiseCover.other σ c ⊆
        OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ (otherIndex c),
      ∀ (p : ℕ) (L A : ℝ)
        (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
        (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
        cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (SelfCutOscillation.short F L)) p T = 0 →
        (∀ x y, SobolevLength.length F (α x) + SobolevLength.length F (β y) < A) →
        ∃ (goodχ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          ((m + 1) + (m + p)) (OriginalFirstHalfNormalizationCup.properPrimitive α β r hr h p T hκ R hR))
          (goodδ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          (((m + 1) + (m + p)) + 1)
          (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
            (OriginalFirstHalfNormalizationCup.properPrimitive α β r hr h p T hκ R hR)))
          (goodN : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          (((m + 1) + (m + p)) + 1) (OriginalFirstHalfNormalizationCup.properOrder α β r hr h p T hκ R hR))
          (goodOld : ∀ v : Bool, FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          (((m + 1) + (m + p)) + 1) (properOrder α β R r hR hr h p T hκ v)),
        ∀ q,
          ((OriginalFirstHalfFactorwiseNormalizedTime.operation α β R r hR hr h p T hκ hκR F
            (A - L + 5 * ε) η hη hρr goodN hT σ hσ index hindex).post
              (push (retained α β R r hR hr F (A - L + 5 * ε)))).homology q =
          ((OriginalFirstHalfCutThenJoinTime.operation α β R r η hR hr hκ hκR hη h hρr p T F
            (A - L + 5 * ε) goodOld hT).pre
              (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))).homology q ∧
          (∀ (i j : ℕ) (hij : i + j = (m + 1) + q),
            FirstInputSelfCutTimeFactorization.geometric α β R r hr hκ h2κR h p T hT σ hσ
              firstIndex hfirst otherIndex hother i j q hij =
            HomologicalComplex.ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) ((m + p) + i) j
              (((m + 1) + (m + p)) + q) (by omega) ≫
              (OriginalFirstHalfFactorwiseNormalizedTime.operation α β R r hR hr h p T hκ hκR F
                (A - L + 5 * ε) η hη hρr goodN hT σ hσ index hindex).component q ≫
              (push (OriginalFirstHalfCutOutputJoinBounded.toNear α β R r hR hr F (A - L + 5 * ε))).f q) ∧
          (∀ (l j : ℕ) (hN : l + j = ((m + 1) + (m + p)) + q), l < m + p →
            HomologicalComplex.ιTensorObj (chains (TopCat.of P)) (chains (TopCat.of Q)) l j
              (((m + 1) + (m + p)) + q) hN ≫
              (OriginalFirstHalfFactorwiseNormalizedTime.operation α β R r hR hr h p T hκ hκR F
                (A - L + 5 * ε) η hη hρr goodN hT σ hσ index hindex).component q = 0) ∧
          (FirstInputSelfCutTime.operation α r hr κ h p T hT σ hσ firstIndex hfirst true).homology q =
            (FirstInputSelfCutTime.operation α r hr κ h p T hT σ hσ firstIndex hfirst false).homology q ∧
          (FirstInputSelfCutTime.sectioned α r hr κ h p T hT σ hσ firstIndex hfirst true).homology q =
            (FirstInputSelfCutTime.sectioned α r hr κ h p T hT σ hσ firstIndex hfirst false).homology q := by
  obtain ⟨u, hu, hu1, hscale⟩ := FirstInputSelfCutUniformAllDegreesTime.exists_uniform
    α β h hρr hr F hε hb hradius
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu
  obtain ⟨η, hη, hηb, hdata⟩ := hscale R hR hRu
  refine ⟨η, hη, hηb, ?_⟩
  intro κ hκ h2κR
  obtain ⟨hκR, σ, hσ, hσb, index, hindex, firstIndex, hfirst, otherIndex, hother, htested⟩ := hdata κ hκ h2κR
  refine ⟨hκR, σ, hσ, hσb, index, hindex, firstIndex, hfirst, otherIndex, hother, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨goodχ, goodδ, goodN, goodOld, hcmp⟩ := htested p L A T hT hshort hA
  refine ⟨goodχ, goodδ, goodN, goodOld, ?_⟩
  intro q
  exact ⟨(hcmp q).1, (hcmp q).2.1, (hcmp q).2.2,
    FirstInputSelfCutNormalizationTime.homology_eq α r hr κ h p T hT σ hσ firstIndex hfirst q,
    FirstInputSelfCutNormalizationTime.sectioned_homology_eq α r hr κ h p T hT σ hσ firstIndex hfirst q⟩

end
end Finsler.FirstInputSelfCutUniformRawNormalizedTime
