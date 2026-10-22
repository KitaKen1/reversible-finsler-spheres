module

public import Finsler.Loop.FirstInputSelfCutBoundedFactorization
public import Finsler.Loop.FirstInputSelfCutFactorwiseRefinement
public import Finsler.Loop.OriginalFirstHalfUniformNormalizedTensorTime
public import Finsler.Loop.OriginalFirstHalfNormalizedCutThenJoinTime
public import Finsler.Loop.OriginalFirstHalfCutThenJoinTime

/-! One scale and three actual refinements before all tested data.
The all-input time comparison and the genuine single-input cut/external
beta/output-join bounded cap factorization share length<A-L+5epsilon. -/

@[expose] public section
namespace Finsler.FirstInputSelfCutUniformFactorization

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
          ∀ (i j : ℕ) (hij : i + j = (m + 1) + q),
            FirstInputSelfCutBoundedFactorization.geometric α β R r hr hκ h2κR h p T hT σ
              firstIndex hfirst otherIndex hother i j q hij =
            FirstInputSelfCutBoundedFactorization.bounded α β R r hR hr hκ h p T F (A - L + 5 * ε) η σ
              goodN index hindex i j q hij ≫
              (push (OriginalFirstHalfCutOutputJoinBounded.toNear α β R r hR hr F (A - L + 5 * ε))).f q := by
  obtain ⟨u, hu, hu1, hscale⟩ := OriginalFirstHalfUniformNormalizedTensorTime.exists_uniform
    α β h hρr hr F hε hb hradius
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu
  obtain ⟨η, hη, hηb, hdata⟩ := hscale R hR hRu
  refine ⟨η, hη, hηb, ?_⟩
  intro κ hκ h2κR
  obtain ⟨hκR, htested⟩ := hdata κ hκ h2κR
  obtain ⟨σ, hσ, hσb, index, firstIndex, otherIndex, hindex, hfirst, hother⟩ :=
    FirstInputSelfCutFactorwiseRefinement.exists_refinement α β R r η κ ρ hr hη hκ hκR hρr hb
  refine ⟨hκR, σ, hσ, hσb, index, hindex, firstIndex, hfirst, otherIndex, hother, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨goodχ, goodδ, goodN, goodOld, hcmp⟩ := htested p L A T hT hshort hA
  refine ⟨goodχ, goodδ, goodN, goodOld, ?_⟩
  intro q
  constructor
  · exact (OriginalFirstHalfFactorwiseNormalizedTime.retained_homology_eq α β R r hR hr h p T hκ hκR
    F (A - L + 5 * ε) η hη hρr goodN hT σ hσ index hindex q).symm.trans (hcmp q)
  · intro i j hij
    exact FirstInputSelfCutBoundedFactorization.component_eq α β R r hR hr hκ h2κR h p T hT
      F (A - L + 5 * ε) η σ goodN index hindex firstIndex hfirst otherIndex hother i j q hij


end
end Finsler.FirstInputSelfCutUniformFactorization
