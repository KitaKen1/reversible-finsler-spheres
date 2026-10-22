module

public import Finsler.Loop.OriginalFirstHalfNormalizedTensorTime
public import Finsler.Loop.OriginalFirstHalfNormalizedCutThenJoinTime
public import Finsler.Loop.OriginalFirstHalfCutThenJoinTime

/-! Uniform actual first-factor tensor-time comparison with the genuine
original-cylinder geometric cut-then-join operation after the external
cross, inside literal length<A-L+5epsilon and before tested data. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfUniformNormalizedTensorTime

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
      ∃ η : ℝ, ∃ hη : 0 < η, η ≤ b ∧ ∀ (κ : ℝ) (hκ : 0 < κ), 2 * κ ≤ R →
      ∃ hκR : κ < R, ∀ (p : ℕ) (L A : ℝ)
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
          ((OriginalFirstHalfNormalizedTensorTime.tensorTime α β R r hR hr h p T hκ hκR F
            (A - L + 5 * ε) η hη hρr goodN hT).post
              (push (retained α β R r hR hr F (A - L + 5 * ε)))).homology q =
          ((OriginalFirstHalfCutThenJoinTime.operation α β R r η hR hr hκ hκR hη h hρr p T F
            (A - L + 5 * ε) goodOld hT).pre
              (SmallRectangleCross.ambient (TopCat.of P) (TopCat.of Q))).homology q := by
  obtain ⟨u, hu, hu1, hscale⟩ := OriginalFirstHalfNormalizedCutThenJoinTime.exists_uniform
    α β h hρr hr F hε hb hradius
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu
  obtain ⟨η, hη, hηb, hdata⟩ := hscale R hR hRu
  refine ⟨η, hη, hηb, ?_⟩
  intro κ hκ h2κR
  obtain ⟨hκR, htested⟩ := hdata κ hκ h2κR
  refine ⟨hκR, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨goodχ, goodδ, goodN, goodOld, hcmp⟩ := htested p L A T hT hshort hA
  refine ⟨goodχ, goodδ, goodN, goodOld, ?_⟩
  intro q
  rw [← OriginalFirstHalfNormalizedTensorTime.retained_homology_eq α β R r hR hr h p T hκ hκR
    F (A - L + 5 * ε) η hη hρr goodN hT q]
  simp only [DegreeLoweringHomology.Map.post_homology, DegreeLoweringHomology.Map.pre_homology]
  rw [Category.assoc, ← DegreeLoweringHomology.Map.post_homology, hcmp q]


end
end Finsler.OriginalFirstHalfUniformNormalizedTensorTime
