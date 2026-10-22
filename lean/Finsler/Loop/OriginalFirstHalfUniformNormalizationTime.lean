module

public import Finsler.Loop.OriginalFirstHalfNormalizationTime

/-! One supplied tube/radius and one common scale for the actual
normalization primitive, its coboundary, normalized cup and existing
cup operations. Their full-time comparison keeps literal length<A-L+5epsilon. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfUniformNormalizationTime

open CategoryTheory AlgebraicTopology SphereOddDegree
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
          ((OriginalFirstHalfNormalizationTime.normalizedTime α β R r hR hr h p T hκ hκR F
            (A - L + 5 * ε) η hη hρr goodN hT).post
              (push (retained α β R r hR hr F (A - L + 5 * ε)))).homology q =
          ((OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F
            (A - L + 5 * ε) η hη hρr goodOld hT true).post
              (push (retained α β R r hR hr F (A - L + 5 * ε)))).homology q := by
  obtain ⟨u, hu, hu1, hscale⟩ := FirstInputRotationSupportedCap.exists_uniform α β r hr F hε hb hradius
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu
  obtain ⟨η, hη, hηb, had⟩ := hscale R hR hRu
  refine ⟨η, hη, hηb, ?_⟩
  intro κ hκ h2κR
  have hκR : κ < R := by linarith
  refine ⟨hκR, ?_⟩
  intro p L A T hT hshort hA
  have hAtube : ∀ z : CompactNearJoinParameters.tube α β R,
      SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2) < A := fun z => hA z.val.1 z.val.2
  have goodχ := had _ L A _ (OriginalFirstHalfNormalizationCup.proper_primitive_short_zero α β r hr h p T hκ R hR F L hshort) hAtube
  have goodδ := had _ L A _ (OriginalFirstHalfNormalizationCup.proper_boundary_short_zero α β r hr h p T hκ R hR F L hshort) hAtube
  have goodN := had _ L A _ (OriginalFirstHalfNormalizationCup.proper_order_short_zero α β r hr h p T hκ R hR F L hshort) hAtube
  have goodOld : ∀ v : Bool, FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
      (((m + 1) + (m + p)) + 1) (properOrder α β R r hR hr h p T hκ v) := fun v =>
    had _ L A _ (proper_short_zero α β R r hR hr h p T hκ v F L hshort) hAtube
  refine ⟨goodχ, goodδ, goodN, goodOld, ?_⟩
  intro q
  simp only [DegreeLoweringHomology.Map.post_homology]
  rw [OriginalFirstHalfNormalizationTime.homology_eq α β R r hR hr h p T hκ hκR F
    (A - L + 5 * ε) η hη hρr goodχ goodδ goodN goodOld hT q]

end
end Finsler.OriginalFirstHalfUniformNormalizationTime
