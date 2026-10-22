module

public import Finsler.Loop.OriginalFirstHalfSequentialTimeComparison
public import Finsler.Loop.OriginalFirstHalfUniformZeroGammaComparison

/-! A single supplied-tube scale for the real sequential join/gamma,
the existing tested cap, the cup-one primitive and both cup orders.
The actual full-time comparison is retained in literal A-L+5epsilon. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfUniformSequentialTimeComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier
open Finsler.OriginalFirstHalfJointSupportedCap Finsler.OriginalFirstHalfCupOrderCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

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
        ∃ (goodΓ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          ((m + 1) + p) (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
          (oldGood : FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η p T)
          (goodχ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          ((m + 1) + (m + p)) (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ))
          (goodδ : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          (((m + 1) + (m + p)) + 1)
          (cochainCoboundary (ZMod 2) (FirstInputRotationCochains.space α β R r) ((m + 1) + (m + p))
            (FirstInputRotationCupOne.primitive α β R r hR hr h p T hκ)))
          (good : ∀ v : Bool, FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
          (((m + 1) + (m + p)) + 1) (properOrder α β R r hR hr h p T hκ v)),
        ∀ q,
          ((OriginalFirstHalfSequentialTimeComparison.onJoin α β R r hR hr h p T hκ F
            (A - L + 5 * ε) η hη hκR hρr goodΓ hT).post
              (push (retained α β R r hR hr F (A - L + 5 * ε)))).homology q =
          ((OriginalFirstHalfCupOrderTimeHomology.operation α β R r hR hr h p T hκ hκR F
            (A - L + 5 * ε) η hη hρr good hT true).post
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
  have goodΓ := had _ L A _ (TestedCupOneSupport.gamma_zero F (FirstInputRotationCochains.testedMap α β R r hR hr) L
    (m + 1) p (FirstInputRotationCochains.thom α β R r hR hr (by omega) h) T hshort) hAtube
  have goodT := had _ L A _ (TestedCupOneSupport.tested_zero F (FirstInputRotationCochains.testedMap α β R r hR hr)
    L p T hshort) hAtube
  have oldGood := OriginalFirstHalfUniformZeroGammaComparison.tested_adequate α β R r hR hr F
    (A - L + 5 * ε) η p T goodT
  have goodχ := had _ L A _ (FirstInputRotationCupOne.primitive_short_zero α β R r hR hr h p T hκ F L hshort) hAtube
  have goodδ := had _ L A _ (FirstInputRotationCupOne.primitive_boundary_short_zero α β R r hR hr h p T hκ F L hshort) hAtube
  have good : ∀ v : Bool, FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η
      (((m + 1) + (m + p)) + 1) (properOrder α β R r hR hr h p T hκ v) := fun v =>
    had _ L A _ (proper_short_zero α β R r hR hr h p T hκ v F L hshort) hAtube
  refine ⟨goodΓ, oldGood, goodχ, goodδ, good, ?_⟩
  intro q
  rw [OriginalFirstHalfSequentialTimeComparison.retained_join_cup α β R r hR hr h p T hκ F
    (A - L + 5 * ε) η hη hκR hρr goodΓ good hT q]
  simp only [DegreeLoweringHomology.Map.post_homology]
  rw [OriginalFirstHalfCupOrderTimeHomology.homology_eq α β R r hR hr h p T hκ hκR F
    (A - L + 5 * ε) η hη hρr good hT goodχ goodδ q]

end
end Finsler.OriginalFirstHalfUniformSequentialTimeComparison
