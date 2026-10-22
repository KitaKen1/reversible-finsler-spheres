module

public import Finsler.Loop.OriginalFirstHalfZeroGammaComparison

/-! The generic supported-cochain scale supplies both the new gamma
bound and the old tested bound on the same actual tube and scale.
The real bounded cap comparison is therefore uniformly constructed. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfUniformZeroGammaComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem tested_adequate {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] {n : ℕ}
    (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r : ℝ) (hR : R ≤ 1 / 2) (hr : r < 1)
    (F : ReversibleMetric n) (B η : ℝ) (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
    (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F B η p
      (FirstInputRotationCochains.tested α β R r hR hr p T)) :
    FirstInputRotationTestedCap.Adequate α β R r hR hr F B η p T := good

theorem exists_uniform {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
    (r : ℝ) (hr : r < 1) {δ ρ ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)
    (F : ReversibleMetric (m + 1)) (hε : 0 < ε) (hb : 0 < b)
    (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ u > 0, u ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < u →
      ∃ η > 0, η ≤ b ∧ ∀ (p : ℕ) (L A : ℝ)
        (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
        (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
        cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
          (SelfCutOscillation.short F L)) p T = 0 →
        (∀ z : CompactNearJoinParameters.tube α β R,
          SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2) < A) →
        ∃ (good : FirstInputRotationSupportedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η ((m + 1) + p)
          (FirstInputRotationCupOne.gamma α β R r hR hr h p T))
          (oldGood : FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η p T),
        ∀ q,
          OriginalFirstHalfZeroGammaCap.component α β R r hR hr h p T F (A - L + 5 * ε) η good q ≫
            (push (OriginalFirstHalfJointSupportedCap.boundedStage α β R r hR hr F (A - L + 5 * ε))).f q =
          (OriginalFirstHalfZeroGammaComparison.smallAmbientMap α β R r η ρ).f (((m + 1) + p) + q) ≫
            (FirstInputRotationAmbientCap.operation α β R r hR hr p T (by omega) h F
              (A - L + 5 * ε) η oldGood hT).component q := by
  obtain ⟨u, hu, hu1, hscale⟩ := FirstInputRotationSupportedCap.exists_uniform α β r hr F hε hb hradius
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu
  obtain ⟨η, hη, hηb, had⟩ := hscale R hR hRu
  refine ⟨η, hη, hηb, ?_⟩
  intro p L A T hT hshort hA
  have good := had _ L A _ (TestedCupOneSupport.gamma_zero F (FirstInputRotationCochains.testedMap α β R r hR hr) L
    (m + 1) p (FirstInputRotationCochains.thom α β R r hR hr (by omega) h) T hshort) hA
  have goodT := had _ L A _ (TestedCupOneSupport.tested_zero F (FirstInputRotationCochains.testedMap α β R r hR hr)
    L p T hshort) hA
  have oldGood := tested_adequate α β R r hR hr F (A - L + 5 * ε) η p T goodT
  refine ⟨good, oldGood, ?_⟩
  intro q
  exact OriginalFirstHalfZeroGammaComparison.component_compare α β R r η ρ hR hr h p T F
    (A - L + 5 * ε) good oldGood hT q

end
end Finsler.OriginalFirstHalfUniformZeroGammaComparison
