module

public import Finsler.Loop.OriginalFirstHalfCutThenJoinTime
public import Finsler.Loop.OriginalFirstHalfUniformActualJoinCupConnection

/-! On every supplied sufficiently small tube and normalized radius,
one scale before tested data connects the genuine corrected first-half
join operation to the actual original-cylinder gamma-first, retained-
right-cut join-second full-time model in literal A-L+5epsilon. The
external-product D_T(alpha) joined with beta factorization is separate. -/

@[expose] public section
namespace Finsler.OriginalFirstHalfUniformCutThenJoinTime

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
      ∃ η : ℝ, ∃ hη : 0 < η, η ≤ b ∧ ∀ (κ : ℝ) (hκ : 0 < κ) (h2κR : 2 * κ ≤ R),
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
          (FirstInputRotationJoinedTime.joined α β hκ h2κR hR hr p T h F
            (A - L + 5 * ε) η hη hρr oldGood hT 1).homology q =
          (OriginalFirstHalfCutThenJoinTime.operation α β R r η hR hr hκ hκR hη h hρr
            p T F (A - L + 5 * ε) good hT).homology q := by
  obtain ⟨u, hu, hu1, hscale⟩ := OriginalFirstHalfUniformActualJoinCupConnection.exists_uniform
    α β h hρr hr F hε hb hradius
  refine ⟨u, hu, hu1, ?_⟩
  intro R hR hRu
  obtain ⟨η, hη, hηb, had⟩ := hscale R hR hRu
  refine ⟨η, hη, hηb, ?_⟩
  intro κ hκ h2κR
  obtain ⟨hκR, htested⟩ := had κ hκ h2κR
  refine ⟨hκR, ?_⟩
  intro p L A T hT hshort hA
  obtain ⟨goodΓ, oldGood, goodχ, goodδ, good, he⟩ := htested p L A T hT hshort hA
  refine ⟨goodΓ, oldGood, goodχ, goodδ, good, ?_⟩
  intro q
  exact (he q).trans (OriginalFirstHalfCutThenJoinTime.homology_eq α β R r η hR hr hκ hκR hη h hρr
    p T F (A - L + 5 * ε) good hT q).symm

end
end Finsler.OriginalFirstHalfUniformCutThenJoinTime
