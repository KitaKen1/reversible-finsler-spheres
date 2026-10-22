module

public import Finsler.Loop.FirstInputRotationTimeEndpoints

/-! Uniform actual full-time rotation comparison. The mismatch radius
works for every later smaller tube; the rectangle scale precedes all
tested degrees, cochains and length thresholds. -/

@[expose] public section
namespace Finsler.FirstInputRotationUniformFullTime

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem exists_uniform {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1)))
    {δ ρ r ε b : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r < 1)
    (F : ReversibleMetric (m + 1)) (hε : 0 < ε) (hb : 0 < b)
    (hradius : r < SelfCutLengthControl.radius F hε) :
    ∃ κ > 0, κ ≤ 1 / 2 ∧ ∀ (R : ℝ) (hR : R ≤ 1 / 2), R < κ →
      ∃ η > 0, ∃ hη : 0 < η, η ≤ b ∧
      ∀ (p : ℕ) (L A : ℝ)
        (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
        (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0),
        cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (SelfCutOscillation.short F L)) p T = 0 →
        (∀ z : CompactNearJoinParameters.tube α β R,
          SobolevLength.length F (α z.val.1) + SobolevLength.length F (β z.val.2) < A) →
        ∃ hgood : FirstInputRotationTestedCap.Adequate α β R r hR hr F (A - L + 5 * ε) η p T,
        ∀ q,
          (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F (A - L + 5 * ε)
            η hη hρr hgood hT 0).homology q =
          (FirstInputRotationTimeEndpoints.endpoint α β R r hR hr p T h F (A - L + 5 * ε)
            η hη hρr hgood hT 1).homology q := by
  obtain ⟨κ, hκ, hκ1, hscale⟩ := FirstInputRotationTestedCap.exists_uniform α β r hr F hε hb hradius
  refine ⟨κ, hκ, hκ1, ?_⟩
  intro R hR hRκ
  obtain ⟨η, hη, hηb, had⟩ := hscale R hR hRκ
  refine ⟨η, hη, hη, hηb, ?_⟩
  intro p L A T hT hshort hA
  exact ⟨had p L A T hshort hA,
    FirstInputRotationTimeEndpoints.homology_eq α β R r hR hr p T h F (A - L + 5 * ε)
      η hη hρr (had p L A T hshort hA) hT⟩

end
end Finsler.FirstInputRotationUniformFullTime
