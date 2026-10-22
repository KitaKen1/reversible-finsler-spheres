module

public import Finsler.Loop.JoinedNativeCanonicalTime

/-! Exact real budget transport for actual native full/canonical time
comparison. The target transport is equality of the SAME short bound,
not an inclusion into a larger sublevel. -/

@[expose] public section
namespace Finsler.JoinedNativeCanonicalBudget

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 2400000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q] [CompactSpace P] [CompactSpace Q] {m : ℕ}
    (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r : ℝ)
    (hR : R ≤ 1 / 2) (hr : r < 1) (F : ReversibleMetric (m + 1))
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1 / 2) (B θ ζ : ℝ) (hθ : 0 < θ) (hζ : 0 < ζ)
    (p : ℕ) (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r)
    (hg : FirstInputRotationTestedCap.Adequate α β R r hR hr F B ζ p T)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (D : JoinedRotationSplitData.Data α β R r hR hr F s hs hs1 B θ ζ hθ hζ p T h hρr hg hT)
    (ε a L : ℝ) (hε : 0 < ε) (hbudget : a - L + 3 * ε = B)
    (κ₀ σ : ℝ) (hσ : 0 < σ) (hradius : r < SelfCutLengthControl.radius F hε)
    (hsmall : SingleInputCutMetricAdequacy.Adequate (JoinedNativeCanonicalTime.joinedFamily α β R hR) r hr F ε σ)
    (index : (ClosedInterval × CompactNearJoinParameters.tube α β R) →
      Option (CompactRotatedCutData.source (JoinedNativeCanonicalTime.joinedFamily α β R hR) r))
    (hindex : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆
      FirstInputSelfCutCover.cover (JoinedNativeCanonicalTime.joinedFamily α β R hR) r hr κ₀ ρ (index c))
    (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (SelfCutOscillation.short F L)) p T = 0)
    (hA : ∀ x, SobolevLength.length F (JoinedNativeCanonicalTime.joinedFamily α β R hR x) < a) (hm : 1 ≤ m)

include hσ hradius hsmall hindex hm in
theorem full_homology (q : ℕ) : D.full.homology q =
    (((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshort).pre
      (push (CompactInputShortMaps.family (JoinedNativeCanonicalTime.joinedFamily α β R hR) F a hA))).post
      (eqToHom (congrArg (fun c : ℝ => chains (TopCat.of (SelfCutOscillation.short F c))) hbudget))).homology q := by
  subst B
  simpa only [eqToHom_refl, DegreeLoweringHomology.Map.post_homology,
    HomologicalComplex.homologyMap_id, Category.comp_id] using
    JoinedNativeCanonicalTime.full_homology α β R r hR hr F s hs hs1 θ ζ hθ hζ p T h hρr ε a L hε hg hT D
      κ₀ σ hσ hradius hsmall index hindex hshort hA hm q

end
end Finsler.JoinedNativeCanonicalBudget
