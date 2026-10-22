module

public import Finsler.Loop.FirstInputSelfCutBoundedTime
public import Finsler.Loop.FirstInputSelfCutTimeFactorization
public import Finsler.Loop.SingleCutCanonicalDT
public import Finsler.Topology.SmallInclusionHomologyCancellation

/-! Actual source homology sections disappear only after their proved
input inverse identities. The real sectioned bounded time retains the
canonical D_T value, and the real beta section retains its own short
input. No strict chain naturality of subdivision is asserted. -/

@[expose] public section
namespace Finsler.BoundedSelfTimeHomologyInput

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree TauCeti
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.FirstInputSelfCutCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1) (κ : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (ε a L σ : ℝ) (hσ : 0 < σ) (hε : 0 < ε)
  (hradius : r < SelfCutLengthControl.radius F hε)
  (hsmall : SingleInputCutMetricAdequacy.Adequate α r hr F ε σ)
  (firstIndex : (ClosedInterval × P) → Option (CompactRotatedCutData.source α r))
  (hfirst : ∀ c, OriginalFirstHalfFactorwiseCover.first σ c ⊆ cover α r hr κ ρ (firstIndex c))
  (hshortT : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)
  (hA : ∀ x, SobolevLength.length F (α x) < a)


theorem sectioned_homology (v : Bool) (q : ℕ) :
    (FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA v).homology q =
    (FirstInputSelfCutBoundedTime.operation α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA v).homology q := by
  rw [FirstInputSelfCutBoundedTime.sectioned, DegreeLoweringHomology.Map.pre_homology,
    homologyMap_comp, SmallInclusionHomologyCancellation.homology_section,
    Category.id_comp]

theorem retained_input (v : Bool) (q : ℕ) :
    (FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA v).homology q ≫
      homologyMap (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) ≫
        push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε))) q =
    (FirstInputSelfCutBoundedTime.retained α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA v).homology q := by
  rw [sectioned_homology, FirstInputSelfCutBoundedTime.retained, DegreeLoweringHomology.Map.post_homology]

theorem canonical_input (S : ℝ) (hρr : ρ < r)
    (hSe : S = SelfCutLengthControl.radius F hε) (hρe : ρ = S / 2) (hm : 1 ≤ m) (v : Bool) (q : ℕ) :
    (FirstInputSelfCutBoundedTime.sectioned α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
      firstIndex hfirst hshortT hA v).homology q ≫
      homologyMap (inclusion (TopCat.of (FirstInputSelfCutBoundedSpace.bounded α r hr F (a - L + 3 * ε)))
        (FirstInputSelfCutBoundedSpace.carrier α r hr F (a - L + 3 * ε) κ) ≫
        push (FirstInputSelfCutBoundedSpace.retained α r hr F (a - L + 3 * ε))) q =
    ((FilteredPrismSelfCut.canonicalOperation m p F hε T hT hshortT).pre
      (push (CompactInputShortMaps.family α F a hA))).homology q := by
  rw [retained_input]
  exact SingleCutCanonicalDT.retained_canonical_DT α r hr κ h p T hT F ε a L σ hσ hε hradius hsmall
    firstIndex hfirst hshortT hA S hρr hSe hρe hm v q

variable {Q : Type} [PseudoMetricSpace Q] (β : C(Q, SphereLoop (m + 1)))
  (otherIndex : Q → Q)
  (hother : ∀ c, OriginalFirstHalfFactorwiseCover.other σ c ⊆
    OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ (otherIndex c))

def otherChain :=
  smallSingularRetraction (X := TopCat.of Q) coeff (OriginalFirstHalfFactorwiseCover.other σ)
    (OriginalFirstHalfFactorwiseCover.other_open σ) (OriginalFirstHalfFactorwiseCover.other_univ hσ) ≫
  FirstInputSelfCutBoundedFactorization.otherMap β σ otherIndex hother

theorem other_component (j : ℕ) : (otherChain κ σ hσ β otherIndex hother).f j =
    FirstInputSelfCutTimeFactorization.otherSection β σ hσ otherIndex hother j := rfl

theorem other_homology (j : ℕ) : homologyMap (otherChain κ σ hσ β otherIndex hother) j ≫
    homologyMap (inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ)) j =
    𝟙 ((chains (TopCat.of Q)).homology j) := by
  have hi : FirstInputSelfCutBoundedFactorization.otherMap β σ otherIndex hother ≫
      inclusion (TopCat.of Q) (OriginalFirstHalfNormalizedCutJoinFactor.otherCover β κ) =
    inclusion (TopCat.of Q) (OriginalFirstHalfFactorwiseCover.other σ) :=
    SmallRefinementComparison.refinement_inclusion _ _ _ _
  rw [← homologyMap_comp, otherChain, Category.assoc, hi, homologyMap_comp]
  exact SmallInclusionHomologyCancellation.homology_section (TopCat.of Q)
    (OriginalFirstHalfFactorwiseCover.other σ) (OriginalFirstHalfFactorwiseCover.other_open σ)
    (OriginalFirstHalfFactorwiseCover.other_univ hσ) j

end
end Finsler.BoundedSelfTimeHomologyInput
