module

public import Finsler.Loop.SingleCutCanonicalTwoStage
public import Finsler.Loop.SmallCapRetractionHomology
public import Finsler.Loop.LocalizedCapCupCompositionSource

/-! Exact one-cup/two-cap agreement on the real canonical common
cover. The tested extension need only be closed on the proper domain.
The ordinary retained source of the genuine filtered two-stage map is
identified by an equality of actual chains. -/

@[expose] public section
namespace Finsler.SingleCutCanonicalCupOnCommonCover

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SupportedCapNaturality Finsler.SmallChainCarrier Finsler.RelativeCapAssociativity
open Finsler.FirstInputSelfCutCochains

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P : Type} [PseudoMetricSpace P] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (r : ℝ) (hr : r < 1)
  (F : ReversibleMetric (m + 1)) (a R : ℝ) (hrR : r < R)
  (hA : ∀ x, SobolevLength.length F (α x) < a) (hR : R ≤ 1) (ε : ℝ)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)

theorem tested_source : cochainPullback (source α r) p
    (FirstInputRotationZeroTimeFactors.originalTested α r hr p T) =
      cochainPullback (FirstInputRotationOriginalFactors.originalTester α r hr) p T := by
  rw [FirstInputRotationZeroTimeFactors.originalTested,
    show source α r = SupportedCap.subspaceMap (ambient α) (CompactRotatedCutData.source α r) from rfl,
    TubeCochainExtension.restriction]

include hT in
theorem tested_closed : cochainCoboundary (ZMod 2) (OriginalFirstHalfCutNormalizedFactors.cutSpace α r) p
    (cochainPullback (source α r) p (FirstInputRotationZeroTimeFactors.originalTested α r hr p T)) = 0 := by
  rw [tested_source]
  exact pullback_closed _ _ _ hT

def testedCap := SmallCapRetractionHomology.smallCap (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
  (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε) p
  (cochainPullback (source α r) p (FirstInputRotationZeroTimeFactors.originalTested α r hr p T))
  (tested_closed α r hr p T hT)

def operation := DegreeLoweringComposition.compose
  (SingleCutCanonicalThomSmallLift.operation α r F a R hrR hA hR ε h)
  (testedCap α r hr F a R hrR hA hR ε p T hT)

theorem component_source (q : ℕ) :
    (operation α r hr F a R hrR hA hR ε h p T hT).component q ≫
      (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
        (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε) ≫ push (source α r)).f q =
    (inclusion (ambient α) (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ)).f (((m + 1) + p) + q) ≫
      absoluteChain (ambient α) ((m + 1) + p) q (((m + 1) + p) + q) rfl
        (SingleCutCanonicalThomCochains.canonicalGamma α r hr h p T) := by
  have he := LocalizedCapCupCompositionSource.component_source
    (SingleCutCanonicalThomSmallLift.cover α r F a R hrR hA hR ε ρ)
    (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε) (source α r)
    (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε))
    (SingleCutCanonicalThomCochains.canonicalThom α h)
    (FirstInputRotationZeroTimeFactors.originalTested α r hr p T)
    (SingleCutCanonicalThomSmallLift.operation α r F a R hrR hA hR ε h)
    (testedCap α r hr F a R hrR hA hR ε p T hT)
    (fun j => by simpa only [HomologicalComplex.comp_f, Category.assoc] using
      SingleCutCanonicalThomSmallLift.component_source α r F a R hrR hA hR ε h j)
    (fun j => SmallCapCarrier.smallCap_inclusion _ _ p j (p + j) rfl _) q
  rw [SingleCutCanonicalThomCochains.canonicalGamma, CupOne.cup_comparison]
  exact he

def cupComponent (q : ℕ) := FarSubspaceSmallCap.component (ambient α) (CompactRotatedCutData.source α r)
  (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)
  (SingleCutCanonicalIncoming.cover_open α r F a R hrR hA hR ε) (far α ρ)
  (SingleCutCanonicalThomSmallLift.near α r)
  (fun z hz => show SupportedSelfCut.distance (m + 1) (z.1, α z.2) ≤ r from hz.le)
  ((m + 1) + p) (SingleCutCanonicalThomCochains.canonicalGamma α r hr h p T)
  (SingleCutCanonicalThomCochains.gamma_far_zero α r hr h p T) q

theorem component_eq_cup (q : ℕ) :
    (operation α r hr F a R hrR hA hR ε h p T hT).component q =
      cupComponent α r hr F a R hrR hA hR ε h p T q := by
  haveI : Mono ((inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
      (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε) ≫ push (source α r)).f q) := by
    simpa only [SmallCapSubspaceLift.target, SmallCapSubspaceLift.source,
      Iso.refl_hom, Category.id_comp, FirstInputSelfCutCochains.source] using
      SmallCapSubspaceLift.target_mono (ambient α) (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
        (CompactRotatedCutData.source α r) (Iso.refl _)
        (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε) q
  apply (cancel_mono ((inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
    (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε) ≫ push (source α r)).f q)).mp
  rw [component_source]
  exact (FarSubspaceSmallCap.component_source (ambient α) (CompactRotatedCutData.source α r)
    (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)
    (SingleCutCanonicalIncoming.cover_open α r F a R hrR hA hR ε) (far α ρ)
    (SingleCutCanonicalThomSmallLift.near α r)
    (fun z hz => show SupportedSelfCut.distance (m + 1) (z.1, α z.2) ≤ r from hz.le)
    ((m + 1) + p) (SingleCutCanonicalThomCochains.canonicalGamma α r hr h p T)
    (SingleCutCanonicalThomCochains.gamma_far_zero α r hr h p T) q).symm

variable (hε : 0 < ε) (hRR : R ≤ SelfCutLengthControl.radius F hε) (L : ℝ)
  (hshort : cochainPullback (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (SelfCutOscillation.short F L)) p T = 0)

theorem filtered_twoStage_source (q : ℕ) :
    (SingleCutCanonicalTwoStage.operation α r F a R hrR hA hR ε h hε hRR L p T hT hshort).component q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (SelfCutOscillation.short F (a - L + 3 * ε)))).f q =
    cupComponent α r hr F a R hrR hA hR ε h p T q ≫
      (inclusion (OriginalFirstHalfCutNormalizedFactors.cutSpace α r)
        (SingleCutCanonicalIncoming.cover α r F a R hrR hA hR ε)).f q ≫
      (push (TopCat.ofHom (OriginalFirstHalfCutOutputJoinData.kept α r hr))).f q := by
  rw [← component_eq_cup α r hr F a R hrR hA hR ε h p T hT q]
  have hs := SingleCutCanonicalTestedSmall.component_source F hR hε hRR p T hT hshort α r hr hrR hA q
  change (SingleCutCanonicalIncoming.smallMap α r F a R hrR hA hR ε).f (p + q) ≫
    (FilteredTestedCap.smallOperation F hR hε hRR p T hT hshort).component q ≫ _ = _ at hs
  rw [operation, SingleCutCanonicalTwoStage.operation, DegreeLoweringComposition.component,
    DegreeLoweringComposition.component]
  dsimp only [SingleCutCanonicalThomSmallLift.testedSmall, DegreeLoweringHomology.Map.post]
  simp only [Category.assoc]
  rw [hs]
  dsimp only [testedCap, SmallCapRetractionHomology.smallCap]
  rw [← Category.assoc (SmallCapCarrier.smallCap _ _ p q (p + q) rfl _),
    SmallCapCarrier.smallCap_inclusion, tested_source]
  simp only [Category.assoc]

end
end Finsler.SingleCutCanonicalCupOnCommonCover
