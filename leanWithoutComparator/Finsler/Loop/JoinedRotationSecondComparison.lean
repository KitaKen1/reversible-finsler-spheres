module

public import Finsler.Loop.FullSecondHalfTrimmedTimeComparison
public import Finsler.Loop.JoinedRotationSplitData
public import Finsler.Loop.DegreeLoweringCompositionPostHomology
public import Finsler.Loop.JoinedSquareTimeHomology
public import Finsler.Topology.FilteredTimePrismOperation
public import Finsler.Topology.JoinedSmallCapExtension
public import Finsler.Loop.CutTimeCommonComparison
public import Finsler.Loop.CylinderCommonCover
public import Finsler.Topology.AnnularDoubleCap
import all Finsler.Loop.FullSecondHalfStartTimeComparison
import all Finsler.Loop.FullSecondHalfTrimmedTimeComparison

/-! The actual full second-half native bounded cap has the genuine
annular cut as its ambient chain image. Identify the small face and
retained output before passing to homology. -/

@[expose] public section
namespace Finsler.JoinedRotationSecondComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

attribute [local instance] FullSecondHalfCompactTimeOperation.tube_compactSpace

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
    [CompactSpace P] [CompactSpace Q]
    (m p : ℕ) (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R : ℝ) (hR : R ≤ 1 / 2) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r < 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (F : ReversibleMetric (m + 1))
    (η B : ℝ)
    (hW : ∀ center, JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆ JoinedRectangleRefinement.far (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) 0 (by norm_num) (by norm_num) ρ 2 ∨
      JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆ domain (tube (CompactNearJoinParameters.tube α β R)) (family (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) 0 (by norm_num) (by norm_num)) (fun _ => r) 2)
    (c : ∀ q, (small (TopCat.of (ClosedInterval × (CompactNearJoinParameters.tube α β R))) (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X
      ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) hr.le F B))).X q)
    (hnative : ∀ q, (SecondHalfNativeFaceCapDomain.faceMap (CompactNearJoinParameters.tube α β R) η ≫
      JoinedLocalizedCutComparison.familySmallMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) 0 (by norm_num) (by norm_num) ρ r 2 (JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η) hW).f
        ((m + 1) + (p + q)) ≫
      SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
        (NormalizedSelfCut.testedCocycle (m + 1) p hr.le T) q ((m + 1) + (p + q)) rfl =
          c q ≫ (push (FullSecondHalfNativeLift.nativeCutBound (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) hr.le F B)).f q)

variable (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2) (θ ζ : ℝ)
  (hθ : 0 < θ) (hζ : 0 < ζ)
  (hg : FirstInputRotationTestedCap.Adequate α β R r hR hr F B ζ p T)
  (D : JoinedRotationSplitData.Data α β R r hR hr F a ha ha1 B θ ζ hθ hζ p T h hρr hg hT)
  (hη : 0 < η)
  (hc : ∀ q, c (q + 1) ≫ (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) hr.le F B))).d (q + 1) q =
    (small (TopCat.of (ClosedInterval × (CompactNearJoinParameters.tube α β R))) (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d
      ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)
  (hsource : ∀ q, c q ≫ (push (FullSecondHalfNativeLift.nativeSource (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) hr.le F B)).f q =
    (inclusion (TopCat.of (ClosedInterval × (CompactNearJoinParameters.tube α β R))) (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f ((m + 1) + (p + q)) ≫
      PartialDoubleCap.cap (TopCat.of (ClosedInterval × (CompactNearJoinParameters.tube α β R))) (m + 1) p q
        (FullSecondHalfNativeTimeOperation.thom (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) (by omega) h) (FullSecondHalfNativeTimeOperation.tested (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) hr.le p T))
  (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R)))
    (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) hr.le F B))) (m + p))
  (hw : ∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
    ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R)) (SecondHalfNativeFaceCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
        (FullSecondHalfAnnularInputs.faceCover_open (CompactNearJoinParameters.tube α β R) η) (FullSecondHalfAnnularInputs.faceCover_univ (CompactNearJoinParameters.tube α β R) η hη) _ m p c) q)

  (h₀ : ∀ (s : ClosedInterval) (x : CompactNearJoinParameters.tube α β R), distance (m + 1)
    (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))
      a ha.le ha1.le 2 ((s, 0), x)) ≤ δ)
  (h₁ : ∀ (s : ClosedInterval) (x : CompactNearJoinParameters.tube α β R), distance (m + 1)
    (JoinedFamilyNaturality.globalMap (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))
      a ha.le ha1.le 2 ((s, 1), x)) ≤ δ)

variable {C : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ} {b : ℕ}
  (f : DegreeLoweringHomology.Map C (chains (TopCat.of (CompactNearJoinParameters.tube α β R))) b)

include hnative hc hsource hw h₀ h₁ in
theorem homology_eq (q : ℕ) :
    ((DegreeLoweringComposition.compose f w).post
      (push (FullSecondHalfNativeTimeOperation.retainedOutput (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) hr.le F B))).homology q =
      (DegreeLoweringComposition.compose f D.second).homology q := by
  apply DegreeLoweringCompositionPostHomology.post_congr f w
    (push (FullSecondHalfNativeTimeOperation.retainedOutput (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) hr.le F B)) D.second q
  exact FullSecondHalfTrimmedTimeComparison.homology_eq m p h hρr hr.le T hT F (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) η B hW c hnative
    a ha.le ha1.le θ (D.caps 2) (D.caps_source 2) hη hθ hc hsource (D.caps_comm 2) w hw D.second
    (fun q => by
      simpa only [show JoinedCommonInputRefinement.maps (TopCat.of (CompactNearJoinParameters.tube α β R)) 4 =
        planeFace (TopCat.of (CompactNearJoinParameters.tube α β R)) 1 from rfl,
        JoinedSmallCapExtension.cap, JoinedSimultaneousPrisms.retraction, HomologicalComplex.comp_f, Category.assoc]
        using D.second_component q) h₀ h₁ q

end
end Finsler.JoinedRotationSecondComparison
