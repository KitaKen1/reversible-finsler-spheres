module

public import Finsler.Loop.FullSecondHalfNativeCutFactors
public import Finsler.Loop.CylinderCommonCover
public import Finsler.Topology.AnnularDoubleCap

/-! The actual full second-half native bounded cap has the genuine
annular cut as its ambient chain image. Identify the small face and
retained output before passing to homology. -/

@[expose] public section
namespace Finsler.SecondHalfStartCapAgreement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m p : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (F : ReversibleMetric (m + 1)) (u : C(X, H1JoinContinuity.composable (m + 1)))
    (η B : ℝ)
    (hW : ∀ center, JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u 0 (by norm_num) (by norm_num) ρ 2 ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2)
    (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) (SecondHalfNativeFaceCapDomain.faceCover X η)).X
      ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded u hr F B))).X q)
    (hnative : ∀ q, (SecondHalfNativeFaceCapDomain.faceMap X η ≫
      JoinedLocalizedCutComparison.familySmallMap u 0 (by norm_num) (by norm_num) ρ r 2 (JoinedFilteredCap.rectangleCover X η) hW).f
        ((m + 1) + (p + q)) ≫
      SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
        (NormalizedSelfCut.testedCocycle (m + 1) p hr T) q ((m + 1) + (p + q)) rfl =
          c q ≫ (push (FullSecondHalfNativeLift.nativeCutBound u hr F B)).f q)

variable (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2) (θ : ℝ)

theorem start_family : planeFace (TopCat.of X) 0 ≫ JoinedFamilyNaturality.globalMap u a ha ha1 2 =
    JoinedHalfCollars.secondFamily u := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  change JoinedHalfCollars.secondFamily u (InteriorTimeSlide.slide a ha ha1 (0, z.1), z.2) = _
  rw [InteriorTimeSlide.slide_zero]

variable (d : ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X θ)).X
    ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).X q)
  (hd : ∀ q, d q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (JoinedFilteredCap.sublevel F B))).f q =
    (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X θ)).f ((m + 1) + (p + q)) ≫
      (push (JoinedFamilyNaturality.globalMap u a ha ha1 2)).f ((m + 1) + (p + q)) ≫
      eqToHom (congrArg (chains (parameters (m + 1))).X
        (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫ AnnularCutComparison.cut m p h hρr hr T hT q)

include hnative hd in
theorem agreement (q : ℕ) :
    (CylinderCommonCover.toSource (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
      (SecondHalfNativeFaceCapDomain.faceCover X η) (JoinedFilteredCap.rectangleCover X θ)
      (planeFace (TopCat.of X) 0)).f ((m + 1) + (p + q)) ≫ c q ≫
      (push (FullSecondHalfNativeTimeOperation.retainedOutput u hr F B)).f q =
    (CylinderCommonCover.toTarget (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
      (SecondHalfNativeFaceCapDomain.faceCover X η) (JoinedFilteredCap.rectangleCover X θ)
      (planeFace (TopCat.of X) 0)).f ((m + 1) + (p + q)) ≫ d q := by
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (JoinedFilteredCap.sublevel F B))).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B) q
  apply (cancel_mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (JoinedFilteredCap.sublevel F B))).f q)).mp
  have hs := FullSecondHalfNativeCutFactors.cap_inclusion m p h hρr hr T hT F u η B hW c hnative q
  have hMs := congrArg (fun z => z.f ((m + 1) + (p + q)))
    (CylinderCommonCover.toSource_inclusion (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
      (SecondHalfNativeFaceCapDomain.faceCover X η) (JoinedFilteredCap.rectangleCover X θ) (planeFace (TopCat.of X) 0))
  have hMt := congrArg (fun z => z.f ((m + 1) + (p + q)))
    (CylinderCommonCover.toTarget_inclusion (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
      (SecondHalfNativeFaceCapDomain.faceCover X η) (JoinedFilteredCap.rectangleCover X θ) (planeFace (TopCat.of X) 0))
  simp only [HomologicalComplex.comp_f] at hMs hMt
  have hg := congrArg (fun z => (push z).f ((m + 1) + (p + q))) (start_family m u a ha ha1)
  simp only [push_comp, HomologicalComplex.comp_f] at hg
  simp only [Category.assoc]
  rw [hs, hd q]
  simp only [← Category.assoc]
  rw [hMs, hMt]
  simp only [Category.assoc]
  rw [← Category.assoc ((push (planeFace (TopCat.of X) 0)).f ((m + 1) + (p + q))), hg]

end
end Finsler.SecondHalfStartCapAgreement
