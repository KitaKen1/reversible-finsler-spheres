module

public import Finsler.Topology.FirstHalfNativeTimeFactors
public import Finsler.Topology.FirstHalfFaceRefinement

/-! Retain the original outer small-cap scale. A common finer source
cover compares the actual first-half cut-domain cap with that outer cap
literally in the same retained-length target, by chain monicity only. -/

@[expose] public section
namespace Finsler.FirstHalfRefinedCapAgreement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

theorem agreement {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m p : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (F : ReversibleMetric (m + 1)) (u : C(X, H1JoinContinuity.composable (m + 1)))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2) (η η₀ η₁ B : ℝ) (hη₀ : η ≤ η₀) (hη₁ : η ≤ η₁)
    (hW : ∀ center, JoinedFilteredCap.rectangleCover X η₁ center ⊆ JoinedRectangleRefinement.far u a ha.le ha1.le ρ 1 ∨
      JoinedFilteredCap.rectangleCover X η₁ center ⊆ domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
    (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η₁)).X
      ((m + 1) + (p + q)) ⟶ (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)).X q)
    (hnative : ∀ q, (FirstHalfInteriorCapDomain.faceMap X η₁ ≫
      JoinedLocalizedCutComparison.familySmallMap u a ha.le ha1.le ρ r 1 (JoinedFilteredCap.rectangleCover X η₁) hW).f
        ((m + 1) + (p + q)) ≫
      SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
        (NormalizedSelfCut.testedCocycle (m + 1) p hr T) q ((m + 1) + (p + q)) rfl =
          c q ≫ (push (FirstHalfNativeCapDeformation.nativeCut u a ha ha1 hr F B)).f q)
    (d : ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)).X
      ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).X q)
    (hd : ∀ q, d q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (JoinedFilteredCap.sublevel F B))).f q =
      (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)).f ((m + 1) + (p + q)) ≫
        (push (JoinedFamilyNaturality.globalMap u a ha.le ha1.le 1)).f ((m + 1) + (p + q)) ≫
          eqToHom (congrArg (chains (parameters (m + 1))).X
            (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
              AnnularCutComparison.cut m p h hρr hr T hT q) (q : ℕ) :
    (FirstHalfFaceRefinement.map X hη₁).f ((m + 1) + (p + q)) ≫ c q ≫
      (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B)).f q =
        (FirstHalfFaceRefinement.toOuter X hη₀).f ((m + 1) + (p + q)) ≫ d q := by
  haveI : Mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (JoinedFilteredCap.sublevel F B))).f q) :=
    SupportedCap.subspacePush_mono (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B) q
  apply (cancel_mono ((push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (JoinedFilteredCap.sublevel F B))).f q)).mp
  have hs := FirstHalfNativeTimeFactors.cap_inclusion m p h hρr hr T hT F u a ha ha1 η₁ B hW c hnative q
  have h₁ := congrArg (fun z => z.f ((m + 1) + (p + q))) (FirstHalfFaceRefinement.map_inclusion X hη₁)
  have h₀ := congrArg (fun z => z.f ((m + 1) + (p + q))) (FirstHalfFaceRefinement.toOuter_inclusion X hη₀)
  simp only [HomologicalComplex.comp_f] at h₀ h₁
  have hg := congrArg (fun z => (push z).f ((m + 1) + (p + q))) (JoinedEndpointMaps.first_end u a ha.le ha1.le)
  simp only [push_comp, HomologicalComplex.comp_f] at hg
  simp only [Category.assoc]
  rw [hs, hd q]
  simp only [← Category.assoc]
  rw [h₁, h₀]
  simp only [Category.assoc]
  rw [← Category.assoc ((push (planeFace (TopCat.of X) 1)).f ((m + 1) + (p + q))), hg]

end
end Finsler.FirstHalfRefinedCapAgreement
