module

public import Finsler.Topology.FirstHalfAnnularTimeDomain
public import Finsler.Topology.AnnularDoubleCap

/-! Literal chain identities linking the actual cut-domain first-half
cap to the original native annular cut, with its actual small-chain
retraction. The retained-length inclusion is compared before homology. -/

@[expose] public section
namespace Finsler.FirstHalfNativeTimeFactors

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X] {n : ℕ}
  (u : C(X, H1JoinContinuity.composable n)) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

theorem face_inclusion (ρ r η : ℝ)
    (hW : ∀ center, JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha.le ha1.le ρ 1 ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1) :
    (FirstHalfInteriorCapDomain.faceMap X η ≫
      JoinedLocalizedCutComparison.familySmallMap u a ha.le ha1.le ρ r 1 (JoinedFilteredCap.rectangleCover X η) hW) ≫
        inclusion (parameters n) (SupportedCap.cover (parameters n) (exterior n ρ) (neighborhood n r)) =
      inclusion (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η) ≫
        push (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) := by
  rw [Category.assoc, JoinedLocalizedCutComparison.familySmallMap_inclusion]
  have hf : FirstHalfInteriorCapDomain.faceMap X η ≫
      inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) =
    inclusion (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η) ≫
      push (planeFace (TopCat.of X) 1) := by
    exact SmallRetractionComparison.map_inclusion
      (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
      (FirstHalfInteriorCapDomain.faceCover X η) (JoinedFilteredCap.rectangleCover X η)
      (planeFace (TopCat.of X) 1) id (fun i z hz => show
        planeFace (TopCat.of X) 1 z ∈ JoinedFilteredCap.rectangleCover X η i from hz)
  rw [← Category.assoc, hf, Category.assoc, ← push_comp, JoinedEndpointMaps.first_end]

theorem retained_inclusion {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) :
    FirstHalfNativeCapDeformation.nativeCut u a ha ha1 hr F B ≫ TopCat.ofHom (SupportedSelfCut.retained n hr) =
      FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B ≫
        SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (JoinedFilteredCap.sublevel F B) := by
  ext z : 1
  rfl

theorem cap_inclusion {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m p : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (F : ReversibleMetric (m + 1)) (u : C(X, H1JoinContinuity.composable (m + 1)))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2) (η B : ℝ)
    (hW : ∀ center, JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha.le ha1.le ρ 1 ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
    (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η)).X
      ((m + 1) + (p + q)) ⟶ (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)).X q)
    (hc : ∀ q, (FirstHalfInteriorCapDomain.faceMap X η ≫
      JoinedLocalizedCutComparison.familySmallMap u a ha.le ha1.le ρ r 1 (JoinedFilteredCap.rectangleCover X η) hW).f
        ((m + 1) + (p + q)) ≫
      SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
        (NormalizedSelfCut.testedCocycle (m + 1) p hr T) q ((m + 1) + (p + q)) rfl =
          c q ≫ (push (FirstHalfNativeCapDeformation.nativeCut u a ha ha1 hr F B)).f q) (q : ℕ) :
    c q ≫ (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B)).f q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
      (inclusion (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η)).f ((m + 1) + (p + q)) ≫
        (push (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le)).f ((m + 1) + (p + q)) ≫
          eqToHom (congrArg (chains (parameters (m + 1))).X
            (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
              AnnularCutComparison.cut m p h hρr hr T hT q := by
  have hs := AnnularDoubleCap.canonical_cut_on_small m p h hρr hr T
    (FirstHalfInteriorCapDomain.faceCover X η)
    (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le)
    (FirstHalfInteriorCapDomain.faceMap X η ≫
      JoinedLocalizedCutComparison.familySmallMap u a ha.le ha1.le ρ r 1 (JoinedFilteredCap.rectangleCover X η) hW)
    (face_inclusion u a ha ha1 ρ r η hW) hT q
  rw [← Category.assoc _ _ ((push (TopCat.ofHom (SupportedSelfCut.retained (m + 1) hr))).f q),
    hc q, Category.assoc, ← HomologicalComplex.comp_f, ← push_comp,
    retained_inclusion, push_comp, HomologicalComplex.comp_f] at hs
  simpa only [Category.assoc] using hs.symm

end
end Finsler.FirstHalfNativeTimeFactors
