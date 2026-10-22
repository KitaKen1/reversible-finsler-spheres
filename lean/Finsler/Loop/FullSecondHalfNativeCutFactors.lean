module

public import Finsler.Loop.FullSecondHalfNativeTimeOperation
public import Finsler.Topology.AnnularDoubleCap

/-! The actual full second-half native bounded cap has the genuine
annular cut as its ambient chain image. Identify the small face and
retained output before passing to homology. -/

@[expose] public section
namespace Finsler.FullSecondHalfNativeCutFactors

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
  (u : C(X, H1JoinContinuity.composable n))

theorem face_inclusion (ρ r η : ℝ)
    (hW : ∀ center, JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u 0 (by norm_num) (by norm_num) ρ 2 ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2) :
    (SecondHalfNativeFaceCapDomain.faceMap X η ≫
      JoinedLocalizedCutComparison.familySmallMap u 0 (by norm_num) (by norm_num) ρ r 2 (JoinedFilteredCap.rectangleCover X η) hW) ≫
        inclusion (parameters n) (SupportedCap.cover (parameters n) (exterior n ρ) (neighborhood n r)) =
      inclusion (TopCat.of (ClosedInterval × X)) (SecondHalfNativeFaceCapDomain.faceCover X η) ≫
        push (JoinedHalfCollars.secondFamily u) := by
  rw [Category.assoc, JoinedLocalizedCutComparison.familySmallMap_inclusion]
  have hf : SecondHalfNativeFaceCapDomain.faceMap X η ≫
      inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η) =
    inclusion (TopCat.of (ClosedInterval × X)) (SecondHalfNativeFaceCapDomain.faceCover X η) ≫
      push (planeFace (TopCat.of X) 1) := by
    exact SmallRetractionComparison.map_inclusion
      (X := TopCat.of (ClosedInterval × X)) (Y := TopCat.of (Outer X))
      (SecondHalfNativeFaceCapDomain.faceCover X η) (JoinedFilteredCap.rectangleCover X η)
      (planeFace (TopCat.of X) 1) id (fun i z hz => show
        planeFace (TopCat.of X) 1 z ∈ JoinedFilteredCap.rectangleCover X η i from hz)
  rw [← Category.assoc, hf, Category.assoc, ← push_comp, SecondHalfZeroFaceGeometry.face_family]

theorem retained_inclusion {r : ℝ} (hr : r ≤ 1) (F : ReversibleMetric n) (B : ℝ) :
    FullSecondHalfNativeLift.nativeCutBound u hr F B ≫ TopCat.ofHom (SupportedSelfCut.retained n hr) =
      FullSecondHalfNativeTimeOperation.retainedOutput u hr F B ≫
        SupportedCap.subspaceMap (TopCat.of (SphereLoop n)) (JoinedFilteredCap.sublevel F B) := by
  ext z : 1
  rfl

theorem cap_inclusion {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m p : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (F : ReversibleMetric (m + 1)) (u : C(X, H1JoinContinuity.composable (m + 1)))
    (η B : ℝ)
    (hW : ∀ center, JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u 0 (by norm_num) (by norm_num) ρ 2 ∨
      JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u 0 (by norm_num) (by norm_num)) (fun _ => r) 2)
    (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) (SecondHalfNativeFaceCapDomain.faceCover X η)).X
      ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded u hr F B))).X q)
    (hc : ∀ q, (SecondHalfNativeFaceCapDomain.faceMap X η ≫
      JoinedLocalizedCutComparison.familySmallMap u 0 (by norm_num) (by norm_num) ρ r 2 (JoinedFilteredCap.rectangleCover X η) hW).f
        ((m + 1) + (p + q)) ≫
      SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
        (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
        (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
        (NormalizedSelfCut.testedCocycle (m + 1) p hr T) q ((m + 1) + (p + q)) rfl =
          c q ≫ (push (FullSecondHalfNativeLift.nativeCutBound u hr F B)).f q) (q : ℕ) :
    c q ≫ (push (FullSecondHalfNativeTimeOperation.retainedOutput u hr F B)).f q ≫
      (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
      (inclusion (TopCat.of (ClosedInterval × X)) (SecondHalfNativeFaceCapDomain.faceCover X η)).f ((m + 1) + (p + q)) ≫
        (push (JoinedHalfCollars.secondFamily u)).f ((m + 1) + (p + q)) ≫
          eqToHom (congrArg (chains (parameters (m + 1))).X
            (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫
              AnnularCutComparison.cut m p h hρr hr T hT q := by
  have hs := AnnularDoubleCap.canonical_cut_on_small m p h hρr hr T
    (SecondHalfNativeFaceCapDomain.faceCover X η)
    (JoinedHalfCollars.secondFamily u)
    (SecondHalfNativeFaceCapDomain.faceMap X η ≫
      JoinedLocalizedCutComparison.familySmallMap u 0 (by norm_num) (by norm_num) ρ r 2 (JoinedFilteredCap.rectangleCover X η) hW)
    (face_inclusion u ρ r η hW) hT q
  rw [← Category.assoc _ _ ((push (TopCat.ofHom (SupportedSelfCut.retained (m + 1) hr))).f q),
    hc q, Category.assoc, ← HomologicalComplex.comp_f, ← push_comp,
    retained_inclusion, push_comp, HomologicalComplex.comp_f] at hs
  simpa only [Category.assoc] using hs.symm

end
end Finsler.FullSecondHalfNativeCutFactors
