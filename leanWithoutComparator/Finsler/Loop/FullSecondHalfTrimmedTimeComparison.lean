module

public import Finsler.Loop.FullSecondHalfStartTimeComparison
public import Finsler.Loop.JoinedSquareTimeHomology
public import Finsler.Topology.FilteredTimePrismOperation
public import Finsler.Topology.JoinedSmallCapExtension
public import Finsler.Loop.CutTimeCommonComparison
public import Finsler.Loop.CylinderCommonCover
public import Finsler.Topology.AnnularDoubleCap
import all Finsler.Loop.FullSecondHalfStartTimeComparison

/-! The actual full second-half native bounded cap has the genuine
annular cut as its ambient chain image. Identify the small face and
retained output before passing to homology. -/

@[expose] public section
namespace Finsler.FullSecondHalfTrimmedTimeComparison

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

variable (d : ∀ q, (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X θ)).X
    ((m + 1) + (p + q)) ⟶ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).X q)
  (hd : ∀ q, d q ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
    (JoinedFilteredCap.sublevel F B))).f q =
    (inclusion (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X θ)).f ((m + 1) + (p + q)) ≫
      (push (JoinedFamilyNaturality.globalMap u a ha ha1 2)).f ((m + 1) + (p + q)) ≫
      eqToHom (congrArg (chains (parameters (m + 1))).X
        (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫ AnnularCutComparison.cut m p h hρr hr T hT q)


variable (hη : 0 < η) (hθ : 0 < θ)
  (hc : ∀ q, c (q + 1) ≫ (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded u hr F B))).d (q + 1) q =
    (small (TopCat.of (ClosedInterval × X)) (SecondHalfNativeFaceCapDomain.faceCover X η)).d
      ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)
  (hsource : ∀ q, c q ≫ (push (FullSecondHalfNativeLift.nativeSource u hr F B)).f q =
    (inclusion (TopCat.of (ClosedInterval × X)) (SecondHalfNativeFaceCapDomain.faceCover X η)).f ((m + 1) + (p + q)) ≫
      PartialDoubleCap.cap (TopCat.of (ClosedInterval × X)) (m + 1) p q
        (FullSecondHalfNativeTimeOperation.thom u (by omega) h) (FullSecondHalfNativeTimeOperation.tested u hr p T))
  (hdcomm : ∀ q, d (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q =
    (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X θ)).d
      ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ d q)
  (w : DegreeLoweringHomology.Map (chains (TopCat.of X))
    (chains (TopCat.of (SecondHalfZeroFaceGeometry.nativeBounded u hr F B))) (m + p))
  (hw : ∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
    ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of X) (SecondHalfNativeFaceCapDomain.faceCover X η)
        (FullSecondHalfAnnularInputs.faceCover_open X η) (FullSecondHalfAnnularInputs.faceCover_univ X η hη) _ m p c) q)

variable (k : DegreeLoweringHomology.Map (chains (TopCat.of X))
    (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p))
  (hk : ∀ q, k.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
    (push (planeFace (TopCat.of X) 1) ≫
      TauCeti.smallSingularRetraction (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X θ)
        (JoinedSimultaneousPrisms.rectangles_open X θ) (JoinedSimultaneousPrisms.rectangles_univ X θ hθ)).f
          ((m + p) + q + 1) ≫ ClosedCapDegreeTransport.align m p d q)
  (h₀ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
    (JoinedFamilyNaturality.globalMap u a ha ha1 2 ((s, 0), x)) ≤ δ)
  (h₁ : ∀ (s : ClosedInterval) (x : X), distance (m + 1)
    (JoinedFamilyNaturality.globalMap u a ha ha1 2 ((s, 1), x)) ≤ δ)

include hnative hd hc hsource hdcomm hw hk h₀ h₁ in
theorem homology_eq (q : ℕ) :
    (w.post (push (FullSecondHalfNativeTimeOperation.retainedOutput u hr F B))).homology q = k.homology q := by
  let E := chains (TopCat.of (JoinedFilteredCap.sublevel F B))
  let U := JoinedFilteredCap.rectangleCover X θ
  let g := JoinedFamilyNaturality.globalMap u a ha ha1 2
  let cap := ClosedCapDegreeTransport.align m p d
  have hcap (t : ℕ) : cap (t + 1) ≫ E.d (t + 1) t =
      (small (TopCat.of (Outer X)) U).d ((m + p) + t + 2) ((m + p) + t + 1) ≫ cap t :=
    ClosedCapDegreeTransport.align_comm m p d hdcomm t
  have hci (t : ℕ) : cap t ≫ (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
      (JoinedFilteredCap.sublevel F B))).f t =
      (inclusion (TopCat.of (Outer X)) U).f ((m + p) + t + 1) ≫ (push g).f ((m + p) + t + 1) ≫
        AnnularCutComparison.cut m p h hρr hr T hT t := by
    simpa only [HomologicalComplex.comp_f, Category.assoc] using
      ClosedCapDegreeTransport.align_inclusion m p d
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B)))
        (inclusion (TopCat.of (Outer X)) U ≫ push g)
        (fun t => AnnularCutComparison.cut m p h hρr hr T hT t)
        (fun t => by simpa only [HomologicalComplex.comp_f, Category.assoc] using hd t) t
  let D := JoinedSmallCapExtension.cap X θ hθ E (m + p) cap
  have hD := JoinedSmallCapExtension.cap_comm X θ hθ E (m + p) cap hcap
  have hDi := JoinedSmallCapExtension.cap_inclusion
    (P := parameters (m + 1)) (L := TopCat.of (SphereLoop (m + 1))) X θ hθ (m + p)
    (JoinedFilteredCap.sublevel F B) g (fun t => AnnularCutComparison.cut m p h hρr hr T hT t) cap hci
  have hRet : JoinedSimultaneousPrisms.retraction X θ hθ =
      TauCeti.smallSingularRetraction (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X θ)
        (JoinedSimultaneousPrisms.rectangles_open X θ) (JoinedSimultaneousPrisms.rectangles_univ X θ hθ) := rfl
  let v₀ := FilteredTimePrismOperation.operation m p h hρr hr T hT (TopCat.of X) (TopCat.of (Outer X))
    U g (JoinedFilteredCap.sublevel F B) D hDi (planeFace (TopCat.of X) 0) hD
      (fun x => h₀ 0 x) (fun x => h₁ 0 x)
  have hv₀ (t : ℕ) : v₀.component t = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + t) ≫
      (push (planeFace (TopCat.of X) 0) ≫
        TauCeti.smallSingularRetraction (X := TopCat.of (Outer X)) coeff U
          (JoinedSimultaneousPrisms.rectangles_open X θ) (JoinedSimultaneousPrisms.rectangles_univ X θ hθ)).f
            ((m + p) + t + 1) ≫ cap t := by
    change AnnularTimeTrim.prism (TopCat.of X) ((m + p) + t) ≫
      (push (planeFace (TopCat.of X) 0)).f ((m + p) + t + 1) ≫ D t = _
    simp only [D, JoinedSmallCapExtension.cap, hRet, U, cap, HomologicalComplex.comp_f, Category.assoc]
  have he := FullSecondHalfStartTimeComparison.homology_eq m p h hρr hr T hT F u η B hW c hnative
    a ha ha1 θ d hd hη hθ hc hsource hdcomm w hw v₀ hv₀ q
  apply he.trans
  apply JoinedSquareTimeHomology.homology_eq m p h hρr hr T hT (TopCat.of X) U g
    (JoinedFilteredCap.sublevel F B) D hDi hD h₀ h₁ v₀ k
  · intro t
    change AnnularTimeTrim.prism (TopCat.of X) ((m + p) + t) ≫
      (push (planeFace (TopCat.of X) 0)).f ((m + p) + t + 1) ≫ D t = _
    rfl
  · intro t
    rw [hk t]
    simp only [HomologicalComplex.comp_f, D, JoinedSmallCapExtension.cap, hRet, U, cap, Category.assoc]

end
end Finsler.FullSecondHalfTrimmedTimeComparison
