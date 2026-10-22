module

public import Finsler.Topology.FirstHalfRefinedCapAgreement
public import Finsler.Topology.NestedCapRefinement
public import Finsler.Topology.RetainedTimeAlignment
public import Finsler.Topology.PrismRefinementHomology

/-! Keep the actual outer time model and its cap scale fixed. A common
finer source cover supplies a genuine cut-domain time operation whose
original and fixed-output deformed retained operations agree with that
outer model inside the same retained-length target. -/

@[expose] public section
namespace Finsler.FirstHalfRefinedTimeAgreement

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 900000

theorem exists_operation_and_eq {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (m p : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
    (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
    (F : ReversibleMetric (m + 1)) (u : C(X, H1JoinContinuity.composable (m + 1)))
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2) (η η₀ η₁ B : ℝ) (hη : 0 < η)
    (hle₀ : η ≤ η₀) (hle₁ : η ≤ η₁)
    (h₀ : ∀ x, distance (m + 1)
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (0, x)) ≤ δ)
    (h₁ : ∀ x, distance (m + 1)
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (1, x)) ≤ δ)
    (hW : ∀ center, JoinedFilteredCap.rectangleCover X η₁ center ⊆ JoinedRectangleRefinement.far u a ha.le ha1.le ρ 1 ∨
      JoinedFilteredCap.rectangleCover X η₁ center ⊆ domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
    (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η₁)).X
      ((m + 1) + (p + q)) ⟶ (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)).X q)
    (hc : ∀ q, c (q + 1) ≫ (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)).d (q + 1) q =
      (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η₁)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)
    (hi : ∀ q, c q ≫ (push (FirstHalfAnnularTimeInputs.projection u a ha ha1 hr F B)).f q =
      (inclusion (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η₁)).f ((m + 1) + (p + q)) ≫
        PartialDoubleCap.cap (TopCat.of (ClosedInterval × X)) (m + 1) p q
          (FirstHalfAnnularTimeDomain.thom u a ha ha1 (by omega) h) (FirstHalfAnnularTimeDomain.tested u a ha ha1 hr p T))
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
            (show (m + 1) + (p + q) = (m + p) + q + 1 by omega)) ≫ AnnularCutComparison.cut m p h hρr hr T hT q)
    (hdcomm : ∀ q, d (q + 1) ≫ (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).d (q + 1) q =
      (small (TopCat.of (Outer X)) (JoinedFilteredCap.rectangleCover X η₀)).d
        ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ d q)
    (v : DegreeLoweringHomology.Map (chains (TopCat.of X))
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p))
    (hv : ∀ q, v.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
      (push (planeFace (TopCat.of X) 1) ≫
        TauCeti.smallSingularRetraction (X := TopCat.of (Outer X)) coeff (JoinedFilteredCap.rectangleCover X η₀)
          (JoinedSimultaneousPrisms.rectangles_open X η₀)
          (JoinedSimultaneousPrisms.rectangles_univ X η₀ (hη.trans_le hle₀))).f ((m + p) + q + 1) ≫
            ClosedCapDegreeTransport.align m p d q) :
    ∃ w : DegreeLoweringHomology.Map (chains (TopCat.of X))
      (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) (m + p),
      (∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
        ClosedCapDegreeTransport.align m p
          (CutDomainTimePrism.retracted (TopCat.of X) (FirstHalfInteriorCapDomain.faceCover X η)
            (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
            (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) m p
            (NestedCapRefinement.pre (m + 1) p (FirstHalfFaceRefinement.map X hle₁) c)) q) ∧
      (∀ q, v.homology q = (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))).homology q) ∧
      (∀ q, v.homology q = (w.post (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F B 1))).homology q) := by
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let U := FirstHalfInteriorCapDomain.faceCover X η
  let U₁ := FirstHalfInteriorCapDomain.faceCover X η₁
  let V := JoinedFilteredCap.rectangleCover X η₀
  let E := chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)
  let j := push (FirstHalfAnnularTimeInputs.projection u a ha ha1 hr F B)
  let M := FirstHalfFaceRefinement.map X hle₁
  let R := TauCeti.smallSingularRetraction (X := TopCat.of (ClosedInterval × (TopCat.of X))) coeff U
    (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
  let c' := NestedCapRefinement.pre (m + 1) p M c
  have hc' := NestedCapRefinement.pre_comm (m + 1) p M c hc
  have hi' := NestedCapRefinement.pre_inclusion C U₁ U M (FirstHalfFaceRefinement.map_inclusion X hle₁)
    E j (m + 1) p (FirstHalfAnnularTimeDomain.thom u a ha ha1 (by omega) h)
    (FirstHalfAnnularTimeDomain.tested u a ha ha1 hr p T) c hi
  let w : DegreeLoweringHomology.Map (chains (TopCat.of X)) E (m + p) :=
    CutDomainTimePrism.operation (TopCat.of X) U
      (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
      E m p c' (FirstHalfAnnularTimeInputs.collar u a ha ha1 δ)
      (FirstHalfAnnularTimeDomain.thom u a ha ha1 (by omega) h) (FirstHalfAnnularTimeDomain.tested u a ha ha1 hr p T)
      (FirstHalfAnnularTimeInputs.annular_inner_zero u a ha ha1 (by omega) h) j
      (FirstHalfAnnularTimeInputs.projection_mono u a ha ha1 hr F B) hi' hc' h₀ h₁
  have hcap (q : ℕ) : c' q ≫ (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B)).f q =
      (FirstHalfFaceRefinement.toOuter X hle₀).f ((m + 1) + (p + q)) ≫ d q := by
    simpa only [c', M, NestedCapRefinement.pre, Category.assoc] using
      FirstHalfRefinedCapAgreement.agreement m p h hρr hr T hT F u a ha ha1 η η₀ η₁ B hle₀ hle₁ hW c hnative d hd q
  have hm (q : ℕ) : (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))).component q =
      AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
        (R ≫ FirstHalfFaceRefinement.toOuter X hle₀).f ((m + p) + q + 1) ≫
          ClosedCapDegreeTransport.align m p d q := by
    have hh := RetainedTimeAlignment.agreement R (FirstHalfFaceRefinement.toOuter X hle₀)
      (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B)) m p c' d hcap q
    change (AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
      ClosedCapDegreeTransport.align m p (CutDomainTimePrism.retracted (TopCat.of X) U
        (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη) E m p c') q) ≫ _ = _
    have hR : CutDomainTimePrism.retracted (TopCat.of X) U
        (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη) E m p c' =
        (fun s => R.f ((m + 1) + (p + s)) ≫ c' s) := rfl
    rw [hR]
    simpa only [Category.assoc] using
      congrArg (fun z => AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫ z) hh
  have heq (q : ℕ) : v.homology q =
      (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))).homology q := by
    exact PrismRefinementHomology.homology_eq (TopCat.of X) (TopCat.of (Outer X)) U V
      (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
      (JoinedSimultaneousPrisms.rectangles_open X η₀) (JoinedSimultaneousPrisms.rectangles_univ X η₀ (hη.trans_le hle₀))
      (planeFace (TopCat.of X) 1) id (fun center z hz => JoinedRectangleRefinement.rectangleCover_mono hle₀ center hz)
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))) (m + p)
      (ClosedCapDegreeTransport.align m p d) (ClosedCapDegreeTransport.align_comm m p d hdcomm)
      v (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))) hv hm q
  refine ⟨w, ?_, heq, ?_⟩
  · intro q
    rfl
  · intro q
    exact (heq q).trans (FirstHalfAnnularTimeDomain.post_homology_eq u a ha ha1 hr F B w q)

end
end Finsler.FirstHalfRefinedTimeAgreement
