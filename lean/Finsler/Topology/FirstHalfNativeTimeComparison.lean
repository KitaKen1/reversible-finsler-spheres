module

public import Finsler.Topology.FirstHalfNativeTimeFactors
public import Finsler.Topology.FilteredModelNativeComparison

/-! The actual cut-domain-valued first-half time model has precisely the
original native annular time operation as its ordinary ambient image.
The original and length-preserving deformed retained models stay in the
same genuine length sublevel; no target homology injectivity is used. -/

@[expose] public section
namespace Finsler.FirstHalfNativeTimeComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
open Finsler.SupportedCapNaturality Finsler.SobolevLength Finsler.SelfCutParameterFamily
open Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

variable {X : Type} [PseudoMetricSpace X] [CompactSpace X]
  (m p : ℕ) {δ ρ r : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr : ρ < r) (hr : r ≤ 1)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (F : ReversibleMetric (m + 1)) (u : C(X, H1JoinContinuity.composable (m + 1)))
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2) (η : ℝ) (hη : 0 < η) (B : ℝ)
  (hW : ∀ center, JoinedFilteredCap.rectangleCover X η center ⊆ JoinedRectangleRefinement.far u a ha.le ha1.le ρ 1 ∨
    JoinedFilteredCap.rectangleCover X η center ⊆ domain (tube X) (family u a ha.le ha1.le) (fun _ => r) 1)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × X)) (FirstHalfInteriorCapDomain.faceCover X η)).X
    ((m + 1) + (p + q)) ⟶ (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)).X q)
  (hnative : ∀ q, (FirstHalfInteriorCapDomain.faceMap X η ≫
    JoinedLocalizedCutComparison.familySmallMap u a ha.le ha1.le ρ r 1 (JoinedFilteredCap.rectangleCover X η) hW).f
      ((m + 1) + (p + q)) ≫
    SupportedDoubleCap.localized (parameters (m + 1)) (exterior (m + 1) ρ) (neighborhood (m + 1) r)
      (m + 1) p (AnnularSelfCut.cocycle (m + 1) (by omega) h)
      (AnnularSupportedCut.cocycle_supported (m + 1) (by omega) h)
      (NormalizedSelfCut.testedCocycle (m + 1) p hr T) q ((m + 1) + (p + q)) rfl =
        c q ≫ (push (FirstHalfNativeCapDeformation.nativeCut u a ha ha1 hr F B)).f q)

include hnative

theorem retracted_inclusion (q : ℕ) :
    ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of X) (FirstHalfInteriorCapDomain.faceCover X η)
        (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
        (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) m p c) q ≫
      (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B)).f q ≫
        (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))).f q =
    (TauCeti.singularSmallApprox (X := TopCat.of (ClosedInterval × X)) coeff
      (FirstHalfInteriorCapDomain.faceCover X η)).f ((m + p) + q + 1) ≫
        (push (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le)).f ((m + p) + q + 1) ≫
          AnnularCutComparison.cut m p h hρr hr T hT q := by
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let U := FirstHalfInteriorCapDomain.faceCover X η
  let R := TauCeti.smallSingularRetraction (X := C) coeff U
    (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
  let g := CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le
  let j := push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B) ≫
    push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1))) (JoinedFilteredCap.sublevel F B))
  have hi (s : ℕ) : CutDomainTimePrism.retracted (TopCat.of X) U
      (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
      (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) m p c s ≫ j.f s =
    (TauCeti.singularSmallApprox (X := C) coeff U ≫ push g).f ((m + 1) + (p + s)) ≫
      eqToHom (congrArg (chains (parameters (m + 1))).X
        (show (m + 1) + (p + s) = (m + p) + s + 1 by omega)) ≫
          AnnularCutComparison.cut m p h hρr hr T hT s := by
    have hs := FirstHalfNativeTimeFactors.cap_inclusion m p h hρr hr T hT F u a ha ha1 η B hW c hnative s
    have hR : R.f ((m + 1) + (p + s)) ≫ (inclusion C U).f ((m + 1) + (p + s)) =
        (TauCeti.singularSmallApprox (X := C) coeff U).f ((m + 1) + (p + s)) := by
      simpa only [HomologicalComplex.comp_f] using congrArg (fun z => z.f ((m + 1) + (p + s)))
        (TauCeti.smallSingularRetraction_comp_ι (X := C) coeff U
          (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη))
    dsimp only [CutDomainTimePrism.retracted, j]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [hs]
    simpa only [C, U, R, g, ← Category.assoc] using congrArg
      (fun z => z ≫ (push g).f ((m + 1) + (p + s)) ≫
        eqToHom (congrArg (chains (parameters (m + 1))).X
          (show (m + 1) + (p + s) = (m + p) + s + 1 by omega)) ≫
            AnnularCutComparison.cut m p h hρr hr T hT s) hR
  have hh := ClosedCapDegreeTransport.align_inclusion m p
    (CutDomainTimePrism.retracted (TopCat.of X) U
      (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
      (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) m p c) j
    (TauCeti.singularSmallApprox (X := C) coeff U ≫ push g)
    (fun s => AnnularCutComparison.cut m p h hρr hr T hT s) hi q
  simpa only [j, HomologicalComplex.comp_f, Category.assoc] using hh

variable
  (h₀ : ∀ x, distance (m + 1)
    (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (0, x)) ≤ δ)
  (h₁ : ∀ x, distance (m + 1)
    (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le (1, x)) ≤ δ)
  (w : DegreeLoweringHomology.Map (chains (TopCat.of X))
    (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) (m + p))
  (hw : ∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of X) ((m + p) + q) ≫
    ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of X) (FirstHalfInteriorCapDomain.faceCover X η)
        (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
        (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) m p c) q)

include hw h₀ h₁

theorem native_inclusion (q : ℕ) :
    (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))).homology q ≫
      HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (JoinedFilteredCap.sublevel F B))) q =
    (AnnularTrimHomology.operation (X := TopCat.of X) m p h hρr hr T hT
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) h₀ h₁).homology q := by
  let C : TopCat.{0} := TopCat.of (ClosedInterval × X)
  let U := FirstHalfInteriorCapDomain.faceCover X η
  let g := CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le
  let v : ∀ q, (chains C).X ((m + p) + q + 1) ⟶
      (chains (TopCat.of (JoinedFilteredCap.sublevel F B))).X q := fun q => ClosedCapDegreeTransport.align m p
    (CutDomainTimePrism.retracted (TopCat.of X) U
      (FirstHalfAnnularTimeInputs.faceCover_open X η) (FirstHalfAnnularTimeInputs.faceCover_univ X η hη)
      (chains (FirstHalfBoundedCapDeformation.boundedCut u a ha ha1 hr F B)) m p c) q ≫
    (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B)).f q
  have hv := retracted_inclusion m p h hρr hr T hT F u a ha ha1 η hη B hW c hnative
  have hid : push (𝟙 C) = 𝟙 (chains C) := by
    change ((SSet.chainComplexFunctor.{0} (ModuleCat.{0} (ZMod 2))).obj coeff).map (TopCat.toSSet.map (𝟙 C)) = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have hm (s : ℕ) : (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))).component s =
      AnnularTimeTrim.prism (TopCat.of X) ((m + p) + s) ≫ (push (𝟙 C)).f ((m + p) + s + 1) ≫ v s := by
    simp only [DegreeLoweringHomology.Map.post, hw, hid, HomologicalComplex.id_f, v, C, U, Category.id_comp, Category.assoc]
  exact FilteredModelNativeComparison.identified_inclusion m p h hρr hr T hT
    (TopCat.of X) C U g (𝟙 C) h₀ h₁ (JoinedFilteredCap.sublevel F B) v
    (fun s => by simpa only [v, C, U, Category.assoc] using hv s)
    (w.post (push (FirstHalfBoundedCapDeformation.retained u a ha ha1 hr F B))) hm
    g (Category.id_comp g) h₀ h₁ q

theorem deformed_native_inclusion (q : ℕ) :
    (w.post (push (FirstHalfBoundedCapDeformation.endpoint u a ha ha1 hr F B 1))).homology q ≫
      HomologicalComplex.homologyMap (push (SupportedCap.subspaceMap (TopCat.of (SphereLoop (m + 1)))
        (JoinedFilteredCap.sublevel F B))) q =
    (AnnularTrimHomology.operation (X := TopCat.of X) m p h hρr hr T hT
      (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily u) a ha.le ha1.le) h₀ h₁).homology q := by
  rw [← FirstHalfAnnularTimeDomain.post_homology_eq u a ha ha1 hr F B w q]
  exact native_inclusion m p h hρr hr T hT F u a ha ha1 η hη B hW c hnative h₀ h₁ w hw q

end
end Finsler.FirstHalfNativeTimeComparison
