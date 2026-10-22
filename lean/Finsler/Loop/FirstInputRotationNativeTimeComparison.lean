module

public import Finsler.Loop.FirstInputRotationNativeCapComparison
public import Finsler.Loop.FirstInputRotationTrimmedCutEndpoints

/-! Compare the actual original first-half time operation with the
trimmed rotation-one model inside the identical bounded cut target.
The relative common-cover comparison retains all endpoint terms and
the genuine source-before-map versus target-after-map retractions. -/

@[expose] public section
namespace Finsler.FirstInputRotationNativeTimeComparison

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.SelfCutParameterFamily Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open Finsler.SmallChainCarrier Finsler.FirstInputRotationTimeTrim Finsler.FirstInputRotationCutCylinder

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {m : ℕ}
  (α : C(P, SphereLoop (m + 1))) (β : C(Q, SphereLoop (m + 1))) (R r₀ r₁ : ℝ)
  (hR : R ≤ 1 / 2) (hr₀ : r₀ < 1) (hr₁ : r₁ ≤ 1) (hr : r₁ ≤ r₀)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

local instance : CompactSpace (CompactNearJoinParameters.tube α β R) :=
  isCompact_iff_compactSpace.mp (CompactNearJoinParameters.compact α β R)

theorem distance_eq (z : ClosedInterval × CompactNearJoinParameters.tube α β R) :
    distance (m + 1) (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) a ha.le ha1.le z) =
      distance (m + 1) (InteriorTimeSlide.trimTime a ha.le ha1.le z.1, α z.2.val.1) := by
  rw [FirstHalfInteriorPrism.distance_trimmed
    (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 z]
  have hd := FirstInputRotationFamily.time_distance α β R (hR.trans_lt (by norm_num))
    (InteriorTimeSlide.trimTime a ha.le ha1.le z.1) 1 z.2
  change distance (m + 1) (InteriorTimeSlide.trimTime a ha.le ha1.le z.1,
    FirstInputRotationFamily.family α β R (hR.trans_lt (by norm_num)) (1, z.2)) = _ at hd
  rw [FirstInputRotationFamily.family_one] at hd
  exact hd

theorem endpoint_collar {δ : ℝ} (t : ClosedInterval)
    (hs : ∀ s x, sideHomotopy α β R a ha ha1 t (s, x) ∈ collar α β R δ)
    (x : CompactNearJoinParameters.tube α β R) :
    distance (m + 1) (CylinderTimeTrim.trimmedMap (JoinedHalfCollars.firstFamily (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num)))) a ha.le ha1.le (t, x)) ≤ δ := by
  rw [distance_eq α β R hR a ha ha1]
  exact trim_endpoint_collar α β R a ha ha1 t hs (1, x)

variable (F : ReversibleMetric (m + 1)) (B η ζ : ℝ) (hη : 0 < η) (hζ : 0 < ζ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p)
  {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ) (hρr₀ : ρ < r₀)
  (hzero : ∀ s x, sideHomotopy α β R a ha ha1 0 (s, x) ∈ collar α β R δ)
  (hone : ∀ s x, sideHomotopy α β R a ha ha1 1 (s, x) ∈ collar α β R δ)
  (hW : ∀ center,
    JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆
      JoinedRectangleRefinement.far (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le ρ 1 ∨
    JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆
      domain (tube (CompactNearJoinParameters.tube α β R)) (family (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le) (fun _ => r₁) 1)
  (hgood : FirstInputRotationTestedCap.Adequate α β R r₀ hR hr₀ F B ζ p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop (m + 1))) p T = 0)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X ((m + 1) + (p + q)) ⟶ (chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B)).X q)
  (hc : ∀ q, c (q + 1) ≫ (chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B)).d (q + 1) q =
    (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).d ((m + 1) + (p + (q + 1))) ((m + 1) + (p + q)) ≫ c q)
  (hi : ∀ q, c q ≫ (push (FirstHalfAnnularTimeInputs.projection (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B)).f q =
    (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f ((m + 1) + (p + q)) ≫ PartialDoubleCap.cap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (m + 1) p q
      (FirstHalfAnnularTimeDomain.thom (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 (by omega) h)
      (FirstHalfAnnularTimeDomain.tested (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ p T))
  (w : DegreeLoweringHomology.Map (chains (TopCat.of (CompactNearJoinParameters.tube α β R))) (chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B)) (m + p))
  (hw : ∀ q, w.component q = AnnularTimeTrim.prism (TopCat.of (CompactNearJoinParameters.tube α β R)) ((m + p) + q) ≫
    ClosedCapDegreeTransport.align m p
      (CutDomainTimePrism.retracted (TopCat.of (CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)
        (FirstHalfAnnularTimeInputs.faceCover_open (CompactNearJoinParameters.tube α β R) η)
        (FirstHalfAnnularTimeInputs.faceCover_univ (CompactNearJoinParameters.tube α β R) η hη)
        (chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B)) m p c) q)

include hc hi hW hw in
theorem cut_homology_eq (q : ℕ) :
    (w.post (push (FirstInputRotationNativeBounded.boundedMap α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B))).homology q =
      (FirstInputRotationTrimmedCutEndpoints.endpoint α β R r₀ hR hr₀ p T h F B ζ hζ hρr₀ hgood hT
        a ha ha1 hzero hone 1).homology q := by
  apply CutTimeCommonComparison.homology_eq (TopCat.of (CompactNearJoinParameters.tube α β R)) (cylinder α β R) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) (cover α β R r₀ ζ ρ)
    (FirstHalfAnnularTimeInputs.faceCover_open (CompactNearJoinParameters.tube α β R) η)
    (FirstHalfAnnularTimeInputs.faceCover_univ (CompactNearJoinParameters.tube α β R) η hη)
    (cover_open α β R r₀ ζ ρ) (cover_univ α β R r₀ ζ hζ hρr₀) (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)
    (chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B)) (chains (FirstInputRotationTimeCap.target α β R r₀ hR hr₀ F B)) (push (FirstInputRotationNativeBounded.boundedMap α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B))
    m p c hc (FirstHalfAnnularTimeInputs.collar (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 δ)
    (FirstHalfAnnularTimeDomain.thom (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 (by omega) h)
    (FirstHalfAnnularTimeDomain.tested (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ p T)
    (FirstHalfAnnularTimeInputs.annular_inner_zero (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 (by omega) h)
    (push (FirstHalfAnnularTimeInputs.projection (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B)) (FirstHalfAnnularTimeInputs.projection_mono (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B) hi
    (endpoint_collar α β R hR a ha ha1 0 hzero) (endpoint_collar α β R hR a ha ha1 1 hone)
    (FirstInputRotationTimeCap.component α β R r₀ hR hr₀ p T (by omega) h F B ζ hgood hT)
    (FirstInputRotationTimeCap.component_comm α β R r₀ hR hr₀ p T (by omega) h F B ζ hgood hT)
    (FirstInputRotationNativeCapComparison.on_common α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B η ζ p T
      (by omega) h hW hgood hT c hi) w hw
    (FirstInputRotationTrimmedCutEndpoints.endpoint α β R r₀ hR hr₀ p T h F B ζ hζ hρr₀ hgood hT
      a ha ha1 hzero hone 1)
    (FirstInputRotationTrimmedCutEndpoints.component_normal α β R r₀ hR hr₀ p T h F B ζ hζ hρr₀ hgood hT
      a ha ha1 hzero hone 1) q

include hr hc hi hW hw in
theorem retained_homology_eq (q : ℕ) :
    (w.post (push (FirstHalfBoundedCapDeformation.retained (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B))).homology q =
      (FirstInputRotationTrimmedEndpoints.endpoint α β R r₀ hR hr₀ p T h F B ζ hζ hρr₀ hgood hT
        a ha ha1 hzero hone 1).homology q := by
  have he := cut_homology_eq α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B η ζ hη hζ p T h hρr₀
    hzero hone hW hgood hT c hc hi w hw q
  have hs := congrArg (fun g => HomologicalComplex.homologyMap (push g) q)
    (FirstInputRotationNativeBounded.retained_square α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B)
  rw [push_comp, HomologicalComplex.homologyMap_comp] at hs
  rw [FirstHalfAnnularTimeDomain.post_homology_eq (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B w q]
  rw [DegreeLoweringHomology.Map.post_homology, ← hs, ← Category.assoc]
  have hc' := congrArg (fun g => g ≫ HomologicalComplex.homologyMap
    (push (FirstInputRotationFilteredCap.retained α β R r₀ hR hr₀ F B)) q) he
  rw [DegreeLoweringHomology.Map.post_homology] at hc'
  rw [hc']
  simpa only [DegreeLoweringHomology.Map.post_homology] using
    (FirstInputRotationTrimmedCutEndpoints.retained_homology α β R r₀ hR hr₀ p T h F B ζ hζ hρr₀ hgood hT
      a ha ha1 hzero hone 1 q)

end
end Finsler.FirstInputRotationNativeTimeComparison
