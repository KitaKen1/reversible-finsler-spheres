module

public import Finsler.Loop.FirstInputRotationNativeCaps
public import Finsler.Loop.CutTimeCommonComparison

/-! Actual original and rotating two-caps agree in the same bounded
proper cut domain on a common source cover. The equality follows from
literal source formulas and the proved local tested agreement. -/

@[expose] public section
namespace Finsler.FirstInputRotationNativeCapComparison

open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.SelfCutParameterFamily Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open Finsler.SmallChainCarrier Finsler.FirstInputRotationTimeTrim

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1600000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r₀ r₁ : ℝ)
  (hR : R ≤ 1 / 2) (hr₀ : r₀ < 1) (hr₁ : r₁ ≤ 1) (hr : r₁ ≤ r₀)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

local instance : CompactSpace (CompactNearJoinParameters.tube α β R) :=
  isCompact_iff_compactSpace.mp (CompactNearJoinParameters.compact α β R)

variable (F : ReversibleMetric n) (B η ζ : ℝ) (p : ℕ)
  (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p)
  (hn : 1 ≤ n) {δ ρ : ℝ} (h : 0 < δ ∧ δ ≤ 1 ∧ δ < ρ)


variable
  (hW : ∀ center,
    JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆
      JoinedRectangleRefinement.far (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le ρ 1 ∨
    JoinedFilteredCap.rectangleCover (CompactNearJoinParameters.tube α β R) η center ⊆
      domain (tube (CompactNearJoinParameters.tube α β R)) (family (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le) (fun _ => r₁) 1)
  (hgood : FirstInputRotationTestedCap.Adequate α β R r₀ hR hr₀ F B ζ p T)
  (hT : cochainCoboundary (ZMod 2) (TopCat.of (SphereLoop n)) p T = 0)
  (c : ∀ q, (small (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).X (n + (p + q)) ⟶ ((chains (FirstHalfBoundedCapDeformation.boundedCut (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B))).X q)
  (hi : ∀ q, c q ≫ (push (FirstHalfAnnularTimeInputs.projection (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B)).f q =
    (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) ≫ PartialDoubleCap.cap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) n p q
      (FirstHalfAnnularTimeDomain.thom (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hn h)
      (FirstHalfAnnularTimeDomain.tested (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ p T))

include hW hi in
theorem on_common (q : ℕ) :
    (CylinderCommonCover.toSource (X := (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))) (Y := FirstInputRotationCutCylinder.cylinder α β R) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) (FirstInputRotationCutCylinder.cover α β R r₀ ζ ρ) (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)).f
      (n + (p + q)) ≫ c q ≫ ((push (FirstInputRotationNativeBounded.boundedMap α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B))).f q =
    (CylinderCommonCover.toTarget (X := (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))) (Y := FirstInputRotationCutCylinder.cylinder α β R) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) (FirstInputRotationCutCylinder.cover α β R r₀ ζ ρ) (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)).f
      (n + (p + q)) ≫ FirstInputRotationTimeCap.component α β R r₀ hR hr₀ p T hn h F B ζ hgood hT q := by
  let Ms := CylinderCommonCover.toSource (X := (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))) (Y := FirstInputRotationCutCylinder.cylinder α β R) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) (FirstInputRotationCutCylinder.cover α β R r₀ ζ ρ) (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)
  let Mt := CylinderCommonCover.toTarget (X := (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))) (Y := FirstInputRotationCutCylinder.cylinder α β R) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) (FirstInputRotationCutCylinder.cover α β R r₀ ζ ρ) (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)
  let W := CylinderCommonCover.cover (X := (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))) (Y := FirstInputRotationCutCylinder.cylinder α β R) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) (FirstInputRotationCutCylinder.cover α β R r₀ ζ ρ) (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)
  let b := push (FirstInputRotationTimeCap.source α β R r₀ hR hr₀ F B)
  let b₀ := push (FirstHalfAnnularTimeInputs.projection (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ F B)
  haveI : Mono (b.f q) := FirstInputRotationTimeCap.source_mono α β R r₀ hR hr₀ F B q
  apply (cancel_mono (b.f q)).mp
  have hs := congrArg (fun g => (push g).f q)
    (FirstInputRotationNativeBounded.source_square α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B)
  simp only [push_comp, HomologicalComplex.comp_f] at hs
  have hs' : ((push (FirstInputRotationNativeBounded.boundedMap α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B))).f q ≫ b.f q = b₀.f q ≫ (push (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)).f q := by
    simpa only [b, b₀, push_comp, HomologicalComplex.comp_f, Category.assoc] using hs
  have hMs : Ms.f (n + (p + q)) ≫ (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) =
      (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) W).f (n + (p + q)) := congrArg (fun g => g.f (n + (p + q)))
        (CylinderCommonCover.toSource_inclusion (X := (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)))
          (Y := FirstInputRotationCutCylinder.cylinder α β R) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) (FirstInputRotationCutCylinder.cover α β R r₀ ζ ρ) (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1))
  have hMt : Mt.f (n + (p + q)) ≫
      (inclusion (FirstInputRotationCutCylinder.cylinder α β R) (FirstInputRotationCutCylinder.cover α β R r₀ ζ ρ)).f (n + (p + q)) =
      (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) W).f (n + (p + q)) ≫ (push (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)).f (n + (p + q)) :=
    congrArg (fun g => g.f (n + (p + q)))
      (CylinderCommonCover.toTarget_inclusion (X := (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)))
        (Y := FirstInputRotationCutCylinder.cylinder α β R) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η) (FirstInputRotationCutCylinder.cover α β R r₀ ζ ρ) (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1))
  have hcap := FirstInputRotationNativeCaps.cap_agreement α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 η hn h hW p T q
  have hncap := PartialDoubleCap.cap_natural (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) n p q
    (FirstInputRotationCutCylinder.thom α β R hR hn h)
    (FirstInputRotationCutCylinder.tested α β R r₀ hR hr₀ p T)
  change (Ms.f (n + (p + q)) ≫ c q ≫ ((push (FirstInputRotationNativeBounded.boundedMap α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1 F B))).f q) ≫ b.f q =
    (Mt.f (n + (p + q)) ≫ FirstInputRotationTimeCap.component α β R r₀ hR hr₀ p T hn h F B ζ hgood hT q) ≫ b.f q
  calc
    _ = Ms.f (n + (p + q)) ≫ (c q ≫ b₀.f q) ≫ (push (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)).f q := by
      simp only [Category.assoc]
      rw [hs']
    _ = Ms.f (n + (p + q)) ≫
        ((inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) ≫ PartialDoubleCap.cap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) n p q
          (FirstHalfAnnularTimeDomain.thom (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hn h)
          (FirstHalfAnnularTimeDomain.tested (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ p T)) ≫ (push (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)).f q := by rw [hi]
    _ = Ms.f (n + (p + q)) ≫
        ((inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) ≫ PartialDoubleCap.cap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) n p q
          (cochainPullback (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) n (FirstInputRotationCutCylinder.thom α β R hR hn h))
          (cochainPullback (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) p (FirstInputRotationCutCylinder.tested α β R r₀ hR hr₀ p T))) ≫ (push (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)).f q := by rw [hcap]
    _ = ((Ms.f (n + (p + q)) ≫ (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q))) ≫
        (push (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1)).f (n + (p + q))) ≫ PartialDoubleCap.cap (FirstInputRotationCutCylinder.cylinder α β R) n p q
          (FirstInputRotationCutCylinder.thom α β R hR hn h)
          (FirstInputRotationCutCylinder.tested α β R r₀ hR hr₀ p T) := by
      simpa only [Category.assoc] using congrArg
        (fun g => Ms.f (n + (p + q)) ≫ (inclusion (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R)) (FirstHalfInteriorCapDomain.faceCover (CompactNearJoinParameters.tube α β R) η)).f (n + (p + q)) ≫ g) hncap
    _ = (Mt.f (n + (p + q)) ≫
        (inclusion (FirstInputRotationCutCylinder.cylinder α β R) (FirstInputRotationCutCylinder.cover α β R r₀ ζ ρ)).f (n + (p + q))) ≫
        PartialDoubleCap.cap (FirstInputRotationCutCylinder.cylinder α β R) n p q
          (FirstInputRotationCutCylinder.thom α β R hR hn h)
          (FirstInputRotationCutCylinder.tested α β R r₀ hR hr₀ p T) := by rw [hMs, hMt]
    _ = _ := by
      simp only [b, Category.assoc]
      rw [FirstInputRotationTimeCap.component_source]

end
end Finsler.FirstInputRotationNativeCapComparison
