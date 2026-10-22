module

public import Finsler.Loop.FirstInputRotationNativeBounded
public import Finsler.Loop.FirstInputRotationTrimmedThom

/-! Compare the actual two different tested zero extensions on the
original first-half face domain. Their restrictions agree through the
actual tested loop, without equating the extensions on the full cylinder. -/

@[expose] public section
namespace Finsler.FirstInputRotationNativeTested

open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.CochainComparison
open Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut Finsler.SupportedCapNaturality
open Finsler.SelfCutParameterFamily Finsler.JoinedComparisonAdequacy Finsler.JoinedRefinedComparisons
open Finsler.FirstInputRotationTimeTrim

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {P Q : Type} [PseudoMetricSpace P] [PseudoMetricSpace Q]
  [CompactSpace P] [CompactSpace Q] {n : ℕ}
  (α : C(P, SphereLoop n)) (β : C(Q, SphereLoop n)) (R r₀ r₁ : ℝ)
  (hR : R ≤ 1 / 2) (hr₀ : r₀ < 1) (hr₁ : r₁ ≤ 1) (hr : r₁ ≤ r₀)
  (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)

local instance : CompactSpace (CompactNearJoinParameters.tube α β R) :=
  isCompact_iff_compactSpace.mp (CompactNearJoinParameters.compact α β R)

abbrev faceDomain : Set (ClosedInterval × CompactNearJoinParameters.tube α β R) :=
  (planeFace (TopCat.of (CompactNearJoinParameters.tube α β R)) 1) ⁻¹'
    domain (tube (CompactNearJoinParameters.tube α β R))
      (family (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha.le ha1.le)
        (fun _ => r₁) 1

def intoRotation : TopCat.of (faceDomain α β R r₁ hR a ha ha1) ⟶
    FirstInputRotationCochains.space α β R r₀ :=
  FirstHalfInteriorFaceDomain.toInterior
    (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 r₁ ≫
      FirstInputRotationNativeDomain.intoRotation α β R r₀ r₁ hR hr a ha ha1

theorem source_square :
    SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
      (faceDomain α β R r₁ hR a ha ha1) ≫
      (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) ≫
        FirstInputRotationCutCylinder.reorder α β R =
      intoRotation α β R r₀ r₁ hR hr a ha ha1 ≫ FirstInputRotationAmbientCover.source α β R r₀ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  rfl

include hr in
theorem new_restriction (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback
      (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (faceDomain α β R r₁ hR a ha ha1)) p
      (cochainPullback (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) p
        (FirstInputRotationCutCylinder.tested α β R r₀ hR hr₀ p T)) =
      cochainPullback
        (FirstHalfInteriorFaceDomain.toInterior
          (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 r₁ ≫
          FirstHalfInteriorTested.sourceMap
            (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁) p T := by
  have hs := source_square α β R r₀ r₁ hR hr a ha ha1
  simp only [Category.assoc] at hs
  rw [FirstInputRotationCutCylinder.tested, ← pullback_comp, ← pullback_comp]
  simp only [Category.assoc]
  rw [hs, pullback_comp,
    FirstInputRotationAmbientCap.tested_restriction, intoRotation, pullback_comp,
    FirstInputRotationNativeDomain.tested_cochain α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1,
    ← pullback_comp]

theorem old_restriction (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback
      (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (faceDomain α β R r₁ hR a ha ha1)) p
      (FirstHalfAnnularTimeDomain.tested
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ p T) =
      cochainPullback
        (FirstHalfInteriorFaceDomain.toInterior
          (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 r₁ ≫
          FirstHalfInteriorTested.sourceMap
            (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁) p T := by
  let X := CompactNearJoinParameters.tube α β R
  let u := CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))
  let D := domain (tube X) (family u a ha.le ha1.le) (fun _ => r₁) 1
  let f := planeFace (TopCat.of X) 1
  let M := DoubleCapEmbeddingPullback.domainMap f D
  have hs : SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) (f ⁻¹' D) ≫ f =
      M ≫ SupportedCap.subspaceMap (TopCat.of (Outer X)) D :=
    by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro z
      rfl
  have ht : M ≫ testedMap (tube X) (family u a ha.le ha1.le) (fun _ => r₁) (fun _ => hr₁) 1 =
      FirstHalfInteriorFaceDomain.toInterior u a ha ha1 r₁ ≫
        FirstHalfInteriorTested.sourceMap u a ha ha1 hr₁ := by
    rw [testedMap, ← Category.assoc, FirstHalfInteriorFaceDomain.toCut_native,
      Category.assoc, FirstHalfInteriorNative.tested_native]
  change cochainPullback (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × X)) (f ⁻¹' D)) p
    (cochainPullback f p
      (TubeCochainExtension.extend (TopCat.of (Outer X)) D p
        (cochainPullback (testedMap (tube X) (family u a ha.le ha1.le)
          (fun _ => r₁) (fun _ => hr₁) 1) p T))) = _
  rw [← pullback_comp, hs, pullback_comp, TubeCochainExtension.restriction,
    ← pullback_comp, ht]

include hr in
theorem agreement (p : ℕ)
    (T : singularCochainGroup (ZMod 2) (TopCat.of (SphereLoop n)) p) :
    cochainPullback
      (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (faceDomain α β R r₁ hR a ha ha1)) p
      (FirstHalfAnnularTimeDomain.tested
        (CompactNearJoinParameters.inputs α β R (hR.trans_lt (by norm_num))) a ha ha1 hr₁ p T) =
    cochainPullback
      (SupportedCap.subspaceMap (TopCat.of (ClosedInterval × CompactNearJoinParameters.tube α β R))
        (faceDomain α β R r₁ hR a ha ha1)) p
      (cochainPullback (rotationSlice α β R 1 ≫ trimMap α β R a ha ha1) p
        (FirstInputRotationCutCylinder.tested α β R r₀ hR hr₀ p T)) := by
  rw [old_restriction, new_restriction α β R r₀ r₁ hR hr₀ hr₁ hr a ha ha1]

end
end Finsler.FirstInputRotationNativeTested
