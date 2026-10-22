module

public import Finsler.Loop.NativeSequentialTimeFaces

/-! Facewise annihilation for the actual two sequential supported caps.
The seam test hypothesis lives on the actual final collar; both original
small approximations preserve its inverse-image carrier. -/
@[expose] public section
namespace Finsler.NativeSequentialTestedFaces
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeSequentialTimeFaces
open Finsler.NativeSupportedStageCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (q : ℕ)

def prefixTested (T : singularCochainGroup (ZMod 2) (NativeSequentialCollarGeometry.prefixSource m hm F) q) :=
  (firstOperation m hm F).component ((m + 1) + q) ≫
    (prefixOperation m hm F).component q ≫ cochainPullback (prefixFinal m hm F) q T

def suffixTested (T : singularCochainGroup (ZMod 2) (NativeSequentialCollarGeometry.suffixSource m hm F) q) :=
  (firstOperation m hm F).component ((m + 1) + q) ≫
    (suffixOperation m hm F).component q ≫ cochainPullback (suffixFinal m hm F) q T

theorem prefix_outer_zero (T : singularCochainGroup (ZMod 2) (NativeSequentialCollarGeometry.prefixSource m hm F) q)
    (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (outerFace (m + 1) t)) _
      (prefixTested m hm F q T) = 0 := by
  have h := congrArg (fun c => c ≫ ((prefixOperation m hm F).component q ≫
    cochainPullback (prefixFinal m hm F) q T)) (first_endpoint m hm F t ht ((m + 1) + q))
  simp only [Category.assoc, zero_comp] at h
  exact h

theorem suffix_outer_zero (T : singularCochainGroup (ZMod 2) (NativeSequentialCollarGeometry.suffixSource m hm F) q)
    (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (outerFace (m + 1) t)) _
      (suffixTested m hm F q T) = 0 := by
  have h := congrArg (fun c => c ≫ ((suffixOperation m hm F).component q ≫
    cochainPullback (suffixFinal m hm F) q T)) (first_endpoint m hm F t ht ((m + 1) + q))
  simp only [Category.assoc, zero_comp] at h
  exact h

theorem prefix_inner_zero (T : singularCochainGroup (ZMod 2) (NativeSequentialCollarGeometry.prefixSource m hm F) q) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 0)) _
      (prefixTested m hm F q T) = 0 := by
  apply output_zero (firstParameter (m + 1)) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (innerFace (m + 1) 0) ((m + 1) + q)
  change (push (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F 0))).f _ ≫
    (prefixOperation m hm F).component q ≫ _ = 0
  rw [← Category.assoc, NativeSequentialTimeFaces.prefix_inner_zero, zero_comp]

theorem suffix_inner_one (T : singularCochainGroup (ZMod 2) (NativeSequentialCollarGeometry.suffixSource m hm F) q) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 1)) _
      (suffixTested m hm F q T) = 0 := by
  apply output_zero (firstParameter (m + 1)) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (innerFace (m + 1) 1) ((m + 1) + q)
  change (push (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F 1))).f _ ≫
    (suffixOperation m hm F).component q ≫ _ = 0
  rw [← Category.assoc, NativeSequentialTimeFaces.suffix_inner_one, zero_comp]

theorem prefix_seam_zero (T : singularCochainGroup (ZMod 2) (NativeSequentialCollarGeometry.prefixSource m hm F) q)
    (hT : cochainPullback (SupportedCap.subspaceMap (NativeSequentialCollarGeometry.prefixSource m hm F)
      (NativeSequentialCollarGeometry.prefixCollar m hm F)) q T = 0) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 1)) _
      (prefixTested m hm F q T) = 0 := by
  apply output_zero (firstParameter (m + 1)) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (innerFace (m + 1) 1) ((m + 1) + q)
  apply output_zero (prefixParameter m hm F) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (outerInnerFace m hm F 1) q
  exact pullback_support (prefixFinal m hm F) _ (NativeSequentialCollarGeometry.prefixCollar m hm F)
    (by
      intro z hz
      apply NativeSequentialCollarGeometry.prefix_seam_in_collar m hm F ⟨prefixFinal m hm F z, ?_⟩
      change z.val.val.2 = 1 at hz
      change (z.val.val.2 : ℝ) = 1
      exact congrArg (fun t : ClosedInterval => (t : ℝ)) hz) q T hT

theorem suffix_seam_zero (T : singularCochainGroup (ZMod 2) (NativeSequentialCollarGeometry.suffixSource m hm F) q)
    (hT : cochainPullback (SupportedCap.subspaceMap (NativeSequentialCollarGeometry.suffixSource m hm F)
      (NativeSequentialCollarGeometry.suffixCollar m hm F)) q T = 0) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (innerFace (m + 1) 0)) _
      (suffixTested m hm F q T) = 0 := by
  apply output_zero (firstParameter (m + 1)) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (innerFace (m + 1) 0) ((m + 1) + q)
  apply output_zero (suffixParameter m hm F) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (outerInnerFace m hm F 0) q
  exact pullback_support (suffixFinal m hm F) _ (NativeSequentialCollarGeometry.suffixCollar m hm F)
    (by
      intro z hz
      apply NativeSequentialCollarGeometry.suffix_seam_in_collar m hm F ⟨suffixFinal m hm F z, ?_⟩
      change z.val.val.2 = 0 at hz
      change (z.val.val.2 : ℝ) = 0
      exact congrArg (fun t : ClosedInterval => (t : ℝ)) hz) q T hT

end
end Finsler.NativeSequentialTestedFaces
