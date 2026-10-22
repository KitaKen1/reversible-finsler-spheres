module

public import Finsler.Loop.NativeSupportedStageCarrier

/-! The four actual time faces of the ORIGINAL sequential source.
Outer endpoints annihilate the first supported Thom operation. The
non-seam inner endpoints annihilate the corresponding second operation.
These are cochain restrictions, not merely pointwise assertions. -/
@[expose] public section
namespace Finsler.NativeSequentialTimeFaces
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeSupportedStageCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def outerFace (n : ℕ) (t : ClosedInterval) : Set (source n) := {z | z.1.1 = t}
def innerFace (n : ℕ) (u : ClosedInterval) : Set (source n) := {z | z.2 = u}

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

def outerInnerFace (u : ClosedInterval) : Set (outerSpace m hm F) :=
  (SupportedCap.subspaceMap (source (m + 1))
    (NativeOrderedDoubleCutSupported.near (firstParameter (m + 1)) (radius m hm F))) ⁻¹' innerFace (m + 1) u

theorem first_thom_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (outerFace (m + 1) t)) (m + 1)
      (NativeOrderedDoubleCutSupported.thom (firstParameter (m + 1)) (by omega)
        (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) = 0 := by
  apply parameter_time_zero (firstParameter (m + 1)) (by omega)
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (outerFace (m + 1) t) t (fun _ h => h)
  rcases ht with rfl | rfl
  · exact NormalizedSelfCut.time_zero _ _ _
  · exact NormalizedSelfCut.time_one _ _ _

theorem first_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) (q : ℕ) :
    (push (SupportedCap.subspaceMap (source (m + 1)) (outerFace (m + 1) t))).f ((m + 1) + q) ≫
      (firstOperation m hm F).component q = 0 :=
  thom_zero (firstParameter (m + 1)) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (outerFace (m + 1) t)
    (first_thom_endpoint m hm F t ht) q

theorem prefix_thom_inner_zero :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F 0)) (m + 1)
      (NativeOrderedDoubleCutSupported.thom (prefixParameter m hm F) (by omega)
        (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) = 0 := by
  apply parameter_time_zero (prefixParameter m hm F) (by omega)
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (outerInnerFace m hm F 0) 0
  · intro z hz
    apply Subtype.ext
    change (z.val.2 : ℝ) / 2 = 0
    change z.val.2 = 0 at hz
    rw [hz]
    norm_num
  · exact NormalizedSelfCut.time_zero _ _ _

theorem suffix_thom_inner_one :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F 1)) (m + 1)
      (NativeOrderedDoubleCutSupported.thom (suffixParameter m hm F) (by omega)
        (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)) = 0 := by
  apply parameter_time_zero (suffixParameter m hm F) (by omega)
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F) (outerInnerFace m hm F 1) 1
  · intro z hz
    apply Subtype.ext
    change (1 + (z.val.2 : ℝ)) / 2 = 1
    change z.val.2 = 1 at hz
    rw [hz]
    norm_num
  · exact NormalizedSelfCut.time_one _ _ _

theorem prefix_inner_zero (q : ℕ) :
    (push (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F 0))).f ((m + 1) + q) ≫
      (prefixOperation m hm F).component q = 0 :=
  thom_zero (prefixParameter m hm F) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (outerInnerFace m hm F 0)
    (prefix_thom_inner_zero m hm F) q

theorem suffix_inner_one (q : ℕ) :
    (push (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F 1))).f ((m + 1) + q) ≫
      (suffixOperation m hm F).component q = 0 :=
  thom_zero (suffixParameter m hm F) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (outerInnerFace m hm F 1)
    (suffix_thom_inner_one m hm F) q

end
end Finsler.NativeSequentialTimeFaces
