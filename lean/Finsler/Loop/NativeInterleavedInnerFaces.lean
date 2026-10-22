module

public import Finsler.Loop.NativePrefixTestFaces
public import Finsler.Loop.NativeSuffixTestFaces

/-! BOTH original interleaved inner GH/evaluation cochains are closed
and literally zero on both actual inner time faces. These are the tests
needed for cap/interval interchange, not just their correction primitives. -/
@[expose] public section
namespace Finsler.NativeInterleavedInnerFaces
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeSequentialTimeFaces
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (outerSpace m hm F) (NativePrefixTestOrder.index m a b k + 1)
      (NativePrefixTestOrder.interleaved m hm F a b k E) = 0 :=
  SupportedRightTestOrder.before_closed _ _ _ _ _ _ _ _ _ _ _ _ _
    (NativePrefixTestOrder.alpha_closed m hm F k E hE) (NativePrefixTestOrder.theta_closed m hm F)
    (NativePrefixTestOrder.psi_closed m hm F a b)

theorem suffix_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (outerSpace m hm F) (NativeSuffixTestOrder.index m a b k + 1)
      (NativeSuffixTestOrder.interleaved m hm F a b k E) = 0 :=
  SupportedCapTestOrderCoupling.before_closed _ _ _ _ _ _ _ _ _ _ _ _ _
    (NativeSuffixTestOrder.alpha_closed m hm F a) (NativeSuffixTestOrder.theta_closed m hm F)
    (NativeSuffixTestOrder.psi_closed m hm F b k E hE)

theorem prefix_zero : cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F)
    (outerInnerFace m hm F 0)) (NativePrefixTestOrder.index m a b k + 1)
      (NativePrefixTestOrder.interleaved m hm F a b k E) = 0 :=
  SupportedRightTestLocal.before_thom_zero _ _ _ _ _ _ _ _ _ _ _ _ _
    (outerInnerFace m hm F 0) (prefix_thom_inner_zero m hm F)

theorem prefix_one : cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F)
    (outerInnerFace m hm F 1)) (NativePrefixTestOrder.index m a b k + 1)
      (NativePrefixTestOrder.interleaved m hm F a b k E) = 0 :=
  SupportedRightTestOrder.before_test_zero _ _ _ _ _ _ _ _ _ _ _ _ _
    (outerInnerFace m hm F 1) (NativePrefixTestFaces.psi_seam_zero m hm F a b)

theorem suffix_zero : cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F)
    (outerInnerFace m hm F 0)) (NativeSuffixTestOrder.index m a b k + 1)
      (NativeSuffixTestOrder.interleaved m hm F a b k E) = 0 :=
  SupportedCapTestOrder.before_carrier_zero _ _ _ _ _ _ _ _ _ _ _ _ _
    (outerInnerFace m hm F 0) (NativeSuffixTestFaces.psi_seam_zero m hm F b k E)

theorem suffix_one : cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F)
    (outerInnerFace m hm F 1)) (NativeSuffixTestOrder.index m a b k + 1)
      (NativeSuffixTestOrder.interleaved m hm F a b k E) = 0 :=
  SupportedTestOrderThomCarrier.before_zero _ _ _ _ _ _ _ _ _ _ _ _ _
    (outerInnerFace m hm F 1) (suffix_thom_inner_one m hm F)

end
end Finsler.NativeInterleavedInnerFaces
