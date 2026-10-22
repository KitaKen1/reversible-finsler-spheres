module

public import Finsler.Loop.NativeRawOrderedCupGeometry
public import Finsler.Loop.NativeRawDoubleCapCommon

/-! The genuine supported cup-one correction changes the prefix raw
outer-last/inner-first order to ordered first/last. The SAME local GH
test and real raw cover are retained; the primitive vanishes on the
full raw inverse diagonal. Suffix already has the ordered cup. -/
@[expose] public section
namespace Finsler.NativeRawCupOrder
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeRawClockDoubleGeometry
open Finsler.NativeRawClockSupportedAlignment Finsler.NativeRawOrderedCupGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def prefixOrdered := DoubleFarCupOneCap.right (source (m + 1)) (outerFar m hm F) (prefixFar m hm F)
  (m + 1) m (outerThom m hm F) (prefixThom m hm F) (outer_supported m hm F) (prefix_supported m hm F)
  (prefixNearSet m hm F) (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.far_open _ _)
  (prefix_near_open m hm F) (prefix_cover m hm F) (testDegree m a b k) (prefixTest m hm F a b k E)
def prefixPrimitive := DoubleFarCupOneCap.primitive (source (m + 1)) (outerFar m hm F) (prefixFar m hm F)
  (m + 1) m (outerThom m hm F) (prefixThom m hm F) (outer_supported m hm F) (prefix_supported m hm F)
  (prefixNearSet m hm F) (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.far_open _ _)
  (prefix_near_open m hm F) (prefix_cover m hm F) (testDegree m a b k) (prefixTest m hm F a b k E)

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (prefixPrimitive m hm F a b k E) =
    NativeRawDoubleCapCommon.prefixCoupled m hm F a b k E - prefixOrdered m hm F a b k E :=
  DoubleFarCupOneCap.boundary (source (m + 1)) (outerFar m hm F) (prefixFar m hm F)
  (m + 1) m (outerThom m hm F) (prefixThom m hm F) (outer_supported m hm F) (prefix_supported m hm F)
  (prefixNearSet m hm F) (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.far_open _ _)
  (prefix_near_open m hm F) (prefix_cover m hm F) (testDegree m a b k) (prefixTest m hm F a b k E)
    (NativeOrderedDoubleCutSupported.thom_closed _ _ _) (NativeOrderedDoubleCutSupported.thom_closed _ _ _)
    (prefix_test_closed m hm F a b k E hE)

theorem prefix_primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
    (prefixPrimitive m hm F a b k E) = 0 :=
  DoubleFarCupOneCap.primitive_carrier_zero (source (m + 1)) (outerFar m hm F) (prefixFar m hm F)
  (m + 1) m (outerThom m hm F) (prefixThom m hm F) (outer_supported m hm F) (prefix_supported m hm F)
  (prefixNearSet m hm F) (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.far_open _ _)
  (prefix_near_open m hm F) (prefix_cover m hm F) (testDegree m a b k) (prefixTest m hm F a b k E)
    (NativeRawDoubleCapCommon.prefixDiagonal m) (NativeRawDoubleCapCommon.prefix_diagonal_test_zero m hm F a b k E)

theorem prefix_ordered_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k + 1) (prefixOrdered m hm F a b k E) = 0 :=
  DoubleFarCupOneCap.right_closed (source (m + 1)) (outerFar m hm F) (prefixFar m hm F)
  (m + 1) m (outerThom m hm F) (prefixThom m hm F) (outer_supported m hm F) (prefix_supported m hm F)
  (prefixNearSet m hm F) (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.far_open _ _)
  (prefix_near_open m hm F) (prefix_cover m hm F) (testDegree m a b k) (prefixTest m hm F a b k E)
    (NativeOrderedDoubleCutSupported.thom_closed _ _ _) (NativeOrderedDoubleCutSupported.thom_closed _ _ _)
    (prefix_test_closed m hm F a b k E hE)

end
end Finsler.NativeRawCupOrder
