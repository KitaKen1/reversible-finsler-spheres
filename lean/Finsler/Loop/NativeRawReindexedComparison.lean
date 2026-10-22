module

public import Finsler.Loop.NativeRawCupOrder
public import Finsler.Loop.MultiFarReindexedCarrier

/-! Compare BOTH actual raw ordered-cup evaluations with the pullback
of the SAME sealed ordered common cap. Prefix uses the explicit far
index swap. Source cochains and tests are identified literally, while
full retraction differences are retained as supported primitives. -/
@[expose] public section
namespace Finsler.NativeRawReindexedComparison
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeRawClockDoubleGeometry
open Finsler.NativeRawClockSupportedAlignment Finsler.NativeRawOrderedCupGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def prefixValue := MultiFarReindexedPullback.sourceValue (NativeRawClockMaps.prefixClock (m + 1)) Bool.not
  (prefixFarFamily m hm F) (prefixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
  (prefix_far_open m hm F) (prefix_near_open m hm F) (prefix_cover m hm F)
  (prefix_far_maps m hm F) (prefix_near_maps m hm F)
  ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
  (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
  (NativeOrderedDoubleCapCommon.test m hm F a b k E)
def prefixPrimitive := MultiFarReindexedPullback.primitive (NativeRawClockMaps.prefixClock (m + 1)) Bool.not
  (prefixFarFamily m hm F) (prefixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
  (prefix_far_open m hm F) (prefix_near_open m hm F) (prefix_cover m hm F)
  (NativeOrderedScalarPullback.far_open m hm F) (NativeOrderedScalarPullback.near_open m hm F) (NativeOrderedScalarPullback.cover m hm F)
  (prefix_far_maps m hm F) (prefix_near_maps m hm F)
  ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
  (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
  (NativeOrderedDoubleCapCommon.test m hm F a b k E)

theorem prefix_source_eq : prefixValue m hm F a b k E = NativeRawCupOrder.prefixOrdered m hm F a b k E := by
  have hc := MultiFarSupportedCochain.cut_eq (source (m + 1)) (prefixFarFamily m hm F) (prefixNearSet m hm F)
    (prefix_far_open m hm F) (prefix_near_open m hm F) (prefix_cover m hm F)
    ((m + 1) + m + 1) (testDegree m a b k) (index m a b k + 1) (by dsimp [index]; omega)
    (cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) ((m + 1) + m + 1) (NativeOrderedScalarPullback.thomCup m hm F))
    (DoubleFarCupOneCap.rightCup (source (m + 1)) (m + 1) m (outerThom m hm F) (prefixThom m hm F))
    (fun i => pullback_support (NativeRawClockMaps.prefixClock (m + 1)) (prefixFarFamily m hm F i)
      (NativeOrderedScalarPullback.farFamily m hm F (Bool.not i)) (prefix_far_maps m hm F i)
      ((m + 1) + m + 1) (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F (Bool.not i)))
    (DoubleFarCupOneCap.right_supported (source (m + 1)) (outerFar m hm F) (prefixFar m hm F)
      (m + 1) m (outerThom m hm F) (prefixThom m hm F) (outer_supported m hm F) (prefix_supported m hm F))
    (prefix_cup m hm F)
  exact congrArg₂ (fun c T => c ≫ T) hc (prefix_test m hm F a b k E)

theorem prefix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (prefixPrimitive m hm F a b k E) =
    NativeRawCupOrder.prefixOrdered m hm F a b k E - cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) (index m a b k + 1)
      (NativeOrderedDoubleCapCommon.coupled m hm F a b k E) := by
  have h := MultiFarReindexedPullback.boundary (NativeRawClockMaps.prefixClock (m + 1)) Bool.not
    (prefixFarFamily m hm F) (prefixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
    (prefix_far_open m hm F) (prefix_near_open m hm F) (prefix_cover m hm F)
    (NativeOrderedScalarPullback.far_open m hm F) (NativeOrderedScalarPullback.near_open m hm F) (NativeOrderedScalarPullback.cover m hm F)
    (prefix_far_maps m hm F) (prefix_near_maps m hm F)
    ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
    (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
    (NativeOrderedDoubleCapCommon.test m hm F a b k E)
    (NativeOrderedScalarPullback.thomCup_closed m hm F) (NativeOrderedDoubleCapCommon.test_closed m hm F a b k E hE)
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (prefixPrimitive m hm F a b k E) =
    prefixValue m hm F a b k E - cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) (index m a b k + 1)
      (NativeOrderedDoubleCapCommon.coupled m hm F a b k E) at h
  rw [prefix_source_eq] at h
  exact h

theorem prefix_primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.prefixDiagonal m)) (index m a b k)
    (prefixPrimitive m hm F a b k E) = 0 :=
  MultiFarReindexedCarrier.primitive_zero (NativeRawClockMaps.prefixClock (m + 1)) Bool.not
  (prefixFarFamily m hm F) (prefixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
  (prefix_far_open m hm F) (prefix_near_open m hm F) (prefix_cover m hm F)
  (NativeOrderedScalarPullback.far_open m hm F) (NativeOrderedScalarPullback.near_open m hm F) (NativeOrderedScalarPullback.cover m hm F)
  (prefix_far_maps m hm F) (prefix_near_maps m hm F)
  ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
  (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
  (NativeOrderedDoubleCapCommon.test m hm F a b k E)
    (NativeRawDoubleCapCommon.prefixDiagonal m) (NativeOrderedDoubleCutSupported.diagonal m) (fun _ h => h)
    (NativeOrderedDoubleCapCommon.diagonal_test_zero m hm F a b k E)

def suffixValue := MultiFarReindexedPullback.sourceValue (NativeRawClockMaps.suffixClock (m + 1)) id
  (suffixFarFamily m hm F) (suffixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
  (suffix_far_open m hm F) (suffix_near_open m hm F) (suffix_cover m hm F)
  (suffix_far_maps m hm F) (suffix_near_maps m hm F)
  ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
  (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
  (NativeOrderedDoubleCapCommon.test m hm F a b k E)
def suffixPrimitive := MultiFarReindexedPullback.primitive (NativeRawClockMaps.suffixClock (m + 1)) id
  (suffixFarFamily m hm F) (suffixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
  (suffix_far_open m hm F) (suffix_near_open m hm F) (suffix_cover m hm F)
  (NativeOrderedScalarPullback.far_open m hm F) (NativeOrderedScalarPullback.near_open m hm F) (NativeOrderedScalarPullback.cover m hm F)
  (suffix_far_maps m hm F) (suffix_near_maps m hm F)
  ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
  (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
  (NativeOrderedDoubleCapCommon.test m hm F a b k E)

theorem suffix_source_eq : suffixValue m hm F a b k E = NativeRawDoubleCapCommon.suffixCoupled m hm F a b k E := by
  have hc := MultiFarSupportedCochain.cut_eq (source (m + 1)) (suffixFarFamily m hm F) (suffixNearSet m hm F)
    (suffix_far_open m hm F) (suffix_near_open m hm F) (suffix_cover m hm F)
    ((m + 1) + m + 1) (testDegree m a b k) (index m a b k + 1) (by dsimp [index]; omega)
    (cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) ((m + 1) + m + 1) (NativeOrderedScalarPullback.thomCup m hm F))
    (DoubleFarCupOneCap.leftCup (source (m + 1)) (m + 1) m (outerThom m hm F) (suffixThom m hm F))
    (fun i => pullback_support (NativeRawClockMaps.suffixClock (m + 1)) (suffixFarFamily m hm F i)
      (NativeOrderedScalarPullback.farFamily m hm F (id i)) (suffix_far_maps m hm F i)
      ((m + 1) + m + 1) (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F (id i)))
    (DoubleFarCupOneCap.left_supported (source (m + 1)) (outerFar m hm F) (suffixFar m hm F)
      (m + 1) m (outerThom m hm F) (suffixThom m hm F) (outer_supported m hm F) (suffix_supported m hm F))
    (suffix_cup m hm F)
  exact congrArg₂ (fun c T => c ≫ T) hc (suffix_test m hm F a b k E)

theorem suffix_boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (suffixPrimitive m hm F a b k E) =
    NativeRawDoubleCapCommon.suffixCoupled m hm F a b k E - cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) (index m a b k + 1)
      (NativeOrderedDoubleCapCommon.coupled m hm F a b k E) := by
  have h := MultiFarReindexedPullback.boundary (NativeRawClockMaps.suffixClock (m + 1)) id
    (suffixFarFamily m hm F) (suffixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
    (suffix_far_open m hm F) (suffix_near_open m hm F) (suffix_cover m hm F)
    (NativeOrderedScalarPullback.far_open m hm F) (NativeOrderedScalarPullback.near_open m hm F) (NativeOrderedScalarPullback.cover m hm F)
    (suffix_far_maps m hm F) (suffix_near_maps m hm F)
    ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
    (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
    (NativeOrderedDoubleCapCommon.test m hm F a b k E)
    (NativeOrderedScalarPullback.thomCup_closed m hm F) (NativeOrderedDoubleCapCommon.test_closed m hm F a b k E hE)
  change cochainCoboundary (ZMod 2) (source (m + 1)) (index m a b k) (suffixPrimitive m hm F a b k E) =
    suffixValue m hm F a b k E - cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) (index m a b k + 1)
      (NativeOrderedDoubleCapCommon.coupled m hm F a b k E) at h
  rw [suffix_source_eq] at h
  exact h

theorem suffix_primitive_diagonal_zero : cochainPullback
    (SupportedCap.subspaceMap (source (m + 1)) (NativeRawDoubleCapCommon.suffixDiagonal m)) (index m a b k)
    (suffixPrimitive m hm F a b k E) = 0 :=
  MultiFarReindexedCarrier.primitive_zero (NativeRawClockMaps.suffixClock (m + 1)) id
  (suffixFarFamily m hm F) (suffixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
  (suffix_far_open m hm F) (suffix_near_open m hm F) (suffix_cover m hm F)
  (NativeOrderedScalarPullback.far_open m hm F) (NativeOrderedScalarPullback.near_open m hm F) (NativeOrderedScalarPullback.cover m hm F)
  (suffix_far_maps m hm F) (suffix_near_maps m hm F)
  ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
  (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
  (NativeOrderedDoubleCapCommon.test m hm F a b k E)
    (NativeRawDoubleCapCommon.suffixDiagonal m) (NativeOrderedDoubleCutSupported.diagonal m) (fun _ h => h)
    (NativeOrderedDoubleCapCommon.diagonal_test_zero m hm F a b k E)

end
end Finsler.NativeRawReindexedComparison
