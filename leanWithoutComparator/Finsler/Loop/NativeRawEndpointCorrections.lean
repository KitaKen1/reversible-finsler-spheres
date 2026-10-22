module

public import Finsler.Loop.NativeRawEndpointGeometry
public import Finsler.Loop.ReindexedThomCarrier
public import Finsler.Loop.NativeRawReindexedComparison

/-! All remaining terms of the original Stage103 common-output
primitive vanish on the actual exterior raw faces. The inverse-image
subdivision terms will be cancelled algebraically, rather than audited twice. -/
@[expose] public section
namespace Finsler.NativeRawEndpointCorrections
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeRawClockDoubleGeometry
open Finsler.NativeRawClockSupportedAlignment Finsler.NativeRawOrderedCupGeometry
open Finsler.NativeRawEndpointGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_double_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (index m a b k)
      (NativeRawDoubleCapCommon.prefixPrimitive m hm F a b k E) = 0 :=
  DoubleCapThomCarrier.primitive_zero (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (prefixThom m hm F)
  (outer_supported m hm F) (prefix_supported m hm F) (prefixTest m hm F a b k E)
    (prefixFace m last) (prefix_thom_zero m hm F last)

theorem prefix_cup_one_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (index m a b k)
      (NativeRawCupOrder.prefixPrimitive m hm F a b k E) = 0 :=
  DoubleCapThomCarrier.cup_one_zero (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (prefixFar m hm F) (prefixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (prefixThom m hm F)
  (outer_supported m hm F) (prefix_supported m hm F) (prefixTest m hm F a b k E)
    (prefixFace m last) (prefix_thom_zero m hm F last)

theorem prefix_reindexed_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (index m a b k)
      (NativeRawReindexedComparison.prefixPrimitive m hm F a b k E) = 0 :=
  ReindexedThomCarrier.primitive_zero (NativeRawClockMaps.prefixClock (m + 1)) Bool.not
  (prefixFarFamily m hm F) (prefixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
  (prefix_far_open m hm F) (prefix_near_open m hm F) (prefix_cover m hm F)
  (NativeOrderedScalarPullback.far_open m hm F) (NativeOrderedScalarPullback.near_open m hm F) (NativeOrderedScalarPullback.cover m hm F)
  (prefix_far_maps m hm F) (prefix_near_maps m hm F)
  ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
  (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
  (NativeOrderedDoubleCapCommon.test m hm F a b k E)
    (prefixFace m last) (NativeOrderedEndpointCarrier.endpoint m last) (prefix_maps m last)
    (NativeOrderedEndpointCarrier.cup_zero m hm F last)

theorem prefix_ordered_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (index m a b k)
      (cochainPullback (NativeRawClockMaps.prefixClock (m + 1)) (index m a b k)
        (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)) = 0 :=
  pullback_support (NativeRawClockMaps.prefixClock (m + 1)) (prefixFace m last)
    (NativeOrderedEndpointCarrier.endpoint m last) (prefix_maps m last) (index m a b k)
    (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)
    (NativeOrderedEndpointCarrier.primitive_zero m hm F a b k E last)

theorem suffix_double_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)) (index m a b k)
      (NativeRawDoubleCapCommon.suffixPrimitive m hm F a b k E) = 0 :=
  DoubleCapThomCarrier.primitive_zero (source (m + 1)) (outerFar m hm F) (outerNear m hm F) (suffixFar m hm F) (suffixNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (outerThom m hm F) (suffixThom m hm F)
  (outer_supported m hm F) (suffix_supported m hm F) (suffixTest m hm F a b k E)
    (suffixFace m last) (suffix_thom_zero m hm F last)

theorem suffix_reindexed_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)) (index m a b k)
      (NativeRawReindexedComparison.suffixPrimitive m hm F a b k E) = 0 :=
  ReindexedThomCarrier.primitive_zero (NativeRawClockMaps.suffixClock (m + 1)) id
  (suffixFarFamily m hm F) (suffixNearSet m hm F) (NativeOrderedScalarPullback.farFamily m hm F) (NativeOrderedScalarPullback.nearSet m hm F)
  (suffix_far_open m hm F) (suffix_near_open m hm F) (suffix_cover m hm F)
  (NativeOrderedScalarPullback.far_open m hm F) (NativeOrderedScalarPullback.near_open m hm F) (NativeOrderedScalarPullback.cover m hm F)
  (suffix_far_maps m hm F) (suffix_near_maps m hm F)
  ((m + 1) + m + 1) (testDegree m a b k) (index m a b k) (by dsimp [index]; omega)
  (NativeOrderedScalarPullback.thomCup m hm F) (NativeOrderedScalarPullback.thomCup_supported m hm F)
  (NativeOrderedDoubleCapCommon.test m hm F a b k E)
    (suffixFace m last) (NativeOrderedEndpointCarrier.endpoint m last) (suffix_maps m last)
    (NativeOrderedEndpointCarrier.cup_zero m hm F last)

theorem suffix_ordered_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)) (index m a b k)
      (cochainPullback (NativeRawClockMaps.suffixClock (m + 1)) (index m a b k)
        (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)) = 0 :=
  pullback_support (NativeRawClockMaps.suffixClock (m + 1)) (suffixFace m last)
    (NativeOrderedEndpointCarrier.endpoint m last) (suffix_maps m last) (index m a b k)
    (NativeOrderedDoubleCapCommon.primitive m hm F a b k E)
    (NativeOrderedEndpointCarrier.primitive_zero m hm F a b k E last)

end
end Finsler.NativeRawEndpointCorrections
