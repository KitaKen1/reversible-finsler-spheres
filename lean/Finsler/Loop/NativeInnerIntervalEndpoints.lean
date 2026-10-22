module

public import Finsler.Loop.NativeInnerCutEndpointValues
public import Finsler.Loop.NativeInnerIntervalComparison

/-! The SAME actual retained-factor pullback correction vanishes at
BOTH near-interval endpoints, for BOTH raw-half stages. The endpoint
terms retained in Stage113 can therefore be removed literally. -/
@[expose] public section
namespace Finsler.NativeInnerIntervalEndpoints
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.IntervalSobolev
open Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeSequentialTimeFaces
open Finsler.NativeIntervalGHTests Finsler.NativeInnerIntervalComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem prefix_retained_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F t))
      (NativePrefixTestOrder.index m a b k) (NativeInnerRetainedComparison.prefixPrimitive m hm F a b k E) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ _ _ _
    (Or.inl (NativeInnerCutEndpointValues.prefix_primitive_endpoint m hm F a b t ht))

theorem suffix_retained_endpoint (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F t))
      (NativeSuffixTestOrder.index m a b k) (NativeInnerRetainedComparison.suffixPrimitive m hm F a b k E) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ _ _ _
    (Or.inr (NativeInnerCutEndpointValues.suffix_primitive_endpoint m hm F b k E t ht))

theorem raw_endpoint (side : Bool) (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (outerSpace m hm F) (outerInnerFace m hm F t))
      (index m a b k side) (rawPrimitive m hm F a b k E side) = 0 := by
  cases side with
  | false => exact prefix_retained_endpoint m hm F a b k E t ht
  | true => exact suffix_retained_endpoint m hm F a b k E t ht

theorem tube_endpoint (side : Bool) (t : ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (RightIntervalCochain.endpoint (TopCat.of (near m hm F)) t)
      (lowDegree m a b k side + 1) (tubePrimitive m hm F a b k E side) = 0 := by
  apply NativeSequentialGHGlobalComparison.pullback_pre_zero
  rw [← pullback_comp]
  exact NativeSupportedStageCarrier.map_zero _ (outerInnerFace m hm F t) (endpoint_mem m hm F t)
    _ _ (raw_endpoint m hm F a b k E side t ht)

theorem corrected_original (side : Bool) : correctedOriginal m hm F a b k E side =
    RightIntervalFullCoboundary.integrate (TopCat.of (near m hm F)) (lowDegree m a b k side + 1)
      (tubeOriginal m hm F a b k E side) :=
  RightIntervalFullCoboundary.corrected_of_endpoints _ _ _ _
    (tube_endpoint m hm F a b k E side 0 (Or.inl rfl))
    (tube_endpoint m hm F a b k E side 1 (Or.inr rfl))

theorem endpoint_free_boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (near m hm F)) (lowDegree m a b k side)
      (primitive m hm F a b k E side) = before m hm F a b k E side -
        RightIntervalFullCoboundary.integrate (TopCat.of (near m hm F)) (lowDegree m a b k side + 1)
          (tubeOriginal m hm F a b k E side) := by
  rw [boundary m hm F a b k E side hE, corrected_original]

end
end Finsler.NativeInnerIntervalEndpoints
