module

public import Finsler.Loop.NativeOrderedEndpointCarrier
public import Finsler.Loop.NativeRawOrderedCupGeometry
public import Finsler.Loop.NativeRawTimeSquareBoundary

/-! The remaining actual raw faces map to the two ordered endpoint
faces. Exact pullbacks of the original normalized Thom factors transport
their carrier zero; no statement about a closed union is used. -/
@[expose] public section
namespace Finsler.NativeRawEndpointGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeSequentialSupportedStages Finsler.NativeRawClockDoubleGeometry
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

def prefixFace (last : Bool) : Set (source (m + 1)) :=
  NativeRawTimeSquareBoundary.face (m + 1) (if last then 1 else 0)
def suffixFace (last : Bool) : Set (source (m + 1)) :=
  NativeRawTimeSquareBoundary.face (m + 1) (if last then 2 else 3)

theorem prefix_maps (last : Bool) : Set.MapsTo (NativeRawClockMaps.prefixClock (m + 1))
    (prefixFace m last) (NativeOrderedEndpointCarrier.endpoint m last) := by
  intro z hz
  cases last
  · change z.2 = 0 at hz
    apply Subtype.ext
    change (z.1.1 : ℝ) * z.2 = 0
    rw [hz]
    simp
  · exact hz

theorem suffix_maps (last : Bool) : Set.MapsTo (NativeRawClockMaps.suffixClock (m + 1))
    (suffixFace m last) (NativeOrderedEndpointCarrier.endpoint m last) := by
  intro z hz
  cases last
  · exact hz
  · change z.2 = 1 at hz
    apply Subtype.ext
    change (z.1.1 : ℝ) + (1 - z.1.1) * z.2 = 1
    rw [hz]
    simp

theorem prefix_thom_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (m + 1) (outerThom m hm F) = 0 ∨
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (prefixFace m last)) (m + 1) (prefixThom m hm F) = 0 := by
  rcases NativeOrderedEndpointCarrier.thom_zero m hm F last with h | h
  · apply Or.inr
    have hz := pullback_support (NativeRawClockMaps.prefixClock (m + 1)) (prefixFace m last)
      (NativeOrderedEndpointCarrier.endpoint m last) (prefix_maps m last) (m + 1)
      (NativeOrderedDoubleCapCommon.firstThom m hm F) h
    rw [NativeRawOrderedCupGeometry.prefix_first_thom] at hz
    exact hz
  · apply Or.inl
    have hz := pullback_support (NativeRawClockMaps.prefixClock (m + 1)) (prefixFace m last)
      (NativeOrderedEndpointCarrier.endpoint m last) (prefix_maps m last) (m + 1)
      (NativeOrderedDoubleCapCommon.lastThom m hm F) h
    rw [NativeRawOrderedCupGeometry.prefix_last_thom] at hz
    exact hz

theorem suffix_thom_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)) (m + 1) (outerThom m hm F) = 0 ∨
    cochainPullback (SupportedCap.subspaceMap (source (m + 1)) (suffixFace m last)) (m + 1) (suffixThom m hm F) = 0 := by
  rcases NativeOrderedEndpointCarrier.thom_zero m hm F last with h | h
  · apply Or.inl
    have hz := pullback_support (NativeRawClockMaps.suffixClock (m + 1)) (suffixFace m last)
      (NativeOrderedEndpointCarrier.endpoint m last) (suffix_maps m last) (m + 1)
      (NativeOrderedDoubleCapCommon.firstThom m hm F) h
    rw [NativeRawOrderedCupGeometry.suffix_first_thom] at hz
    exact hz
  · apply Or.inr
    have hz := pullback_support (NativeRawClockMaps.suffixClock (m + 1)) (suffixFace m last)
      (NativeOrderedEndpointCarrier.endpoint m last) (suffix_maps m last) (m + 1)
      (NativeOrderedDoubleCapCommon.lastThom m hm F) h
    rw [NativeRawOrderedCupGeometry.suffix_last_thom] at hz
    exact hz

end
end Finsler.NativeRawEndpointGeometry
