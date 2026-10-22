module

public import Finsler.Loop.NativeGHProductPullback

/-! All four time carriers annihilate the SAME product/raw scalar
subdivision primitive, for BOTH actual GH tests. Inner faces use the
proved GH test restrictions; outer faces use the original first Thom. -/
@[expose] public section
namespace Finsler.NativeGHProductFaces
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
open Finsler.RightIntervalCochain Finsler.SupportedIntervalProduct
open Finsler.NativeGHProductPullback Finsler.NativeSequentialTimeFaces
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)
  (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1)

include ht in
theorem rawTest_endpoint : cochainPullback
    (SupportedCap.subspaceMap (TopCat.of (nearRaw m hm F)) (outerInnerFace m hm F t))
    (index m a b k side + 1) (rawTest m hm F a b k E side) = 0 := by
  rcases ht with rfl | rfl <;> cases side
  · exact NativeInterleavedInnerFaces.prefix_zero m hm F a b k E
  · exact NativeInterleavedInnerFaces.suffix_zero m hm F a b k E
  · exact NativeInterleavedInnerFaces.prefix_one m hm F a b k E
  · exact NativeInterleavedInnerFaces.suffix_one m hm F a b k E

include ht in
theorem product_inner_zero : cochainPullback
    (SupportedCap.subspaceMap (space (base m)) (SupportedIntervalFaces.slice (base m) t))
    (m + index m a b k side + 1 + 1) (productValue m hm F a b k E side) = 0 := by
  rw [product_tested]
  apply SupportedIntervalFaces.tested_slice_zero
  rcases ht with rfl | rfl
  · exact test_zero m hm F a b k E side
  · exact test_one m hm F a b k E side

include ht in
theorem original_inner_zero : cochainPullback
    (SupportedCap.subspaceMap (space (base m)) (SupportedIntervalFaces.slice (base m) t))
    (m + index m a b k side + 1 + 1) (originalValue m hm F a b k E side) = 0 := by
  unfold originalValue SupportedCapPullbackPrimitive.original
  rw [← pullback_comp]
  apply NativeSupportedStageCarrier.map_zero _ (innerFace (m + 1) t)
  · intro z
    exact congrArg ULift.down z.property
  · apply SupportedCapTestOrder.cut_carrier_zero_at_degree
    exact NativeSupportedStageCarrier.map_zero
      (restriction (SupportedCap.subspaceMap (raw m) (innerFace (m + 1) t))
        ((SupportedCap.subspaceMap (raw m) (innerFace (m + 1) t)) ⁻¹' nearRaw m hm F)
        (nearRaw m hm F) (fun _ h => h))
      (outerInnerFace m hm F t) (fun z => z.val.property) _ _
      (rawTest_endpoint m hm F a b k E side t ht)

include ht in
theorem primitive_inner_zero : cochainPullback
    (SupportedCap.subspaceMap (space (base m)) (SupportedIntervalFaces.slice (base m) t))
    (m + index m a b k side + 1) (primitive m hm F a b k E side) = 0 :=
  SupportedCapPullbackPrimitive.primitive_carrier_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (product_inner_zero m hm F a b k E side t ht) (original_inner_zero m hm F a b k E side t ht)

include ht in
theorem primitive_endpoint : cochainPullback (endpoint (base m) t)
    (m + index m a b k side + 1) (primitive m hm F a b k E side) = 0 :=
  NativeSupportedStageCarrier.map_zero _ (SupportedIntervalFaces.slice (base m) t) (fun _ => rfl) _ _
    (primitive_inner_zero m hm F a b k E side t ht)

def outerCarrier (m : ℕ) (t : IntervalSobolev.ClosedInterval) : Set (space (base m)) :=
  rawSource m ⁻¹' outerFace (m + 1) t

include ht in
theorem product_outer_zero : cochainPullback
    (SupportedCap.subspaceMap (space (base m)) (outerCarrier m t))
    (m + index m a b k side + 1 + 1) (productValue m hm F a b k E side) = 0 := by
  have hz := SupportedThomCarrierZero.cut_map_zero (farProduct m hm F) (nearProduct m hm F) (outerCarrier m t)
    (farProductOpen m hm F) (nearProductOpen m hm F) (productCover m hm F)
    (m + 1) (index m a b k side + 1) (m + index m a b k side + 1 + 1) (by omega)
    (cochainPullback (rawSource m) (m + 1) (theta m hm F))
    (pullback_support (rawSource m) _ _ (far_maps m hm F) _ _ (thetaSupport m hm F))
    (pullback_support (rawSource m) (outerCarrier m t) (outerFace (m + 1) t) (fun _ h => h) _ _
      (first_thom_endpoint m hm F t ht))
    (SupportedCap.subspaceMap (space (base m)) (outerCarrier m t)) (fun z => z.property)
  have hv := congrArg (fun c => c ≫ cochainPullback
    (restriction (rawSource m) (nearProduct m hm F) (nearRaw m hm F) (near_maps m hm F))
    (index m a b k side + 1) (rawTest m hm F a b k E side)) hz
  simp only [Category.assoc, zero_comp] at hv
  exact hv

include ht in
theorem original_outer_zero : cochainPullback
    (SupportedCap.subspaceMap (space (base m)) (outerCarrier m t))
    (m + index m a b k side + 1 + 1) (originalValue m hm F a b k E side) = 0 := by
  unfold originalValue SupportedCapPullbackPrimitive.original
  rw [← pullback_comp]
  have hz := SupportedThomCarrierZero.cut_map_zero (farRaw m hm F) (nearRaw m hm F) (outerFace (m + 1) t)
    (farRawOpen m hm F) (nearRawOpen m hm F) (rawCover m hm F)
    (m + 1) (index m a b k side + 1) (m + index m a b k side + 1 + 1) (by omega)
    (theta m hm F) (thetaSupport m hm F) (first_thom_endpoint m hm F t ht)
    (SupportedCap.subspaceMap (space (base m)) (outerCarrier m t) ≫ rawSource m) (fun z => z.property)
  have hv := congrArg (fun c => c ≫ rawTest m hm F a b k E side) hz
  simp only [Category.assoc, zero_comp] at hv
  exact hv

include ht in
theorem primitive_outer_zero : cochainPullback
    (SupportedCap.subspaceMap (space (base m)) (outerCarrier m t))
    (m + index m a b k side + 1) (primitive m hm F a b k E side) = 0 :=
  SupportedCapPullbackPrimitive.primitive_carrier_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (product_outer_zero m hm F a b k E side t ht) (original_outer_zero m hm F a b k E side t ht)

include ht in
theorem primitive_outer_endpoint : cochainPullback (SelfCutThomCocycle.atTime (m + 1) t ▷ TopCat.I)
    (m + index m a b k side + 1) (primitive m hm F a b k E side) = 0 :=
  NativeSupportedStageCarrier.map_zero _ (outerCarrier m t) (fun _ => rfl) _ _
    (primitive_outer_zero m hm F a b k E side t ht)

end
end Finsler.NativeGHProductFaces
