module

public import Finsler.Loop.SupportedCapPullbackPrimitive
public import Finsler.Loop.NativeGHIntervalOrder
public import Finsler.Loop.NativeBothInterleavedSquare

/-! Compare the genuine canonical product-cover cap to pullback of
BOTH SAME raw interleaved operations. The explicit correction is the
original source subdivision prism. Degrees agree with the cap/interval
comparison, and no retraction naturality is asserted. -/
@[expose] public section
namespace Finsler.NativeGHProductPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
open Finsler.RightIntervalCochain Finsler.SupportedIntervalProduct
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
abbrev raw := NativeSequentialSupportedStages.source (m + 1)
abbrev parameter := NativeSequentialSupportedStages.firstParameter (m + 1)
abbrev farBase := NativeOrderedDoubleCutSupported.far (𝟙 (base m)) (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev farRaw := NativeOrderedDoubleCutSupported.far (parameter m) (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev nearRaw := NativeOrderedDoubleCutSupported.near (parameter m) (NativeClosingArcPowerVanishing.radius m hm F)
abbrev farProduct := liftSet (base m) (farBase m hm F)
abbrev nearProduct := liftSet (base m) (near m hm F)
abbrev farBaseOpen := NativeOrderedDoubleCutSupported.far_open (𝟙 (base m)) (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev nearBaseOpen := NativeOrderedDoubleCutSupported.near_open (𝟙 (base m)) (NativeClosingArcPowerVanishing.radius m hm F)
abbrev baseCover := NativeOrderedDoubleCutSupported.cover (𝟙 (base m)) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)
abbrev farProductOpen := lift_open (base m) (farBase m hm F) (farBaseOpen m hm F)
abbrev nearProductOpen := lift_open (base m) (near m hm F) (nearBaseOpen m hm F)
abbrev productCover := lift_cover (base m) (farBase m hm F) (near m hm F) (baseCover m hm F)
abbrev farRawOpen := NativeOrderedDoubleCutSupported.far_open (parameter m) (NativeOrderedDoubleCutSupported.thomRadius m hm F)
abbrev nearRawOpen := NativeOrderedDoubleCutSupported.near_open (parameter m) (NativeClosingArcPowerVanishing.radius m hm F)
abbrev rawCover := NativeOrderedDoubleCutSupported.cover (parameter m) (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)
abbrev theta := NativeOrderedDoubleCutSupported.thom (parameter m) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
abbrev thetaSupport := NativeOrderedDoubleCutSupported.thom_supported (parameter m) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)

theorem far_maps : Set.MapsTo (rawSource m) (farProduct m hm F) (farRaw m hm F) := fun _ h => h
theorem near_maps : Set.MapsTo (rawSource m) (nearProduct m hm F) (nearRaw m hm F) := fun _ h => h

theorem near_map : restriction (rawSource m) (nearProduct m hm F) (nearRaw m hm F) (near_maps m hm F) =
    nearOut (base m) (near m hm F) ≫ rawNear m hm F := rfl

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)

def rawTest : singularCochainGroup (ZMod 2) (TopCat.of (nearRaw m hm F)) (index m a b k side + 1) :=
  match side with
  | false => NativePrefixTestOrder.interleaved m hm F a b k E
  | true => NativeSuffixTestOrder.interleaved m hm F a b k E

theorem rawTest_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (nearRaw m hm F)) (index m a b k side + 1)
      (rawTest m hm F a b k E side) = 0 := by
  cases side with
  | false => exact NativeInterleavedInnerFaces.prefix_closed m hm F a b k E hE
  | true => exact NativeInterleavedInnerFaces.suffix_closed m hm F a b k E hE

theorem test_original : test m hm F a b k E side =
    cochainPullback (rawNear m hm F) (index m a b k side + 1) (rawTest m hm F a b k E side) := by
  cases side <;> rfl

def productValue := SupportedCapPullbackPrimitive.localValue (rawSource m)
  (farProduct m hm F) (nearProduct m hm F) (farRaw m hm F) (nearRaw m hm F)
  (farProductOpen m hm F) (nearProductOpen m hm F) (productCover m hm F)
  (far_maps m hm F) (near_maps m hm F) (m + 1) (index m a b k side + 1)
  (m + index m a b k side + 1 + 1) (by omega) (theta m hm F) (thetaSupport m hm F)
  (rawTest m hm F a b k E side)

def originalValue := SupportedCapPullbackPrimitive.original (rawSource m)
  (farRaw m hm F) (nearRaw m hm F) (farRawOpen m hm F) (nearRawOpen m hm F) (rawCover m hm F)
  (m + 1) (index m a b k side + 1) (m + index m a b k side + 1 + 1) (by omega)
  (theta m hm F) (thetaSupport m hm F) (rawTest m hm F a b k E side)

def primitive := SupportedCapPullbackPrimitive.primitive (rawSource m)
  (farProduct m hm F) (nearProduct m hm F) (farRaw m hm F) (nearRaw m hm F)
  (farProductOpen m hm F) (nearProductOpen m hm F) (productCover m hm F)
  (farRawOpen m hm F) (nearRawOpen m hm F) (rawCover m hm F) (far_maps m hm F) (near_maps m hm F)
  (m + 1) (index m a b k side + 1) (theta m hm F) (thetaSupport m hm F)
  (rawTest m hm F a b k E side) (m + index m a b k side + 1) (by omega)

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (space (base m)) (m + index m a b k side + 1)
      (primitive m hm F a b k E side) = productValue m hm F a b k E side - originalValue m hm F a b k E side :=
  SupportedCapPullbackPrimitive.boundary _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (NativeOrderedDoubleCutSupported.thom_closed (parameter m) (by omega) _)
    (rawTest_closed m hm F a b k E side hE)

theorem product_tested : productValue m hm F a b k E side =
    tested (base m) (farBase m hm F) (near m hm F) (farBaseOpen m hm F) (nearBaseOpen m hm F)
      (baseCover m hm F) (m + 1) (index m a b k side + 1) (m + index m a b k side + 1 + 1) (by omega)
      (NativeOrderedDoubleCutSupported.thom (𝟙 (base m)) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))
      (NativeOrderedDoubleCutSupported.thom_supported (𝟙 (base m)) (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F))
      (test m hm F a b k E side) := by
  unfold productValue SupportedCapPullbackPrimitive.localValue tested
  rw [near_map, pullback_comp, ← test_original]
  simp only [theta, NativeOrderedDoubleCutSupported.thom, ← pullback_comp, raw_parameter, Category.comp_id]

theorem interval_product : TimeTriangleSplit.interval (base m) (m + index m a b k side + 1) ≫
    productValue m hm F a b k E side = NativeGHIntervalOrder.after m hm F a b k E side := by
  rw [product_tested]
  rfl

end
end Finsler.NativeGHProductPullback
