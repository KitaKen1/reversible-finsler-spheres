module

public import Finsler.Loop.NativeInterleavedInnerFaces
public import Finsler.Loop.NativeSupportedIntervalOrder

/-! Put BOTH actual inner interleaved GH/evaluation tests on the
canonical right interval over the original outer tube. Explicit maps
retain the raw half clocks. Closure and BOTH endpoint hypotheses of
the supported cap/interval comparison are proved, not supplied. -/
@[expose] public section
namespace Finsler.NativeIntervalGHTests
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.RightIntervalCochain Finsler.NativeSequentialTimeFaces
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

abbrev base (m : ℕ) := SelfCutThomCocycle.parameters (m + 1)

def rawSource (m : ℕ) : space (base m) ⟶ NativeSequentialSupportedStages.source (m + 1) :=
  TopCat.ofHom ⟨fun z => (z.1, z.2.down), by fun_prop⟩

theorem raw_parameter (m : ℕ) : rawSource m ≫ NativeSequentialSupportedStages.firstParameter (m + 1) =
    SupportedIntervalProduct.project (base m) := rfl

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

abbrev near := NativeOrderedDoubleCutSupported.near (𝟙 (base m)) (NativeClosingArcPowerVanishing.radius m hm F)

def rawNear : space (TopCat.of (near m hm F)) ⟶ NativeSequentialSupportedStages.outerSpace m hm F :=
  TopCat.ofHom ⟨fun z => ⟨(z.1.val, z.2.down), z.1.property⟩, by fun_prop⟩

theorem raw_near_square : (SupportedCap.subspaceMap (base m) (near m hm F) ▷ TopCat.I) ≫ rawSource m =
    rawNear m hm F ≫ SupportedCap.subspaceMap (NativeSequentialSupportedStages.source (m + 1))
      (NativeOrderedDoubleCutSupported.near (NativeSequentialSupportedStages.firstParameter (m + 1))
        (NativeClosingArcPowerVanishing.radius m hm F)) := rfl

theorem endpoint_mem (t : _root_.unitInterval) (z : TopCat.of (near m hm F)) :
    rawNear m hm F (endpoint (TopCat.of (near m hm F)) t z) ∈ outerInnerFace m hm F t := rfl

def index (a b k : ℕ) (side : Bool) : ℕ :=
  if side then NativeSuffixTestOrder.index m a b k else NativePrefixTestOrder.index m a b k

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def test (side : Bool) : singularCochainGroup (ZMod 2) (space (TopCat.of (near m hm F)))
    (index m a b k side + 1) :=
  match side with
  | false => cochainPullback (rawNear m hm F) _ (NativePrefixTestOrder.interleaved m hm F a b k E)
  | true => cochainPullback (rawNear m hm F) _ (NativeSuffixTestOrder.interleaved m hm F a b k E)

theorem test_closed (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (space (TopCat.of (near m hm F))) (index m a b k side + 1)
      (test m hm F a b k E side) = 0 := by
  cases side with
  | false => exact pullback_closed _ _ _ (NativeInterleavedInnerFaces.prefix_closed m hm F a b k E hE)
  | true => exact pullback_closed _ _ _ (NativeInterleavedInnerFaces.suffix_closed m hm F a b k E hE)

theorem test_zero (side : Bool) : cochainPullback (endpoint (TopCat.of (near m hm F)) 0)
    (index m a b k side + 1) (test m hm F a b k E side) = 0 := by
  cases side with
  | false =>
    change cochainPullback _ _ (cochainPullback (rawNear m hm F) _ _) = 0
    rw [← pullback_comp]
    exact NativeSupportedStageCarrier.map_zero _ (outerInnerFace m hm F 0) (endpoint_mem m hm F 0) _ _
      (NativeInterleavedInnerFaces.prefix_zero m hm F a b k E)
  | true =>
    change cochainPullback _ _ (cochainPullback (rawNear m hm F) _ _) = 0
    rw [← pullback_comp]
    exact NativeSupportedStageCarrier.map_zero _ (outerInnerFace m hm F 0) (endpoint_mem m hm F 0) _ _
      (NativeInterleavedInnerFaces.suffix_zero m hm F a b k E)

theorem test_one (side : Bool) : cochainPullback (endpoint (TopCat.of (near m hm F)) 1)
    (index m a b k side + 1) (test m hm F a b k E side) = 0 := by
  cases side with
  | false =>
    change cochainPullback _ _ (cochainPullback (rawNear m hm F) _ _) = 0
    rw [← pullback_comp]
    exact NativeSupportedStageCarrier.map_zero _ (outerInnerFace m hm F 1) (endpoint_mem m hm F 1) _ _
      (NativeInterleavedInnerFaces.prefix_one m hm F a b k E)
  | true =>
    change cochainPullback _ _ (cochainPullback (rawNear m hm F) _ _) = 0
    rw [← pullback_comp]
    exact NativeSupportedStageCarrier.map_zero _ (outerInnerFace m hm F 1) (endpoint_mem m hm F 1) _ _
      (NativeInterleavedInnerFaces.suffix_one m hm F a b k E)

end
end Finsler.NativeIntervalGHTests
