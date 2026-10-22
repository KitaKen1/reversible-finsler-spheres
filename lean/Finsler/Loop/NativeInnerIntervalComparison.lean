module

public import Finsler.Loop.NativeInnerRetainedComparison
public import Finsler.Loop.RightIntervalFullCoboundary
public import Finsler.Loop.NativeGHRawTwoTimeComparison
public import Finsler.Topology.DiagonalCutSwap

/-! Integrate BOTH actual inner-cap pullback corrections through the
same original near-tube interval. Both endpoint evaluations are retained
in the corrected original value; no inserted chain is assumed a cycle. -/
@[expose] public section
namespace Finsler.NativeInnerIntervalComparison
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def rawPrimitive (side : Bool) : singularCochainGroup (ZMod 2) (NativeSequentialSupportedStages.outerSpace m hm F)
    (index m a b k side) := match side with
  | false => NativeInnerRetainedComparison.prefixPrimitive m hm F a b k E
  | true => NativeInnerRetainedComparison.suffixPrimitive m hm F a b k E

def rawOriginal (side : Bool) : singularCochainGroup (ZMod 2) (NativeSequentialSupportedStages.outerSpace m hm F)
    (index m a b k side + 1) := match side with
  | false => NativeInnerRetainedComparison.prefixOriginal m hm F a b k E
  | true => NativeInnerRetainedComparison.suffixOriginal m hm F a b k E

theorem raw_boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (NativeSequentialSupportedStages.outerSpace m hm F) (index m a b k side)
      (rawPrimitive m hm F a b k E side) = NativeGHProductPullback.rawTest m hm F a b k E side - rawOriginal m hm F a b k E side := by
  cases side with
  | false => exact NativeInnerRetainedComparison.prefix_boundary m hm F a b k E hE
  | true => exact NativeInnerRetainedComparison.suffix_boundary m hm F a b k E hE

abbrev lowDegree (side : Bool) := index m a b k side - 1

include hm in
theorem index_pos (side : Bool) : 1 ≤ index m a b k side := by
  cases side <;> dsimp [index, NativePrefixTestOrder.index, NativeSuffixTestOrder.index] <;> omega

include hm in
theorem low_degree (side : Bool) : lowDegree m a b k side + 1 = index m a b k side :=
  Nat.sub_add_cancel (index_pos m hm a b k side)

def tubePrimitive (side : Bool) := CochainDegreeTransport.pre
  (RightIntervalCochain.space (TopCat.of (near m hm F))) (low_degree m hm a b k side)
    (cochainPullback (rawNear m hm F) (index m a b k side) (rawPrimitive m hm F a b k E side))

def tubeOriginal (side : Bool) := CochainDegreeTransport.pre
  (RightIntervalCochain.space (TopCat.of (near m hm F))) (congrArg (fun n => n + 1) (low_degree m hm a b k side))
    (cochainPullback (rawNear m hm F) (index m a b k side + 1) (rawOriginal m hm F a b k E side))

def tubeBefore (side : Bool) := CochainDegreeTransport.pre
  (RightIntervalCochain.space (TopCat.of (near m hm F))) (congrArg (fun n => n + 1) (low_degree m hm a b k side))
    (test m hm F a b k E side)

theorem tube_boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (RightIntervalCochain.space (TopCat.of (near m hm F)))
      (lowDegree m a b k side + 1) (tubePrimitive m hm F a b k E side) =
      tubeBefore m hm F a b k E side - tubeOriginal m hm F a b k E side := by
  unfold tubePrimitive
  rw [NativeRawOriginalScalarReduction.pre_boundary, DiagonalCutSwap.pullback_coboundary,
    raw_boundary m hm F a b k E side hE, DiagonalCutSwap.pullback_sub,
    NativeRawOriginalScalarReduction.pre_sub, ← NativeGHProductPullback.test_original]
  rfl

def primitive (side : Bool) := RightIntervalCoboundary.primitive (TopCat.of (near m hm F))
  (lowDegree m a b k side) (tubePrimitive m hm F a b k E side)

def correctedOriginal (side : Bool) := RightIntervalFullCoboundary.corrected (TopCat.of (near m hm F))
  (lowDegree m a b k side) (tubePrimitive m hm F a b k E side) (tubeOriginal m hm F a b k E side)

def before (side : Bool) := RightIntervalFullCoboundary.integrate (TopCat.of (near m hm F))
  (lowDegree m a b k side + 1) (tubeBefore m hm F a b k E side)

theorem boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (TopCat.of (near m hm F)) (lowDegree m a b k side)
      (primitive m hm F a b k E side) = before m hm F a b k E side - correctedOriginal m hm F a b k E side :=
  RightIntervalFullCoboundary.comparison _ _ _ _ _ (tube_boundary m hm F a b k E side hE)

theorem before_original (side : Bool) : before m hm F a b k E side =
    CochainDegreeTransport.pre (TopCat.of (near m hm F)) (low_degree m hm a b k side)
      (TimeTriangleSplit.interval (TopCat.of (near m hm F)) (index m a b k side) ≫ test m hm F a b k E side) :=
  (NativeGHRawTwoTimeComparison.interval_pre _ (low_degree m hm a b k side) _).symm

end
end Finsler.NativeInnerIntervalComparison
