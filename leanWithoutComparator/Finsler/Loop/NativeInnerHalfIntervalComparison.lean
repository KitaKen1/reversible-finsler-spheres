module

public import Finsler.Loop.IntervalHalfScalarComparison
public import Finsler.Loop.NativeInnerFullClock

/-! The full interval and the SAME original raw-half interval differ
by the actual affine triangle primitive. The complementary arc half
is proved zero; no cycle condition is imposed on the near-tube input. -/
@[expose] public section
namespace Finsler.NativeInnerHalfIntervalComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeIntervalGHTests Finsler.NativeInnerIntervalComparison
open Finsler.NativeInnerFullClock (tube space)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

def fullTest (side : Bool) : singularCochainGroup (ZMod 2) (space m hm F) (lowDegree m a b k side + 2) :=
  CochainDegreeTransport.pre (space m hm F) (congrArg (fun n => n + 1) (low_degree m hm a b k side))
    (NativeInnerFullClock.test m hm F a b k E side)

theorem full_closed (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (space m hm F) (lowDegree m a b k side + 2) (fullTest m hm F a b k E side) = 0 :=
  CochainDegreeTransport.closed _ _ _ (NativeInnerFullClock.test_closed m hm F a b k E side hE)

theorem half_original (side : Bool) : cochainPullback
    (tube m hm F ◁ IntervalHalfScalarComparison.halfMap side) (lowDegree m a b k side + 2)
    (fullTest m hm F a b k E side) = tubeOriginal m hm F a b k E side := by
  unfold fullTest
  rw [← NormalizedCutScalarPullback.pre_pullback]
  cases side with
  | false => rw [show IntervalHalfScalarComparison.halfMap false = IntervalTriangle.firstMap from rfl,
      NativeInnerFullClock.prefix_test_half]; rfl
  | true => rw [show IntervalHalfScalarComparison.halfMap true = IntervalTriangle.secondMap from rfl,
      NativeInnerFullClock.suffix_test_half]; rfl

theorem other_half_zero (side : Bool) : cochainPullback
    (tube m hm F ◁ IntervalHalfScalarComparison.halfMap (!side)) (lowDegree m a b k side + 2)
    (fullTest m hm F a b k E side) = 0 := by
  apply NativeSequentialGHGlobalComparison.pullback_pre_zero
  cases side with
  | false => exact NativeInnerFullClock.prefix_test_arc_zero m hm F a b k E
  | true => exact NativeInnerFullClock.suffix_test_arc_zero m hm F a b k E

def primitive (side : Bool) := IntervalHalfScalarComparison.primitive (tube m hm F)
  (lowDegree m a b k side) (fullTest m hm F a b k E side)

def fullValue (side : Bool) := IntervalHalfScalarComparison.value (tube m hm F)
  (lowDegree m a b k side) (fullTest m hm F a b k E side)

def halfValue (side : Bool) := RightIntervalFullCoboundary.integrate (tube m hm F)
  (lowDegree m a b k side + 1) (tubeOriginal m hm F a b k E side)

theorem boundary (side : Bool) (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (tube m hm F) (lowDegree m a b k side) (primitive m hm F a b k E side) =
      fullValue m hm F a b k E side - halfValue m hm F a b k E side := by
  have h := IntervalHalfScalarComparison.boundary_one_half (tube m hm F) (lowDegree m a b k side)
    (fullTest m hm F a b k E side) (full_closed m hm F a b k E side hE) side (other_half_zero m hm F a b k E side)
  rw [IntervalHalfScalarComparison.halfValue, half_original] at h
  exact h

end
end Finsler.NativeInnerHalfIntervalComparison
