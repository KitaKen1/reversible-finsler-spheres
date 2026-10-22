module

public import Finsler.Loop.NativeGHProductRawAlignment
public import Finsler.Loop.TwoTimeSquareCoordinates
public import Finsler.Loop.SingularTimeDoubleNaturality
public import Finsler.Loop.CanonicalIntervalChainBoundary

/-! The SAME Stage108 raw interleaved cochains are closed and vanish
at the two ORIGINAL first-time endpoints. Pulling to the actual
product-time model discharges the non-cycle interval boundary terms. -/
@[expose] public section
namespace Finsler.NativeTimeSquareTests
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests Finsler.NativeGHProductPullback
open Finsler.NativeGHProductRawAlignment (squareDegree stage108 rawInterleaved)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

theorem raw_degree (m : ℕ) (hm : 2 ≤ m) (a b k : ℕ) (side : Bool) :
    squareDegree m a b k + 3 = (m + 1) + (index m a b k side + 1) := by
  have h := NativeGHProductRawAlignment.input_degree m hm a b k side
  omega

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)

theorem stage108_raw : stage108 m hm F a b k E side = CochainDegreeTransport.pre (raw m)
    (raw_degree m hm a b k side) (rawInterleaved m hm F a b k E side) := by
  cases side <;> rfl

theorem stage108_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (raw m) (squareDegree m a b k + 3) (stage108 m hm F a b k E side) = 0 := by
  rw [stage108_raw]
  apply CochainDegreeTransport.closed
  exact DegreeLoweringCochainPullback.closed (NativeSequentialSupportedStages.firstOperation m hm F)
    (index m a b k side + 1) (rawTest m hm F a b k E side) (rawTest_closed m hm F a b k E side hE)

theorem stage108_outer_endpoint (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SupportedCap.subspaceMap (raw m) (NativeSequentialTimeFaces.outerFace (m + 1) t))
      (squareDegree m a b k + 3) (stage108 m hm F a b k E side) = 0 := by
  rw [stage108_raw]
  apply NativeSequentialGHGlobalComparison.pullback_pre_zero
  have h := congrArg (fun f => f ≫ rawTest m hm F a b k E side)
    (NativeSequentialTimeFaces.first_endpoint m hm F t ht (index m a b k side + 1))
  simp only [Category.assoc, zero_comp] at h
  exact h

def test : singularCochainGroup (ZMod 2)
    (Loops (m + 1) ⊗ TopCat.of (IntervalSobolev.ClosedInterval × TopCat.I.{0})) (squareDegree m a b k + 3) :=
  cochainPullback (TwoTimeSquareCoordinates.rawModel (m + 1)) _ (stage108 m hm F a b k E side)

theorem test_closed (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) _ (squareDegree m a b k + 3) (test m hm F a b k E side) = 0 :=
  pullback_closed _ _ _ (stage108_closed m hm F a b k E side hE)

theorem test_endpoint (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (Loops (m + 1) ◁ SingularTimeDoubleNaturality.timeMap (CanonicalIntervalChainBoundary.endpoint t))
      (squareDegree m a b k + 3) (test m hm F a b k E side) = 0 := by
  unfold test
  rw [← pullback_comp]
  exact NativeSupportedStageCarrier.map_zero _ (NativeSequentialTimeFaces.outerFace (m + 1) t) (fun _ => rfl) _ _
    (stage108_outer_endpoint m hm F a b k E side t ht)

end
end Finsler.NativeTimeSquareTests
