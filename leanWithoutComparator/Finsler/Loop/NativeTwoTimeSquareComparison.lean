module

public import Finsler.Loop.IntervalInsertedTimeComparison
public import Finsler.Loop.IntervalTensorSquare
public import Finsler.Loop.NativeTimeSquareTests
public import Finsler.Loop.NativeGHRawTwoTimeComparison

/-! BOTH original two-time insertions compared to the SAME canonical
Stage108 shuffle square, with an explicit source primitive. The actual
first-time endpoint hypotheses are proved by the original Thom cochain.
This does not yet identify the complete nested PrismSelfCut composite. -/
@[expose] public section
namespace Finsler.NativeTwoTimeSquareComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
open Finsler.NativeGHProductRawAlignment (squareDegree stage108)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)

def primitive := IntervalInsertedTimeComparison.primitive (Loops (m + 1)) (squareDegree m a b k)
  (NativeTimeSquareTests.test m hm F a b k E side)

def squareValue : singularCochainGroup (ZMod 2) (Loops (m + 1)) (squareDegree m a b k + 1) :=
  OrderedDoubleCutSquareChain.insertion (Loops (m + 1)) (squareDegree m a b k + 1) ≫
    (push (NativeRawTimeSquareBoundary.squareMap (m + 1))).f (squareDegree m a b k + 3) ≫
      stage108 m hm F a b k E side

theorem product_original : IntervalInsertedTimeComparison.productValue (Loops (m + 1)) (squareDegree m a b k)
    (NativeTimeSquareTests.test m hm F a b k E side) =
      NativeGHRawTwoTimeComparison.twoTimeStage108 m hm F a b k E side := by
  have hs : RightTensorInsertion.insert (chains (Loops (m + 1))) (chains TopCat.I)
      (squareDegree m a b k + 1) 1 CanonicalIntervalChainBoundary.intervalChain ≫
      (SmallRectangleCross.ambient (Loops (m + 1)) TopCat.I).f (squareDegree m a b k + 2) =
    TimeTriangleSplit.interval (Loops (m + 1)) (squareDegree m a b k + 1) := by
    rw [show SmallRectangleCross.ambient (Loops (m + 1)) TopCat.I = SingularRightBoundary.shuffle (Loops (m + 1)) TopCat.I from rfl,
      RightTensorInsertion.shuffle, CanonicalIntervalChainBoundary.intervalChain, SingularRightBoundary.rightChain_simplex]
    rfl
  unfold IntervalInsertedTimeComparison.productValue NativeTimeSquareTests.test
  rw [← Category.assoc _ ((SmallRectangleCross.ambient _ _).f _), hs]
  have h := congrArg (fun f => f ≫ stage108 m hm F a b k E side)
    (TwoTimeSquareCoordinates.original_two_time m (squareDegree m a b k + 1))
  simp only [Category.assoc] at h
  exact h

theorem tensor_square : IntervalInsertedTimeComparison.tensorValue (Loops (m + 1)) (squareDegree m a b k)
    (NativeTimeSquareTests.test m hm F a b k E side) = squareValue m hm F a b k E side := by
  unfold IntervalInsertedTimeComparison.tensorValue NativeTimeSquareTests.test
  rw [← TwoTimeSquareCoordinates.time_square, pullback_comp]
  have h := congrArg (fun f => f ≫ cochainPullback (NativeRawTimeSquareBoundary.squareMap (m + 1))
    (squareDegree m a b k + 3) (stage108 m hm F a b k E side))
    (IntervalTensorSquare.tensor_square (Loops (m + 1)) (squareDegree m a b k + 1))
  simp only [Category.assoc] at h
  exact h

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (squareDegree m a b k) (primitive m hm F a b k E side) =
      NativeGHRawTwoTimeComparison.twoTimeStage108 m hm F a b k E side - squareValue m hm F a b k E side := by
  have h := IntervalInsertedTimeComparison.boundary (Loops (m + 1)) (squareDegree m a b k)
    (NativeTimeSquareTests.test m hm F a b k E side) (NativeTimeSquareTests.test_closed m hm F a b k E side hE)
    (NativeTimeSquareTests.test_endpoint m hm F a b k E side 0 (Or.inl rfl))
    (NativeTimeSquareTests.test_endpoint m hm F a b k E side 1 (Or.inr rfl))
  rw [product_original, tensor_square] at h
  exact h

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (Loops (m + 1))).X (squareDegree m a b k + 1))
    (hc : c ≫ (chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) = 0) :
    c ≫ NativeGHRawTwoTimeComparison.twoTimeStage108 m hm F a b k E side = c ≫ squareValue m hm F a b k E side := by
  have h := congrArg (fun f => c ≫ f) (boundary m hm F a b k E side hE)
  change c ≫ ((chains (Loops (m + 1))).d (squareDegree m a b k + 1) (squareDegree m a b k) ≫
    primitive m hm F a b k E side) = _ at h
  rw [← Category.assoc c, hc, zero_comp, Preadditive.comp_sub] at h
  exact sub_eq_zero.mp h.symm

end
end Finsler.NativeTwoTimeSquareComparison
