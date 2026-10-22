module

public import Finsler.Loop.DoubleCapThomCarrier
public import Finsler.Loop.NativeOrderedScalarPullback
public import Finsler.Loop.NativeSupportedStageCarrier

/-! The two actual exterior endpoint faces of the ordered source.
Either original normalized Thom factor vanishes, so the SAME ordered
cup and double-cap subdivision primitive vanish on each face separately. -/
@[expose] public section
namespace Finsler.NativeOrderedEndpointCarrier
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.NativeOrderedDoubleCapCommon
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

def endpoint (last : Bool) : Set (source m) := if last then
  {z | (NativeOrderedDoubleCutGeometry.lastParameter (m + 1) z).1 = 1} else
  {z | (NativeOrderedDoubleCutGeometry.firstParameter (m + 1) z).1 = 0}

theorem thom_zero (last : Bool) :
    cochainPullback (SupportedCap.subspaceMap (source m) (endpoint m last)) (m + 1) (firstThom m hm F) = 0 ∨
    cochainPullback (SupportedCap.subspaceMap (source m) (endpoint m last)) (m + 1) (lastThom m hm F) = 0 := by
  cases last
  · apply Or.inl
    exact NativeSupportedStageCarrier.parameter_time_zero _ _ _ (endpoint m false) 0
      (fun _ h => h) (NormalizedSelfCut.time_zero _ _ _)
  · apply Or.inr
    exact NativeSupportedStageCarrier.parameter_time_zero _ _ _ (endpoint m true) 1
      (fun _ h => h) (NormalizedSelfCut.time_one _ _ _)

theorem cup_zero (last : Bool) : cochainPullback (SupportedCap.subspaceMap (source m) (endpoint m last))
    ((m + 1) + m + 1) (NativeOrderedScalarPullback.thomCup m hm F) = 0 :=
  CupCapOrder.restriction_zero _ (m + 1) (m + 1) _ (by omega)
    (firstThom m hm F) (lastThom m hm F) (thom_zero m hm F last)

variable (a b k : ℕ) (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k)

theorem primitive_zero (last : Bool) : cochainPullback (SupportedCap.subspaceMap (source m) (endpoint m last))
    (index m a b k) (primitive m hm F a b k E) = 0 :=
  DoubleCapThomCarrier.primitive_zero (source m)
  (firstFar m hm F) (firstNear m hm F) (lastFar m hm F) (lastNear m hm F)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.far_open _ _) (NativeOrderedDoubleCutSupported.near_open _ _)
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (NativeOrderedDoubleCutSupported.cover _ (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F))
  (m + 1) m (testDegree m a b k) (firstThom m hm F) (lastThom m hm F)
  (first_supported m hm F) (last_supported m hm F) (test m hm F a b k E)
    (endpoint m last) (thom_zero m hm F last)

end
end Finsler.NativeOrderedEndpointCarrier
