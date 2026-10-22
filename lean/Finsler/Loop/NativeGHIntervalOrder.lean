module

public import Finsler.Loop.NativeIntervalGHTests

/-! Discharge every near-test hypothesis of the actual cap/interval
interchange using BOTH original interleaved GH/evaluation tests.
The final evaluation is only assumed closed, never zero at endpoints.
The SAME correction vanishes at both ORIGINAL outer time endpoints. -/
@[expose] public section
namespace Finsler.NativeGHIntervalOrder
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SupportedCapNaturality
open Finsler.SmallChainCarrier Finsler.NativeIntervalGHTests
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (a b k : ℕ)
  (E : singularCochainGroup (ZMod 2) (Loops (m + 1)) k) (side : Bool)

def primitive : singularCochainGroup (ZMod 2) (base m) (m + index m a b k side) :=
  NativeSupportedIntervalOrder.primitive m (𝟙 (base m))
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (index m a b k side)
    (test m hm F a b k E side)

def before : singularCochainGroup (ZMod 2) (base m) (m + index m a b k side + 1) :=
  NativeSupportedIntervalOrder.before m (𝟙 (base m))
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (index m a b k side)
    (test m hm F a b k E side)

def after : singularCochainGroup (ZMod 2) (base m) (m + index m a b k side + 1) :=
  NativeSupportedIntervalOrder.after m (𝟙 (base m))
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (index m a b k side)
    (test m hm F a b k E side)

theorem boundary (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0) :
    cochainCoboundary (ZMod 2) (base m) (m + index m a b k side) (primitive m hm F a b k E side) =
      before m hm F a b k E side - after m hm F a b k E side :=
  NativeSupportedIntervalOrder.boundary m (𝟙 (base m))
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (index m a b k side)
    (test m hm F a b k E side) (test_closed m hm F a b k E side hE)
    (test_zero m hm F a b k E side) (test_one m hm F a b k E side)

theorem before_original : CochainDegreeTransport.pre (base m)
    (show m + index m a b k side + 1 = (m + 1) + index m a b k side by omega)
      ((NativeOrderedDoubleCutSupported.operation (𝟙 (base m)) (by omega)
        (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
        (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)).component (index m a b k side) ≫
        TimeTriangleSplit.interval (TopCat.of (near m hm F)) (index m a b k side) ≫ test m hm F a b k E side) =
      before m hm F a b k E side :=
  NativeSupportedIntervalOrder.before_original m (𝟙 (base m)) _ _ _ _

theorem after_original : TimeTriangleSplit.interval (base m) (m + index m a b k side + 1) ≫
    CochainDegreeTransport.pre (RightIntervalCochain.space (base m))
      (show m + index m a b k side + 1 + 1 = (m + 1) + (index m a b k side + 1) by omega)
      ((NativeOrderedDoubleCutSupported.operation (SupportedIntervalProduct.project (base m) ≫ 𝟙 (base m))
        (by omega) (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
        (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F)).component (index m a b k side + 1) ≫
        cochainPullback (SupportedIntervalProduct.nearOut (base m) (near m hm F)) _
          (test m hm F a b k E side)) = after m hm F a b k E side :=
  NativeSupportedIntervalOrder.after_original m (𝟙 (base m)) _ _ _ _

theorem primitive_endpoint (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SelfCutThomCocycle.atTime (m + 1) t) (m + index m a b k side)
      (primitive m hm F a b k E side) = 0 := by
  apply NativeSupportedStageCarrier.map_zero _ (SelfCutEndpoints.timeSlice (m + 1) t) (fun _ => rfl)
  apply NativeSupportedIntervalOrder.primitive_parameter_time_zero m (𝟙 (base m))
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (index m a b k side)
    (test m hm F a b k E side) (SelfCutEndpoints.timeSlice (m + 1) t) t (fun _ h => h)
  rcases ht with rfl | rfl
  · exact NormalizedSelfCut.time_zero _ _ _
  · exact NormalizedSelfCut.time_one _ _ _

theorem cycle_values_eq (hE : cochainCoboundary (ZMod 2) (Loops (m + 1)) k E = 0)
    (c : coeff ⟶ (chains (base m)).X (m + index m a b k side + 1))
    (hc : c ≫ (chains (base m)).d (m + index m a b k side + 1) (m + index m a b k side) = 0) :
    c ≫ before m hm F a b k E side = c ≫ after m hm F a b k E side :=
  NativeSupportedIntervalOrder.cycle_values_eq m (𝟙 (base m))
    (NativeOrderedDoubleCutSupported.thomRadius_pos m hm F)
    (NativeOrderedDoubleCutSupported.thomRadius_lt m hm F) (index m a b k side)
    (test m hm F a b k E side) (test_closed m hm F a b k E side hE)
    (test_zero m hm F a b k E side) (test_one m hm F a b k E side) c hc

end
end Finsler.NativeGHIntervalOrder
