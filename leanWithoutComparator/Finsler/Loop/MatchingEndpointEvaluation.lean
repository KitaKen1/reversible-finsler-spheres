module

public import Finsler.Loop.MatchingZeroEndpointRepresentatives

/-! The real retained matching H1 family evaluates on the original
meridian. Its two time faces evaluate at the two different poles. -/
@[expose] public section
namespace Finsler.MatchingEndpointEvaluation
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily
open Finsler.CochainComparison Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def retainedAt {n : ℕ} (P : Sphere n) (v₀ : equator P) (t : ClosedInterval) :
    MatchingRelativeOutputEndpointTrace.source P ⟶ Loops n :=
  DoubleRelativeTimeCylinder.atTime (MatchingRelativeOutputEndpointTrace.source P) t ≫
    MatchingRetainedOutputPrimitive.retainedH1 P v₀ 1

theorem evaluation {n : ℕ} (P : Sphere n) (v₀ : equator P) (t : ClosedInterval)
    (z : MatchingRelativeOutputEndpointTrace.source P) :
    BorelEvaluation.fullEval n (FullLoopModel.insert n (retainedAt P v₀ t z)) = meridian P z.1 t := by
  have he := ConcreteCategory.congr_hom (ContinuousLoopModel.evaluation_square n)
    (retainedAt P v₀ t z)
  have hc := ConcreteCategory.congr_hom
    (MatchingRetainedOutputPrimitive.ordinary_comparison P v₀ 1) (t, z)
  calc
    BorelEvaluation.fullEval n (FullLoopModel.insert n (retainedAt P v₀ t z)) =
        ContinuousLoopModel.evaluation n (ContinuousLoopModel.inclusion n (retainedAt P v₀ t z)) := he.symm
    _ = NativeMatchingRetainedFactors.retainedMap P v₀ 1 (t, z) 0 :=
      congrArg (ContinuousLoopModel.evaluation n) hc
    _ = meridian P z.1 t := NativeMatchingRetainedFactors.retained_evaluation P v₀ 1 (t, z)

theorem zero_evaluation {n : ℕ} (P : Sphere n) (v₀ : equator P)
    (z : MatchingRelativeOutputEndpointTrace.source P) :
    BorelEvaluation.fullEval n (FullLoopModel.insert n (retainedAt P v₀ 0 z)) = P := by
  rw [evaluation]
  exact (meridian P z.1).source

theorem one_evaluation {n : ℕ} (P : Sphere n) (v₀ : equator P)
    (z : MatchingRelativeOutputEndpointTrace.source P) :
    BorelEvaluation.fullEval n (FullLoopModel.insert n (retainedAt P v₀ 1 z)) = antipode P := by
  rw [evaluation]
  exact (meridian P z.1).target

end
end Finsler.MatchingEndpointEvaluation
