module

public import Finsler.Loop.H1BasedPathLift
public import Finsler.Loop.NativeEvaluationConnectedFiber

/-! The original overlap test is now unconditional. The original
UNIT and original relativeCutZERO need only ONE actual degree-n
homology-zero input on the genuine based strong-H1 loop space. -/
@[expose] public section
namespace Finsler.NativeEvaluationBasedGap
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.H1LocalFiber (based)
open Finsler.MeridianLoopFamily Finsler.NativeEvaluationMayerVietoris
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem joint_overlap (m : ℕ) (hm : 1 ≤ m) (y : Sphere (m + 1))
    (z : homologyZMod2 (overlap y) m)
    (he : (homologyPushZMod2 (overlapEvaluation y) m).hom z = 0)
    (hp : (toPatches y m).hom z = 0) : z = 0 := by
  let := H1BasedPathLift.pathConnected (by omega) y
  exact NativeEvaluationConnectedFiber.joint_overlap m y z he hp

theorem evaluation_injective_of_based_gap (m : ℕ) (hm : 1 ≤ m) (y : Sphere (m + 1))
    (hN : IsZero (homologyZMod2 (TopCat.of (based y)) (m + 1))) :
    Function.Injective (homologyPushZMod2 (BorelEvaluation.fullEval (m + 1)) (m + 1)).hom :=
  evaluation_injective_of_actual_cover_obligations y m
    (NativeEvaluationPatchGap.fromPatches_zero_of_based y (m + 1) hN
      (H1BasedFiberTransport.homology_zero_transport y (antipode y) (m + 1) hN)) (joint_overlap m hm y)

theorem original_UNIT_of_based_gap (m : ℕ) (hm : 2 ≤ m) (y : Sphere (m + 1)) (v₀ : equator y)
    (hN : IsZero (homologyZMod2 (TopCat.of (based y)) (m + 1))) :
    NativeConstantUnitDefect.cutFull m (by omega) y v₀ =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) := by
  let := H1BasedPathLift.pathConnected (by omega) y
  exact NativeEvaluationConnectedFiber.original_UNIT_of_based_gap_and_pathConnected m hm y v₀ hN

theorem original_relativeCut_zero_of_based_gap (m : ℕ) (hm : 2 ≤ m)
    (y : Sphere (m + 1)) (v₀ : equator y)
    (hN : IsZero (homologyZMod2 (TopCat.of (based y)) (m + 1))) :
    NativeConstantUnitDefect.relativeCut m (by omega) y v₀ = 0 := by
  let := H1BasedPathLift.pathConnected (by omega) y
  exact NativeEvaluationConnectedFiber.original_relativeCut_zero_of_based_gap_and_pathConnected m hm y v₀ hN

end
end Finsler.NativeEvaluationBasedGap
