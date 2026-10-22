module

public import Finsler.Loop.PathSphereHomologyGap
public import Finsler.Loop.NativeEvaluationOrdinaryBasedGap

/-! The EXISTING original UNIT, with all native geometric inputs
and dimensions n>=3, supplied by the actual based-path homology gap.
This does not assert GH powers, full UF, positive HR or MAIN. -/
@[expose] public section
namespace Finsler.NativeConstantUnitFromPathMV
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem original_UNIT (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeConstantUnitDefect.cutFull m (by omega) P v₀ =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  NativeEvaluationOrdinaryBasedGap.original_UNIT_of_path_gap m hm P v₀
    (PathSphereHomologyGap.path_top_zero m hm P P v₀)

theorem original_relativeCut_zero (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    NativeConstantUnitDefect.relativeCut m (by omega) P v₀ = 0 :=
  NativeEvaluationOrdinaryBasedGap.original_relativeCut_zero_of_path_gap m hm P v₀
    (PathSphereHomologyGap.path_top_zero m hm P P v₀)

theorem full_evaluation_injective (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    Function.Injective (homologyPushZMod2 (BorelEvaluation.fullEval (m + 1)) (m + 1)).hom :=
  NativeEvaluationOrdinaryBasedGap.evaluation_injective_of_path_gap m (by omega) P
    (PathSphereHomologyGap.path_top_zero m hm P P v₀)

end
end Finsler.NativeConstantUnitFromPathMV
