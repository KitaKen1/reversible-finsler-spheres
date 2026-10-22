module

public import Finsler.Loop.BasedLoopHomologyInjection
public import Finsler.Loop.BasedLoopPathSpace
public import Finsler.Loop.NativeEvaluationBasedGap

/-! State the single remaining UNIT homology gap on Mathlib's
genuine based path-loop space. The H1 comparison is proved injective
in every degree and the ordinary based models are homeomorphic. -/
@[expose] public section
namespace Finsler.NativeEvaluationOrdinaryBasedGap
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.H1LocalFiber (based)
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem based_zero_of_path_zero {n : ℕ} (y : Sphere n) (q : ℕ)
    (h : IsZero (homologyZMod2 (BasedLoopPathSpace.space y) q)) :
    IsZero (homologyZMod2 (TopCat.of (based y)) q) :=
  BasedLoopHomologyInjection.zero_of_ordinary_zero y q (h.of_iso (BasedLoopPathSpace.homologyIso y q))

theorem evaluation_injective_of_path_gap (m : ℕ) (hm : 1 ≤ m) (y : Sphere (m + 1))
    (h : IsZero (homologyZMod2 (BasedLoopPathSpace.space y) (m + 1))) :
    Function.Injective (homologyPushZMod2 (BorelEvaluation.fullEval (m + 1)) (m + 1)).hom :=
  NativeEvaluationBasedGap.evaluation_injective_of_based_gap m hm y (based_zero_of_path_zero y (m + 1) h)

theorem original_UNIT_of_path_gap (m : ℕ) (hm : 2 ≤ m) (y : Sphere (m + 1)) (v₀ : equator y)
    (h : IsZero (homologyZMod2 (BasedLoopPathSpace.space y) (m + 1))) :
    NativeConstantUnitDefect.cutFull m (by omega) y v₀ =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  NativeEvaluationBasedGap.original_UNIT_of_based_gap m hm y v₀ (based_zero_of_path_zero y (m + 1) h)

theorem original_relativeCut_zero_of_path_gap (m : ℕ) (hm : 2 ≤ m)
    (y : Sphere (m + 1)) (v₀ : equator y)
    (h : IsZero (homologyZMod2 (BasedLoopPathSpace.space y) (m + 1))) :
    NativeConstantUnitDefect.relativeCut m (by omega) y v₀ = 0 :=
  NativeEvaluationBasedGap.original_relativeCut_zero_of_based_gap m hm y v₀ (based_zero_of_path_zero y (m + 1) h)

end
end Finsler.NativeEvaluationOrdinaryBasedGap
