module

public import Finsler.Loop.NativeDegreeNLoopHomology

/-! In the ACTUAL degree-n H1 loop homology, evaluation pairing ONE
is equivalent to the EXISTING absolute constant-loop UNIT, for n>=3.
This uses the proved actual evaluation injectivity and the real
sphere Kronecker class, without a residual rank hypothesis. -/
@[expose] public section
namespace Finsler.NativeEvaluationUnitCriterion
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop Finsler.BorelEvaluation
open Finsler.MeridianLoopFamily Finsler.SplitPairHomologyKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

theorem evaluation_scalar (m : ℕ) (z : homologyZMod2 (Loops (m + 1)) (m + 1)) :
    SphereTopClass.homologyEquiv (m + 1) (by omega)
      ((homologyPushZMod2 (MeridianThetaCutCoefficient.evaluation (m + 1)) (m + 1)).hom z) =
    (kroneckerMap (Loops (m + 1)) (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m) z := by
  have hn := congrArg (fun φ : homologyDualZMod2 (Loops (m + 1)) (m + 1) => φ z)
    (kroneckerMap_naturality_apply (MeridianThetaCutCoefficient.evaluation (m + 1)) (m + 1)
      (SphereTopClass.topClass (m + 1) (by omega)))
  have he := MeridianLoopClass.sphere_top_evaluation (m + 1) (by omega)
    ((homologyPushZMod2 (MeridianThetaCutCoefficient.evaluation (m + 1)) (m + 1)).hom z)
  exact he.symm.trans hn.symm

theorem unit_iff_pairing_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)
    (z : homologyZMod2 (Loops (m + 1)) (m + 1)) :
    (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom z =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) ↔
    (kroneckerMap (Loops (m + 1)) (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m) z = 1 := by
  have hu : SphereTopClass.homologyEquiv (m + 1) (by omega)
      ((homologyPushZMod2 (fullEval (m + 1)) (m + 1)).hom
        (AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega))) = 1 := by
    have he : (homologyPushZMod2 (fullEval (m + 1)) (m + 1)).hom
        (AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega)) =
      SphereUnitCandidate.fundamental (m + 1) (by omega) :=
      AbsoluteFilteredUnits.absolute_evaluation (m + 1) (by omega)
    rw [he]
    exact (SphereTopClass.homologyEquiv (m + 1) (by omega)).apply_symm_apply 1
  constructor
  · intro hz
    have he := congrArg (fun w => SphereTopClass.homologyEquiv (m + 1) (by omega)
      ((homologyPushZMod2 (fullEval (m + 1)) (m + 1)).hom w)) hz
    rw [push_comp_apply] at he
    exact (evaluation_scalar m z).symm.trans (he.trans hu)
  · intro hz
    apply NativeConstantUnitFromPathMV.full_evaluation_injective m hm P v₀
    apply (SphereTopClass.homologyEquiv (m + 1) (by omega)).injective
    rw [push_comp_apply]
    exact ((evaluation_scalar m z).trans hz).trans hu.symm

end
end Finsler.NativeEvaluationUnitCriterion
