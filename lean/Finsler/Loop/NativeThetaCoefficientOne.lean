module

public import Finsler.Loop.NativeSameLegSegmentZero

/-! The ORIGINAL GLOBAL coefficient is ONE with no auxiliary radius
premises. Consequently the actual original cutTheta and both H1 and
ordinary triple-meridian rotation Theta classes are NONZERO. This
does not identify the cut with the constant-loop UNIT or prove GH/HR/UF. -/
@[expose] public section
namespace Finsler.NativeThetaCoefficientOne
open CategoryTheory SphereOddDegree AlgebraicTopology
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

variable (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)

theorem coefficient_one : MeridianThetaCutCoefficient.coefficient m hm P v₀ = 1 :=
  NativeSameLegSegmentZero.coefficient_one_at_radii m hm P v₀
    (ρ := 1 / 32) (r := 1 / 16) (η := 1 / 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem cut_pairing_one : (kroneckerMap _ (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m)
    (MeridianThetaCutCoefficient.cutTheta m hm P v₀) = 1 :=
  (MeridianThetaCutCoefficient.cut_pairing m hm P v₀).trans (coefficient_one m hm P v₀)

theorem cut_evaluation_fundamental :
    (homologyPushZMod2 (MeridianThetaCutCoefficient.evaluation (m + 1)) (m + 1)).hom
      (MeridianThetaCutCoefficient.cutTheta m hm P v₀) = SphereUnitCandidate.fundamental (m + 1) (by omega) := by
  rw [MeridianThetaCutCoefficient.evaluation_fundamental_multiple, coefficient_one, one_smul]

theorem cutTheta_ne_zero : MeridianThetaCutCoefficient.cutTheta m hm P v₀ ≠ 0 := by
  intro hz
  have h := cut_pairing_one m hm P v₀
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem thetaInput_ne_zero : MeridianThetaCutCoefficient.thetaInput m hm P v₀ ≠ 0 := by
  intro hz
  have h := coefficient_one m hm P v₀
  unfold MeridianThetaCutCoefficient.coefficient at h
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem H1Theta_ne_zero : MeridianRotationClasses.H1Theta m hm P v₀ ≠ 0 := by
  intro hz
  apply thetaInput_ne_zero m hm P v₀
  unfold MeridianThetaCutCoefficient.thetaInput
  rw [hz, map_zero]

theorem ordinaryTheta_ne_zero : MeridianRotationClasses.ordinaryTheta m hm P v₀ ≠ 0 := by
  intro hz
  apply H1Theta_ne_zero m hm P v₀
  apply (ContinuousLoopHomologyEquivalence.homology (m + 1) (3 * m + 1)).injective
  rw [MeridianRotationClasses.inclusion_theta, hz, map_zero]

end
end Finsler.NativeThetaCoefficientOne
