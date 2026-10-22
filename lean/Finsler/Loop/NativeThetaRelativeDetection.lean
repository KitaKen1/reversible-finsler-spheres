module

public import Finsler.Loop.NativeThetaCoefficientOne
public import Finsler.Loop.ConstantRelativePairing

/-! The ACTUAL original Theta input survives quotienting by constants.
Its detector is the genuine canonical time-cup test class with its
real high-degree relative lift. No rank/generator or UNIT is assumed. -/
@[expose] public section
namespace Finsler.NativeThetaRelativeDetection
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def testClass (m : ℕ) (hm : 1 ≤ m) : RelativeCup.cohomology (fullPair (m + 1)) ((m + m) + (m + 1)) :=
  ConstantRelativeLift.lift (m + 1) ((m + m) + (m + 1)) (by omega) (MeridianThetaCutCoefficient.testClass m)

def input (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    ((fullPair (m + 1)).singularHomology coeff ((m + m) + (m + 1)) : ModuleCat.{0} (ZMod 2)) :=
  ConstantRelativePairing.homologyToRelative (m + 1) ((m + m) + (m + 1))
    (MeridianThetaCutCoefficient.thetaInput m hm P v₀)

theorem test_absolute (m : ℕ) (hm : 1 ≤ m) :
    (relativeToPool (fullPair (m + 1)) ((m + m) + (m + 1))).hom (testClass m hm) =
      (FullLoopModel.cohomologyEquiv (m + 1) ((m + m) + (m + 1))) (MeridianThetaCutCoefficient.testClass m) :=
  ConstantRelativeLift.lift_spec (m + 1) ((m + m) + (m + 1)) (by omega) _

theorem pairing_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    RelativeKronecker.comparison (fullPair (m + 1)) ((m + m) + (m + 1)) (testClass m hm) (input m hm P v₀) = 1 := by
  unfold testClass input
  rw [ConstantRelativePairing.pairing]
  exact NativeThetaCoefficientOne.coefficient_one m hm P v₀

theorem input_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) : input m hm P v₀ ≠ 0 := by
  intro hz
  have h := pairing_one m hm P v₀
  rw [hz, map_zero] at h
  exact zero_ne_one h

theorem test_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) : testClass m hm ≠ 0 := by
  intro hz
  have h := pairing_one m hm P v₀
  rw [hz, map_zero, LinearMap.zero_apply] at h
  exact zero_ne_one h

end
end Finsler.NativeThetaRelativeDetection
