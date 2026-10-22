module

public import Finsler.Loop.NativeThetaCoefficientOne
public import Finsler.Loop.NativeThetaLengthCut

/-! The same ORIGINAL Theta and cut are detected in the ACTUAL
strict length subspaces of EVERY genuine reversible metric. This
uses the existing finite-family bound and L=0; no positive HR saving
or bound uniform over powers is asserted. -/
@[expose] public section
namespace Finsler.NativeFilteredThetaDetection
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.MeridianLoopFamily Finsler.CochainComparison
open Finsler.BorelLoop Finsler.StrictLengthEnergyBridge
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 1 ≤ m) (F : ReversibleMetric (m + 1)) (P : Sphere (m + 1)) (v₀ : equator P)

theorem theta_ne_zero : NativeThetaLengthCut.theta m hm F P v₀ ≠ 0 := by
  intro hz
  have he := NativeThetaLengthCut.theta_full m hm F P v₀
  rw [hz, map_zero] at he
  exact NativeThetaCoefficientOne.H1Theta_ne_zero m hm P v₀ he.symm

theorem input_ne_zero : NativeThetaLengthCut.input m hm F P v₀ ≠ 0 := by
  intro hz
  have he := NativeThetaLengthCut.input_full m hm F P v₀
  rw [hz, map_zero] at he
  exact NativeThetaCoefficientOne.thetaInput_ne_zero m hm P v₀ he.symm

theorem input_pairing_one :
    (kroneckerMap (lengthSpace F (NativeThetaLengthCut.bound F P v₀)) ((m + m) + (m + 1))).hom
      ((cohPullback (LengthFilteredLoopRotation.full F (NativeThetaLengthCut.bound F P v₀)) ((m + m) + (m + 1))).hom
        (MeridianThetaCutCoefficient.testClass m)) (NativeThetaLengthCut.input m hm F P v₀) = 1 := by
  rw [kroneckerMap_naturality_apply]
  change (kroneckerMap _ ((m + m) + (m + 1))).hom (MeridianThetaCutCoefficient.testClass m)
    ((homologyPushZMod2 (LengthFilteredLoopRotation.full F (NativeThetaLengthCut.bound F P v₀)) ((m + m) + (m + 1))).hom
      (NativeThetaLengthCut.input m hm F P v₀)) = 1
  rw [NativeThetaLengthCut.input_full]
  exact NativeThetaCoefficientOne.coefficient_one m hm P v₀

theorem cut_ne_zero {ε : ℝ} (hε : 0 < ε) : NativeThetaLengthCut.cut m hm F P v₀ hε ≠ 0 := by
  intro hz
  have he := NativeThetaLengthCut.cut_full m hm F P v₀ hε
  rw [hz, map_zero] at he
  exact NativeThetaCoefficientOne.cutTheta_ne_zero m hm P v₀ he.symm

theorem cut_pairing_one {ε : ℝ} (hε : 0 < ε) :
    (kroneckerMap (TopCat.of (SelfCutOscillation.short F (NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε))) (m + 1)).hom
      ((cohPullback (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F (NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε))) (m + 1)).hom
        (MeridianThetaCutCoefficient.evaluationClass m)) (NativeThetaLengthCut.cut m hm F P v₀ hε) = 1 := by
  rw [kroneckerMap_naturality_apply]
  change (kroneckerMap _ (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m)
    ((homologyPushZMod2 (SupportedCap.subspaceMap (Loops (m + 1)) (SelfCutOscillation.short F (NativeThetaLengthCut.bound F P v₀ - 0 + 3 * ε))) (m + 1)).hom
      (NativeThetaLengthCut.cut m hm F P v₀ hε)) = 1
  rw [NativeThetaLengthCut.cut_full]
  exact NativeThetaCoefficientOne.cut_pairing_one m hm P v₀

end
end Finsler.NativeFilteredThetaDetection
