module

public import Finsler.Loop.NativeThetaPowers

/-! The literal iterated primitive cut on the actual Theta powers
has the existing absolute UNIT as output. Its actual dual tests are
right-nested omega time cups ending in the evaluation top class.
This does NOT identify them with (GH power of omega) time-cup e;
that restricted comparison is the remaining high-power input. -/
@[expose] public section
namespace Finsler.NativeThetaPowerEvaluationTests
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

def test (m : ℕ) : (r : ℕ) → cohomologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r)
  | 0 => MeridianThetaCutCoefficient.testClass m
  | r + 1 => CanonicalGlobalTimeCup.product m m (NativeThetaPowers.degree m r)
      (MeridianLoopClass.H1TransgressionClass m) (test m r)

def foldCut (m : ℕ) : (r : ℕ) → homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r) →ₗ[ZMod 2]
    homologyZMod2 (Loops (m + 1)) (m + 1)
  | 0 => (CanonicalGlobalSelfCut.map m m (m + 1) (MeridianLoopClass.H1TransgressionClass m)).hom
  | r + 1 => (foldCut m r).comp
      (CanonicalGlobalSelfCut.map m m (NativeThetaPowers.degree m r)
        (MeridianLoopClass.H1TransgressionClass m)).hom

theorem test_pairing (m r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r)) :
    (kroneckerMap (Loops (m + 1)) (NativeThetaPowers.degree m r)).hom (test m r) z =
    (kroneckerMap (Loops (m + 1)) (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m)
      (foldCut m r z) := by
  induction r with
  | zero => exact (CanonicalGlobalSelfCut.pairing m m (m + 1)
      (MeridianLoopClass.H1TransgressionClass m) (MeridianThetaCutCoefficient.evaluationClass m) z).symm
  | succ r ih =>
    exact (CanonicalGlobalSelfCut.pairing m m (NativeThetaPowers.degree m r)
      (MeridianLoopClass.H1TransgressionClass m) (test m r) z).symm.trans (ih _)

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem fold_fullPower (r : ℕ) :
    foldCut m r (NativeThetaPowers.fullPower m hm F P v₀ r) =
      MeridianThetaCutCoefficient.cutTheta m (by omega) P v₀ := by
  induction r with
  | zero => exact congrArg (CanonicalGlobalSelfCut.map m m (m + 1)
      (MeridianLoopClass.H1TransgressionClass m)).hom (NativeThetaPowers.full_zero m hm F P v₀)
  | succ r ih =>
    change foldCut m r ((CanonicalGlobalSelfCut.map m m (NativeThetaPowers.degree m r)
      (MeridianLoopClass.H1TransgressionClass m)).hom
        (NativeThetaPowers.fullPower m hm F P v₀ (r + 1))) = _
    rw [NativeThetaPowers.full_succ_cut]
    exact ih

theorem fold_existing_UNIT (r : ℕ) :
    (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
      (foldCut m r (NativeThetaPowers.fullPower m hm F P v₀ r)) =
        AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) := by
  rw [fold_fullPower]
  exact NativeConstantUnitFromPathMV.original_UNIT m hm P v₀

theorem test_pairing_one (r : ℕ) :
    (kroneckerMap (Loops (m + 1)) (NativeThetaPowers.degree m r)).hom (test m r)
      (NativeThetaPowers.fullPower m hm F P v₀ r) = 1 := by
  rw [test_pairing, fold_fullPower]
  exact NativeThetaCoefficientOne.cut_pairing_one m (by omega) P v₀

include hm F P v₀ in
theorem test_ne_zero (r : ℕ) : test m r ≠ 0 := by
  intro hz
  have hp := test_pairing_one m hm F P v₀ r
  rw [hz, map_zero, LinearMap.zero_apply] at hp
  exact zero_ne_one hp

end
end Finsler.NativeThetaPowerEvaluationTests
