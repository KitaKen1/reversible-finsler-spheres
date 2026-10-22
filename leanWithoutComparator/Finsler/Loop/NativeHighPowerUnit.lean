module

public import Finsler.Loop.NativeGHPowerTimeCupAssociativity
public import Finsler.Loop.NativeHighPowerUnitComparison

/-! The original SINGLE high-power UNIT on the SAME original Theta
powers. Restricted actual GH-power associativity identifies its dual
test with the existing iterated-primitive test, whose pairing is ONE.
No new high-power class, cut, input or unit is substituted. -/
@[expose] public section
namespace Finsler.NativeHighPowerUnit
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.NativeGHPowerTimeCupAssociativity
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

include hm F in
theorem test_succ (r : ℕ) : NativeHighPowerUnitComparison.ghEvaluationTest m (r + 1) =
    CanonicalGlobalTimeCup.product m m (NativeThetaPowers.degree m r)
      (MeridianLoopClass.H1TransgressionClass m) (NativeHighPowerUnitComparison.ghEvaluationTest m r) := by
  unfold NativeHighPowerUnitComparison.ghEvaluationTest
  rw [product_cast_right]
  exact associativity_at_degree m hm F 0 r (m + 1) (by omega)
    (MeridianThetaCutCoefficient.evaluationClass m) (NativeThetaPowers.degree m (r + 1))
    (NativeHighPowerUnitComparison.degree_match m (r + 1)).symm
    (congrArg (fun n => (m + m) + n) (NativeHighPowerUnitComparison.degree_match m r).symm)

include hm F in
theorem test_eq (r : ℕ) : NativeHighPowerUnitComparison.ghEvaluationTest m r =
    NativeThetaPowerEvaluationTests.test m r := by
  induction r with
  | zero => exact NativeHighPowerUnitComparison.zero_test_equality m
  | succ r ih => rw [test_succ m hm F r, ih]; rfl

variable (P : Sphere (m + 1)) (v₀ : equator P)

theorem scalar_one (r : ℕ) :
    (kroneckerMap (Loops (m + 1)) (NativeThetaPowers.degree m r)).hom
      (NativeHighPowerUnitComparison.ghEvaluationTest m r) (NativeThetaPowers.fullPower m hm F P v₀ r) = 1 := by
  rw [test_eq m hm F r]
  exact NativeThetaPowerEvaluationTests.test_pairing_one m hm F P v₀ r

theorem single_UNIT (r : ℕ) :
    (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom
      (NativeHighPowerUnitComparison.singleCut m hm F P v₀ r) =
        AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  NativeHighPowerUnitComparison.unit_of_test_equality m hm F P v₀ r (test_eq m hm F r)

theorem single_eq_iterated (r : ℕ) : NativeHighPowerUnitComparison.singleCut m hm F P v₀ r =
    NativeThetaPowerEvaluationTests.foldCut m r (NativeThetaPowers.fullPower m hm F P v₀ r) :=
  (NativeHighPowerUnitComparison.unit_iff_iterated_comparison m hm F P v₀ r).mp (single_UNIT m hm F P v₀ r)

end
end Finsler.NativeHighPowerUnit
