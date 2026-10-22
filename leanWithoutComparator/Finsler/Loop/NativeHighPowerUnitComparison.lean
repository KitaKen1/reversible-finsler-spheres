module

public import Finsler.Loop.NativeThetaPowerEvaluationTests
public import Finsler.Loop.NativeEvaluationUnitCriterion
public import Finsler.Loop.NativeGHPowers

/-! The EXACT remaining high-power UNIT comparison for the SAME
actual GH power, SAME actual Theta-product power and SAME global cut.
It is equivalent to ONE scalar equality on the actual Theta power;
general GH associativity is stronger than this required input.
The scalar comparison is NOT proved or installed as an axiom here. -/
@[expose] public section
namespace Finsler.NativeHighPowerUnitComparison
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.SplitPairHomologyKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem degree_match (m r : ℕ) : NativeThetaPowers.degree m r =
    (m + NativeGHPowers.degree m r) + (m + 1) := by
  rw [NativeThetaPowers.degree_formula, NativeGHPowers.degree_formula]
  ring

theorem pairing_cast (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (a : cohomologyZMod2 X j) (z : homologyZMod2 X i) :
    (kroneckerMap X i).hom (CupUnit.absoluteCast X h.symm a) z =
      (kroneckerMap X j).hom a ((eqToHom (congrArg (homologyZMod2 X) h)).hom z) := by
  subst j
  simp only [CupUnit.absoluteCast, eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply]

def ghEvaluationTest (m r : ℕ) :
    cohomologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r) :=
  CupUnit.absoluteCast (Loops (m + 1)) (degree_match m r).symm
    (CanonicalGlobalTimeCup.product m (NativeGHPowers.degree m r) (m + 1)
      (NativeGHPowers.power m r) (MeridianThetaCutCoefficient.evaluationClass m))

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

def alignedInput (r : ℕ) :
    homologyZMod2 (Loops (m + 1)) ((m + NativeGHPowers.degree m r) + (m + 1)) :=
  (eqToHom (congrArg (homologyZMod2 (Loops (m + 1))) (degree_match m r))).hom
    (NativeThetaPowers.fullPower m hm F P v₀ r)

def singleCut (r : ℕ) : homologyZMod2 (Loops (m + 1)) (m + 1) :=
  (CanonicalGlobalSelfCut.map m (NativeGHPowers.degree m r) (m + 1)
    (NativeGHPowers.power m r)).hom (alignedInput m hm F P v₀ r)

theorem single_cut_pairing (r : ℕ) :
    (kroneckerMap (Loops (m + 1)) (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m)
      (singleCut m hm F P v₀ r) =
    (kroneckerMap (Loops (m + 1)) (NativeThetaPowers.degree m r)).hom (ghEvaluationTest m r)
      (NativeThetaPowers.fullPower m hm F P v₀ r) :=
  (CanonicalGlobalSelfCut.pairing m (NativeGHPowers.degree m r) (m + 1)
    (NativeGHPowers.power m r) (MeridianThetaCutCoefficient.evaluationClass m)
    (alignedInput m hm F P v₀ r)).trans
      (pairing_cast (Loops (m + 1)) (degree_match m r) _
        (NativeThetaPowers.fullPower m hm F P v₀ r)).symm

theorem unit_iff_scalar_comparison (r : ℕ) :
    (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom (singleCut m hm F P v₀ r) =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) ↔
    (kroneckerMap (Loops (m + 1)) (NativeThetaPowers.degree m r)).hom (ghEvaluationTest m r)
        (NativeThetaPowers.fullPower m hm F P v₀ r) =
      (kroneckerMap (Loops (m + 1)) (NativeThetaPowers.degree m r)).hom
        (NativeThetaPowerEvaluationTests.test m r) (NativeThetaPowers.fullPower m hm F P v₀ r) := by
  rw [NativeEvaluationUnitCriterion.unit_iff_pairing_one m hm P v₀,
    single_cut_pairing, NativeThetaPowerEvaluationTests.test_pairing_one]

theorem unit_of_test_equality (r : ℕ)
    (h : ghEvaluationTest m r = NativeThetaPowerEvaluationTests.test m r) :
    (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom (singleCut m hm F P v₀ r) =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  (unit_iff_scalar_comparison m hm F P v₀ r).mpr
    (congrArg (fun a => (kroneckerMap (Loops (m + 1)) (NativeThetaPowers.degree m r)).hom a
      (NativeThetaPowers.fullPower m hm F P v₀ r)) h)

theorem unit_iff_iterated_comparison (r : ℕ) :
    (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom (singleCut m hm F P v₀ r) =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) ↔
    singleCut m hm F P v₀ r =
      NativeThetaPowerEvaluationTests.foldCut m r (NativeThetaPowers.fullPower m hm F P v₀ r) := by
  have hu := NativeThetaPowerEvaluationTests.fold_existing_UNIT m hm F P v₀ r
  constructor
  · intro hz
    have he := congrArg (homologyPushZMod2 (FullLoopModel.forget (m + 1)) (m + 1)).hom
      (hz.trans hu.symm)
    simpa only [push_comp_apply, FullLoopModel.include_forget, push_id_apply] using he
  · intro he
    exact (congrArg (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom he).trans hu

theorem zero_test_equality (m : ℕ) : ghEvaluationTest m 0 = NativeThetaPowerEvaluationTests.test m 0 := rfl

theorem zero_single_UNIT :
    (homologyPushZMod2 (FullLoopModel.insert (m + 1)) (m + 1)).hom (singleCut m hm F P v₀ 0) =
      AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  unit_of_test_equality m hm F P v₀ 0 (zero_test_equality m)

end
end Finsler.NativeHighPowerUnitComparison
