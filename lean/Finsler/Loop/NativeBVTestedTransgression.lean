module

public import Finsler.Loop.TestedTimeCupBoundary
public import Finsler.Loop.NativeBVEvaluationTransgression

/-! Rotate the evaluation in the TESTED output slot of the ORIGINAL
geometric time cup. Its correction to the SAME next GH power is an
actual constant-relative boundary, and its value on the SAME raised
input is one. Moving source rotation to this tested output remains open. -/
@[expose] public section
namespace Finsler.NativeBVTestedTransgression
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.MeridianLoopFamily Finsler.NativeInnerCutPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1))
    ((m + (m - 1)) + NativeGHPowers.degree m r) :=
  GeometricTimeCupCochain.cochain m (m - 1) (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (NativeBVEvaluationTransgression.correction m hm F) (NativeGHPowers.degree m r)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r)

def before : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  GeometricTimeCupCochain.cochain m m (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVGeometricTest.evaluation m))
    (NativeGHPowers.degree m r) (NativeClosingArcPowerVanishing.powerCocycle m hm F r)

def after : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  GeometricTimeCupCochain.cochain m m (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F 0)
    (NativeGHPowers.degree m r) (NativeClosingArcPowerVanishing.powerCocycle m hm F r)

theorem boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
    ((m + (m - 1)) + NativeGHPowers.degree m r) ≫ primitive m hm F r =
      before m hm F r - after m hm F r := by
  have h := TestedTimeCupBoundary.geometric_boundary_at m (rhoPos m hm F) (rhoLt m hm F)
    (radiusLe m hm F) (m - 1) m (NativeGHPowers.degree m r) (by omega)
    (NativeBVEvaluationTransgression.correction m hm F)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r)
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r)
  rw [NativeBVEvaluationTransgression.correction_boundary, TestedTimeCupBoundary.geometric_sub] at h
  exact h

theorem primitive_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
      ((m + (m - 1)) + NativeGHPowers.degree m r) (primitive m hm F r) = 0 :=
  GlobalTimeCupConstantsVanish.cochain_zero _ _ _ _ _ _ _ _

theorem before_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1))
    (before m hm F r) = 0 :=
  GeometricTimeCupCochain.closed _ _ _ _ _ _ _ _
    (SelfSweepCochain.closed _ _ _ (NativeBVGeometricTest.evaluation_closed m))
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r)

theorem after_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1))
    (after m hm F r) = 0 :=
  GeometricTimeCupCochain.closed _ _ _ _ _ _ _ _
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F 0)
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r)

theorem before_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
      (NativeGHPowers.degree m (r + 1)) (before m hm F r) = 0 :=
  GlobalTimeCupConstantsVanish.cochain_zero _ _ _ _ _ _ _ _

theorem after_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
      (NativeGHPowers.degree m (r + 1)) (after m hm F r) = 0 :=
  GlobalTimeCupConstantsVanish.cochain_zero _ _ _ _ _ _ _ _

theorem relative_cycle_values {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains (Loops (m + 1))).X (NativeGHPowers.degree m (r + 1)))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f
      (NativeGHPowers.degree m (r + 1))) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d
        (NativeGHPowers.degree m (r + 1)) ((m + (m - 1)) + NativeGHPowers.degree m r) = 0) :
    u ≫ before m hm F r = u ≫ after m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← boundary]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (primitive_constants_zero m hm F r)

theorem cycle_values :
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ before m hm F r =
      (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ after m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← boundary, ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

theorem after_class : cocycleClass _ (NativeGHPowers.degree m (r + 1))
    (after m hm F r) (after_closed m hm F r) = NativeGHPowers.power m (r + 1) := by
  exact (NativeGHPowerTimeCupAssociativity.cochain_class m (by omega) m (NativeGHPowers.degree m r)
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F 0)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r)
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F 0)
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r)).trans
      (congrArg₂ (CanonicalGlobalTimeCup.product m m (NativeGHPowers.degree m r))
        (NativeClosingArcPowerVanishing.powerCocycle_class m hm F 0)
        (NativeClosingArcPowerVanishing.powerCocycle_class m hm F r))

theorem before_class : cocycleClass _ (NativeGHPowers.degree m (r + 1))
    (before m hm F r) (before_closed m hm F r) = NativeGHPowers.power m (r + 1) := by
  exact (NativeGHPowerTimeCupAssociativity.cochain_class m (by omega) m (NativeGHPowers.degree m r)
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVGeometricTest.evaluation m))
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r)
    (SelfSweepCochain.closed _ _ _ (NativeBVGeometricTest.evaluation_closed m))
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r)).trans
      (congrArg₂ (CanonicalGlobalTimeCup.product m m (NativeGHPowers.degree m r))
        (NativeBVEvaluationTransgression.normalized_evaluation_rotation_class m)
        (NativeClosingArcPowerVanishing.powerCocycle_class m hm F r))

theorem value_one (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ before m hm F r).hom c = 1 := by
  calc
    _ = (kroneckerMap _ _).hom (cocycleClass _ _ (before m hm F r) (before_closed m hm F r))
        (((chains (Loops (m + 1))).homologyπ _).hom c) := by
      rw [kroneckerMap_cocycleClass]
      exact (kroneckerFunctional_apply _ _ _ (before_closed m hm F r) c).symm
    _ = 1 := by
      rw [before_class, hc]
      exact NativeRaisedBVCandidates.pairing_one m hm F P v₀ r

end
end Finsler.NativeBVTestedTransgression
