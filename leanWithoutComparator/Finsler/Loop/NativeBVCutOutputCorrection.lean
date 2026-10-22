module

public import Finsler.Loop.NativeBVEvaluationTransgression
public import Finsler.Loop.NativeBVThomBoundary

/-! Carry the actual evaluation-rotation correction through EACH original
high-GH cut. The resulting primitive vanishes on constants even though
the original correction has no asserted support. Hence equality holds on
actual relative cycles, not merely absolute cycles. -/
@[expose] public section
namespace Finsler.NativeBVCutOutputCorrection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.NativeInnerCutPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def cut := PrismSelfCut.operation m (NativeGHPowers.degree m r)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
  (NativeClosingArcPowerVanishing.powerCocycle m hm F r)
  (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r)

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1))
    ((m + NativeGHPowers.degree m r) + (m - 1)) :=
  (cut m hm F r).component (m - 1) ≫ NativeBVEvaluationTransgression.correction m hm F

def before : singularCochainGroup (ZMod 2) (Loops (m + 1)) ((m + NativeGHPowers.degree m r) + m) :=
  (cut m hm F r).component m ≫
    SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVGeometricTest.evaluation m)

def after : singularCochainGroup (ZMod 2) (Loops (m + 1)) ((m + NativeGHPowers.degree m r) + m) :=
  (cut m hm F r).component m ≫
    CochainDegreeTransport.pre _ (show m = NativeGHPowers.degree m 0 from rfl)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F 0)

theorem boundary :
    (chains (Loops (m + 1))).d ((m + NativeGHPowers.degree m r) + m)
      ((m + NativeGHPowers.degree m r) + (m - 1)) ≫ primitive m hm F r =
      before m hm F r - after m hm F r := by
  unfold primitive before after
  rw [NativeBVThomBoundary.lowering_boundary_at (cut m hm F r) (m - 1) m (by omega),
    NativeBVEvaluationTransgression.correction_boundary, Preadditive.comp_sub]

theorem primitive_geometric : primitive m hm F r =
    GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m r)
      (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F r) (m - 1)
      (NativeBVEvaluationTransgression.correction m hm F) :=
  GeometricTimeCupCochain.operation_dual _ _ _ _ _ _ _ _ _

theorem primitive_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
      ((m + NativeGHPowers.degree m r) + (m - 1)) (primitive m hm F r) = 0 := by
  rw [primitive_geometric]
  exact GlobalTimeCupConstantsVanish.cochain_zero _ _ _ _ _ _ _ _

theorem relative_cycle_values {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains (Loops (m + 1))).X ((m + NativeGHPowers.degree m r) + m))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f
      ((m + NativeGHPowers.degree m r) + m)) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d
        ((m + NativeGHPowers.degree m r) + m) ((m + NativeGHPowers.degree m r) + (m - 1)) = 0) :
    u ≫ before m hm F r = u ≫ after m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← boundary]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (primitive_constants_zero m hm F r)

theorem cycle_values :
    (chains (Loops (m + 1))).iCycles ((m + NativeGHPowers.degree m r) + m) ≫ before m hm F r =
      (chains (Loops (m + 1))).iCycles ((m + NativeGHPowers.degree m r) + m) ≫ after m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← boundary, ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

end
end Finsler.NativeBVCutOutputCorrection
