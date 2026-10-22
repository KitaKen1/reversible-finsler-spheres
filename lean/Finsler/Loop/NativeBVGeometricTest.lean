module

public import Finsler.Loop.NativeBVOriginalPrismTest
public import Finsler.Loop.NativeGHPowerTimeCupAssociativity
public import Finsler.Loop.SelfSweepCochain

/-! Replace the arbitrary representative of the high GH/evaluation test
by the actual supported cut/time cochain. Its original rotation value is
unchanged on every source cycle, so the remaining coefficient can be
computed directly in the original chain geometry. -/
@[expose] public section
namespace Finsler.NativeBVGeometricTest
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.MeridianLoopFamily Finsler.SmallChainCarrier Finsler.NativeInnerCutPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

def evaluation : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + 1) :=
  SingularNormalization.normalize _ _ (classRepr _ _ (MeridianThetaCutCoefficient.evaluationClass m))

theorem evaluation_closed : cochainCoboundary (ZMod 2) (Loops (m + 1)) (m + 1) (evaluation m) = 0 :=
  SingularNormalization.normalize_closed _ _ _ (classRepr_isCocycle _ _ _)

theorem evaluation_class : cocycleClass _ (m + 1) (evaluation m) (evaluation_closed m) =
    MeridianThetaCutCoefficient.evaluationClass m :=
  (SingularNormalization.normalize_class _ m _ (classRepr_isCocycle _ _ _)).trans (cocycleClass_classRepr _ _ _)

def raw (r : ℕ) := GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m r)
  (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
  (NativeClosingArcPowerVanishing.powerCocycle m hm F r) (m + 1) (evaluation m)

theorem raw_closed (r : ℕ) : cochainCoboundary (ZMod 2) (Loops (m + 1))
    ((m + NativeGHPowers.degree m r) + (m + 1)) (raw m hm F r) = 0 :=
  GeometricTimeCupCochain.closed _ _ _ _ _ _ _ _
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r) (evaluation_closed m)

def test (r : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) :=
  CochainDegreeTransport.pre _ ((NativeThetaBVShiftBridge.degree_match m r).trans
    (NativeHighPowerUnitComparison.degree_match m r)) (raw m hm F r)

theorem test_closed (r : ℕ) : cochainCoboundary (ZMod 2) (Loops (m + 1))
    (NativeGHPowers.degree m (r + 1) + 1) (test m hm F r) = 0 :=
  CochainDegreeTransport.closed _ _ _ (raw_closed m hm F r)

theorem test_class (r : ℕ) :
    cocycleClass _ _ (test m hm F r) (test_closed m hm F r) =
      cocycleClass _ _ (NativeBVOriginalPrismTest.test m r) (NativeBVOriginalPrismTest.test_closed m r) := by
  unfold test NativeBVOriginalPrismTest.test
  rw [CochainDegreeTransport.class_cast _ _ _ (raw_closed m hm F r),
    CochainDegreeTransport.class_cast _ _ _ (classRepr_isCocycle _ _ _), cocycleClass_classRepr]
  have hr := NativeGHPowerTimeCupAssociativity.cochain_class m (by omega) _ _
    (rhoPos m hm F) (rhoLt m hm F) (radiusLe m hm F)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r) (evaluation m)
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r) (evaluation_closed m)
  change cocycleClass _ _ (raw m hm F r) (raw_closed m hm F r) = _ at hr
  rw [NativeGHPowerTimeCupAssociativity.power_class, evaluation_class] at hr
  rw [hr, NativeHighPowerUnitComparison.ghEvaluationTest, NativeGHPowerTimeCupAssociativity.cast_trans]

theorem rotation_cycle_values (r : ℕ) :
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
        SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r) =
      (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
        SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVOriginalPrismTest.test m r) :=
  SelfSweepCochain.cohomologous_cycle_values _ _ _ _ (test_closed m hm F r)
    (NativeBVOriginalPrismTest.test_closed m r) (test_class m hm F r)

theorem coefficient_on_cycle (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    NativeBVOriginalScalar.coefficient m hm P v₀ r =
      ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
        SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r)).hom c := by
  rw [rotation_cycle_values]
  simpa only [SelfSweepCochain.cochain, SelfHomotopySweep.component, Category.assoc] using
    NativeBVOriginalPrismTest.coefficient_on_cycle m hm F P v₀ r c hc

end
end Finsler.NativeBVGeometricTest
