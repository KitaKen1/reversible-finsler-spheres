module

public import Finsler.Loop.NativeBVGeometricTest

/-! The rotation of the original sphere evaluation test is the SAME
original primitive transgression. This identifies the retained-loop term
directly through the existing actual ordinary/H1 prism comparison. -/
@[expose] public section
namespace Finsler.NativeBVEvaluationTransgression
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1300000

theorem BV_evaluation (n q : ℕ) (z : homologyZMod2 (Loops n) q) :
    (homologyPushZMod2 (MeridianThetaCutCoefficient.evaluation n) (q + 1)).hom
      ((H1LoopRotation.BV n q).hom z) =
    (ContinuousLoopSweep.homology n q).hom (ContinuousLoopHomologyEquivalence.homology n q z) := by
  have he : MeridianThetaCutCoefficient.evaluation n =
      ContinuousLoopModel.inclusion n ≫ ContinuousLoopModel.evaluation n :=
    (ContinuousLoopModel.evaluation_square n).symm
  rw [he, ← SplitPairHomologyKernel.push_comp_apply]
  change (homologyPushZMod2 (ContinuousLoopModel.evaluation n) (q + 1)).hom
    (ContinuousLoopHomologyEquivalence.homology n (q + 1) ((H1LoopRotation.BV n q).hom z)) = _
  rw [H1LoopRotation.equivalence_BV]
  exact ConcreteCategory.congr_hom (OrdinaryLoopRotation.BV_evaluation n q) _

theorem evaluation_BV_pairing (m : ℕ) (z : homologyZMod2 (Loops (m + 1)) m) :
    (kroneckerMap _ (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m)
      ((H1LoopRotation.BV (m + 1) m).hom z) =
    (kroneckerMap _ m).hom (MeridianLoopClass.H1TransgressionClass m) z := by
  have hn := congrArg (fun φ : homologyDualZMod2 (Loops (m + 1)) (m + 1) =>
    φ ((H1LoopRotation.BV (m + 1) m).hom z))
      (kroneckerMap_naturality_apply (MeridianThetaCutCoefficient.evaluation (m + 1)) (m + 1)
        (SphereTopClass.topClass (m + 1) (by omega)))
  change (kroneckerMap _ (m + 1)).hom (MeridianThetaCutCoefficient.evaluationClass m)
    ((H1LoopRotation.BV (m + 1) m).hom z) =
    (kroneckerMap _ (m + 1)).hom (SphereTopClass.topClass (m + 1) (by omega))
      ((homologyPushZMod2 (MeridianThetaCutCoefficient.evaluation (m + 1)) (m + 1)).hom
        ((H1LoopRotation.BV (m + 1) m).hom z)) at hn
  rw [BV_evaluation] at hn
  exact hn.trans (ContinuousLoopSweep.H1_pairing (m + 1) m _ z).symm

theorem rotation_class (m : ℕ)
    (T : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + 1))
    (hT : cochainCoboundary (ZMod 2) (Loops (m + 1)) (m + 1) T = 0)
    (h : cocycleClass _ _ T hT = MeridianThetaCutCoefficient.evaluationClass m) :
    cocycleClass _ m (SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m T)
      (SelfSweepCochain.closed _ _ T hT) = MeridianLoopClass.H1TransgressionClass m := by
  apply kroneckerMap_injective (Loops (m + 1)) m
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective ((chains (Loops (m + 1))).homologyπ m)).mp inferInstance) z
  rw [kroneckerMap_cocycleClass]
  calc
    _ = ((chains (Loops (m + 1))).iCycles m ≫
        SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m T).hom c :=
      kroneckerFunctional_apply _ m _ (SelfSweepCochain.closed _ _ T hT) c
    _ = _ := by
      rw [← SelfSweepCochain.pairing _ m T hT c, h]
      exact evaluation_BV_pairing m _

theorem normalized_evaluation_rotation_class (m : ℕ) :
    cocycleClass _ m
      (SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVGeometricTest.evaluation m))
      (SelfSweepCochain.closed _ _ _ (NativeBVGeometricTest.evaluation_closed m)) =
        MeridianLoopClass.H1TransgressionClass m :=
  rotation_class m _ (NativeBVGeometricTest.evaluation_closed m) (NativeBVGeometricTest.evaluation_class m)

theorem same_supported_primitive_class (m : ℕ) (hm : 2 ≤ m) (F : Geometry.ReversibleMetric (m + 1)) :
    cocycleClass _ m
      (SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVGeometricTest.evaluation m))
      (SelfSweepCochain.closed _ _ _ (NativeBVGeometricTest.evaluation_closed m)) =
    cocycleClass _ m (NativeClosingArcPowerVanishing.powerCocycle m hm F 0)
      (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F 0) :=
  (normalized_evaluation_rotation_class m).trans
    (NativeGHPowerTimeCupAssociativity.power_class m hm F 0).symm

def correction (m : ℕ) (hm : 2 ≤ m) (F : Geometry.ReversibleMetric (m + 1)) :
    singularCochainGroup (ZMod 2) (Loops (m + 1)) (m - 1) :=
  CochainClassExact.primitive (cochainCxZMod2 (Loops (m + 1))) m (by omega)
    (SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVGeometricTest.evaluation m))
    (NativeClosingArcPowerVanishing.powerCocycle m hm F 0)
    (SelfSweepCochain.closed _ _ _ (NativeBVGeometricTest.evaluation_closed m))
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F 0)
    (same_supported_primitive_class m hm F)

private theorem differential (X : TopCat.{0}) (i j : ℕ) (h : i + 1 = j)
    (η : singularCochainGroup (ZMod 2) X i) :
    ((cochainCxZMod2 X).d i j).hom η = (chains X).d j i ≫ η := by
  subst j
  rfl

theorem correction_boundary (m : ℕ) (hm : 2 ≤ m) (F : Geometry.ReversibleMetric (m + 1)) :
    (chains (Loops (m + 1))).d m (m - 1) ≫ correction m hm F =
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVGeometricTest.evaluation m) -
        CochainDegreeTransport.pre (Loops (m + 1)) (show m = NativeGHPowers.degree m 0 from rfl)
          (NativeClosingArcPowerVanishing.powerCocycle m hm F 0) := by
  have h := CochainClassExact.primitive_d (cochainCxZMod2 (Loops (m + 1))) m (by omega)
    (SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVGeometricTest.evaluation m))
    (NativeClosingArcPowerVanishing.powerCocycle m hm F 0)
    (SelfSweepCochain.closed _ _ _ (NativeBVGeometricTest.evaluation_closed m))
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F 0) (same_supported_primitive_class m hm F)
  rw [differential _ _ _ (by omega)] at h
  simpa only [correction, CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using h

theorem correction_cycle_values (m : ℕ) (hm : 2 ≤ m) (F : Geometry.ReversibleMetric (m + 1)) :
    (chains (Loops (m + 1))).iCycles m ≫
        SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVGeometricTest.evaluation m) =
      (chains (Loops (m + 1))).iCycles m ≫
        CochainDegreeTransport.pre (Loops (m + 1)) (show m = NativeGHPowers.degree m 0 from rfl)
          (NativeClosingArcPowerVanishing.powerCocycle m hm F 0) := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← correction_boundary m hm F, ← Category.assoc,
    HomologicalComplex.iCycles_d, zero_comp]

end
end Finsler.NativeBVEvaluationTransgression
