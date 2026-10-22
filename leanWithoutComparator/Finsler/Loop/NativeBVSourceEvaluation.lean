module

public import Finsler.Loop.NativeNearCutOriginalThom
public import Finsler.Loop.NativeBVTestedEvaluationTest
public import Finsler.Loop.NormalizedCupBoundary

/-! Replace the original normalized evaluation test by an ACTUAL
sphere-cocycle pullback. On the original cut neighborhood its tested
pullback is literally the source-evaluation pullback. The original
Thom/time and H1 rotation carry the representative correction to a
constant-relative boundary, preserving every original BV coefficient. -/
@[expose] public section
namespace Finsler.NativeBVSourceEvaluation
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.NativeInnerCutPullback
open Finsler.SupportedSelfCut Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def evaluation (m : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + 1) :=
  cochainPullback (MeridianThetaCutCoefficient.evaluation (m + 1)) (m + 1)
    (classRepr _ (m + 1) (SphereTopClass.topClass (m + 1) (by omega)))

theorem evaluation_closed (m : ℕ) : cochainCoboundary (ZMod 2) _ (m + 1) (evaluation m) = 0 :=
  cochainPullback_cocycle _ _ _ (classRepr_isCocycle _ _ _)

theorem evaluation_class (m : ℕ) : cocycleClass _ (m + 1) (evaluation m) (evaluation_closed m) =
    MeridianThetaCutCoefficient.evaluationClass m := by
  unfold evaluation
  rw [← cohPullback_cocycleClass _ _ _ (classRepr_isCocycle _ _ _), cocycleClass_classRepr]
  rfl

theorem evaluation_class_eq (m : ℕ) : cocycleClass _ (m + 1) (NativeBVGeometricTest.evaluation m)
    (NativeBVGeometricTest.evaluation_closed m) =
      cocycleClass _ (m + 1) (evaluation m) (evaluation_closed m) :=
  (NativeBVGeometricTest.evaluation_class m).trans (evaluation_class m).symm

def correction (m : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) m :=
  CochainClassExact.primitive (cochainCxZMod2 (Loops (m + 1))) (m + 1) (by omega)
    (NativeBVGeometricTest.evaluation m) (evaluation m)
    (NativeBVGeometricTest.evaluation_closed m) (evaluation_closed m) (evaluation_class_eq m)

theorem correction_boundary (m : ℕ) : cochainCoboundary (ZMod 2) _ m (correction m) =
    NativeBVGeometricTest.evaluation m - evaluation m :=
  CochainClassExact.primitive_d (cochainCxZMod2 (Loops (m + 1))) (m + 1) (by omega)
    (NativeBVGeometricTest.evaluation m) (evaluation m)
    (NativeBVGeometricTest.evaluation_closed m) (evaluation_closed m) (evaluation_class_eq m)

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

theorem tested_evaluation_map : TopCat.ofHom (tested (m + 1) (radiusLe m hm F)) ≫
    MeridianThetaCutCoefficient.evaluation (m + 1) =
      NativeNearCutOriginalThom.underlying m hm F ≫ MeridianThetaCutCoefficient.evaluation (m + 1) := by
  ext z : 1
  apply Subtype.ext
  exact tested_basepoint (m + 1) (radiusLe m hm F) z

theorem tested_evaluation_pullback : cochainPullback (TopCat.ofHom (tested (m + 1) (radiusLe m hm F)))
    (m + 1) (evaluation m) =
      cochainPullback (NativeNearCutOriginalThom.underlying m hm F) (m + 1) (evaluation m) := by
  unfold evaluation
  rw [← pullback_comp, ← pullback_comp, tested_evaluation_map]

def near : singularCochainGroup (ZMod 2) (NativeNearCutOriginalThom.space m hm F)
    (NativeGHPowers.degree m r + m + 1) :=
  CupOne.cup _ (m + 1) (NativeGHPowers.degree m r) (NativeGHPowers.degree m r + m + 1) (by omega)
    (cochainPullback (NativeNearCutOriginalThom.underlying m hm F) (m + 1) (evaluation m))
    (cochainPullback (TopCat.ofHom (retained (m + 1) (radiusLe m hm F))) (NativeGHPowers.degree m r)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F r))

def nearCorrection : singularCochainGroup (ZMod 2) (NativeNearCutOriginalThom.space m hm F)
    (NativeGHPowers.degree m r + m) :=
  CupOne.cup _ m (NativeGHPowers.degree m r) (NativeGHPowers.degree m r + m) (by omega)
    (cochainPullback (TopCat.ofHom (tested (m + 1) (radiusLe m hm F))) m (correction m))
    (cochainPullback (TopCat.ofHom (retained (m + 1) (radiusLe m hm F))) (NativeGHPowers.degree m r)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F r))

theorem near_boundary : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m r + m)
    (nearCorrection m hm F r) = NativeBVComplementCapTest.near m hm F r - near m hm F r := by
  unfold nearCorrection
  rw [NormalizedCupBoundary.boundary_right_closed _ _ _ _ _ _ _
    (cochainPullback_cocycle _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r)),
    cochainPullback_cochainCoboundary, correction_boundary]
  have hp := map_sub ((singularCochainComplexZMod2.map
    (TopCat.ofHom (tested (m + 1) (radiusLe m hm F))).op).f (m + 1)).hom
    (NativeBVGeometricTest.evaluation m) (evaluation m)
  change cochainPullback _ (m + 1) (_ - _) = cochainPullback _ (m + 1) _ - cochainPullback _ (m + 1) _ at hp
  rw [hp, NormalizedCupBoundary.cup_sub_left, tested_evaluation_pullback]
  rfl

theorem degree_match : NativeGHPowers.degree m (r + 1) = m + (NativeGHPowers.degree m r + m) := by
  rw [NativeGHPowers.degree]
  omega

def sourceCorrection : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  CochainDegreeTransport.pre _ (degree_match m r)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F)
      (NativeGHPowers.degree m r + m) (nearCorrection m hm F r))

def source : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) :=
  CochainDegreeTransport.pre _ (by rw [degree_match]; omega)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F)
      (NativeGHPowers.degree m r + m + 1) (near m hm F r))

private theorem boundary_pre {X : TopCat.{0}} {i j a b : ℕ} (hi : i = a) (hj : j = b)
    (K : singularCochainGroup (ZMod 2) X a) (T U : singularCochainGroup (ZMod 2) X b)
    (h : (chains X).d b a ≫ K = T - U) :
    (chains X).d j i ≫ CochainDegreeTransport.pre X hi K =
      CochainDegreeTransport.pre X hj T - CochainDegreeTransport.pre X hj U := by
  subst a b
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using h

theorem source_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1) + 1)
    (NativeGHPowers.degree m (r + 1)) ≫ sourceCorrection m hm F r =
      NativeBVTestedEvaluationTest.source m hm F r - source m hm F r := by
  have hb := NativeBVThomBoundary.source_boundary m (rhoPos m hm F) (rhoLt m hm F)
    (NativeGHPowers.degree m r + m) (nearCorrection m hm F r)
  rw [near_boundary] at hb
  unfold NativeBVThomBoundary.source at hb
  rw [Preadditive.comp_sub] at hb
  exact boundary_pre (degree_match m r) (show NativeGHPowers.degree m (r + 1) + 1 =
      m + (NativeGHPowers.degree m r + m + 1) by rw [degree_match]; omega) _ _ _ hb

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (K : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h K) =
      CochainDegreeTransport.pre X h (cochainPullback f j K) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

theorem sourceCorrection_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1)) (sourceCorrection m hm F r) = 0 := by
  unfold sourceCorrection
  rw [pullback_pre, NativeBVThomBoundary.source_constants_zero]
  exact comp_zero

theorem near_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m r + m + 1)
    (near m hm F r) = 0 :=
  CupCapOrder.closed _ _ _ _ _ _ _ (cochainPullback_cocycle _ _ _ (evaluation_closed m))
    (cochainPullback_cocycle _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r))

theorem source_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1) + 1)
    (source m hm F r) = 0 := by
  apply CochainDegreeTransport.closed
  have h := NativeBVThomBoundary.source_boundary m (rhoPos m hm F) (rhoLt m hm F)
    (NativeGHPowers.degree m r + m + 1) (near m hm F r)
  rw [near_closed] at h
  exact h.trans comp_zero

theorem source_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1) + 1) (source m hm F r) = 0 := by
  unfold source
  rw [pullback_pre, NativeBVThomBoundary.source_constants_zero]
  exact comp_zero

def test : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (source m hm F r)

theorem test_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1)) (test m hm F r) = 0 :=
  SelfSweepCochain.closed _ _ _ (source_closed m hm F r)

theorem test_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1)) (test m hm F r) = 0 :=
  NativeBVRelativeCochain.rotation_constants_zero _ _ _ (source_constants_zero m hm F r)

def rotatedCorrection : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) - 1) :=
  (H1LoopRotation.chainHomotopy (m + 1)).hom (NativeGHPowers.degree m (r + 1) - 1)
    (NativeGHPowers.degree m (r + 1)) ≫ sourceCorrection m hm F r

theorem rotated_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
    (NativeGHPowers.degree m (r + 1) - 1) ≫ rotatedCorrection m hm F r =
      NativeBVTestedEvaluationTest.test m hm F r - test m hm F r := by
  unfold rotatedCorrection
  rw [NativeBVRelativeCochain.boundary_at (m + 1) _ _ (NativeGHPowers.degree m (r + 1) + 1)
    (by have := NativeGHPowers.degree_ge m (r + 1); omega) rfl, source_boundary, Preadditive.comp_sub]
  rfl

theorem rotatedCorrection_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1) - 1) (rotatedCorrection m hm F r) = 0 :=
  NativeBVRelativeCochain.rotation_constants_zero_at (m + 1) _ _
    (by have := NativeGHPowers.degree_ge m (r + 1); omega) _ (sourceCorrection_constants_zero m hm F r)

theorem cycle_values : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
    NativeBVTestedEvaluationTest.test m hm F r =
      (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ test m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary m hm F r, ← Category.assoc,
    HomologicalComplex.iCycles_d, zero_comp]

theorem relative_cycle_values {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains (Loops (m + 1))).X (NativeGHPowers.degree m (r + 1)))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f
      (NativeGHPowers.degree m (r + 1))) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d
        (NativeGHPowers.degree m (r + 1)) (NativeGHPowers.degree m (r + 1) - 1) = 0) :
    u ≫ NativeBVTestedEvaluationTest.test m hm F r = u ≫ test m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary m hm F r]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (rotatedCorrection_constants_zero m hm F r)

theorem coefficient_on_cycle (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    NativeBVOriginalScalar.coefficient m hm P v₀ r =
      ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ test m hm F r).hom c := by
  rw [← cycle_values]
  exact NativeBVTestedEvaluationTest.coefficient_on_cycle m hm F r P v₀ c hc

end
end Finsler.NativeBVSourceEvaluation
