module

public import Finsler.Loop.NativeBVSourceEvaluation
public import Finsler.Loop.NativeSourceGHProjection

/-! Normalize the genuine source sphere-evaluation pullback. Dold-Kan
naturality retains the literal tested/source equality. Its actual
normalization primitive, followed by the SAME retained GH_r and ORIGINAL
Thom/time, bounds the source-test difference and vanishes on constants. -/
@[expose] public section
namespace Finsler.NativeBVNormalizedSource
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.NativeInnerCutPullback
open Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

def evaluation (m : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (m + 1) :=
  SingularNormalization.normalize _ (m + 1) (NativeBVSourceEvaluation.evaluation m)

theorem evaluation_closed (m : ℕ) : cochainCoboundary (ZMod 2) _ (m + 1) (evaluation m) = 0 :=
  SingularNormalization.normalize_closed _ _ _ (NativeBVSourceEvaluation.evaluation_closed m)

theorem evaluation_normalized (m : ℕ) : DoldKan.DegeneraciesVanish
    (X := SingularNormalization.linearization (Loops (m + 1))) (evaluation m) :=
  SingularNormalization.normalize_degeneracies _ _ _

theorem evaluation_pullback (m : ℕ) : evaluation m =
    cochainPullback (MeridianThetaCutCoefficient.evaluation (m + 1)) (m + 1)
      (SingularNormalization.normalize _ (m + 1) (classRepr _ (m + 1) (SphereTopClass.topClass (m + 1) (by omega)))) :=
  (SingularNormalization.normalize_natural _ _ _).symm

theorem evaluation_class (m : ℕ) : cocycleClass _ (m + 1) (evaluation m) (evaluation_closed m) =
    MeridianThetaCutCoefficient.evaluationClass m :=
  (SingularNormalization.normalize_class _ m _ (NativeBVSourceEvaluation.evaluation_closed m)).trans
    (NativeBVSourceEvaluation.evaluation_class m)

def correction (m : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) m :=
  SingularNormalization.primitive _ m (NativeBVSourceEvaluation.evaluation m)

theorem correction_boundary (m : ℕ) : cochainCoboundary (ZMod 2) _ m (correction m) =
    evaluation m - NativeBVSourceEvaluation.evaluation m :=
  SingularNormalization.primitive_boundary _ _ _ (NativeBVSourceEvaluation.evaluation_closed m)

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

theorem tested_source : cochainPullback (TopCat.ofHom (tested (m + 1) (radiusLe m hm F))) (m + 1) (evaluation m) =
    cochainPullback (NativeNearCutOriginalThom.underlying m hm F) (m + 1) (evaluation m) := by
  rw [evaluation_pullback, ← pullback_comp, ← pullback_comp, NativeBVSourceEvaluation.tested_evaluation_map]

def near : singularCochainGroup (ZMod 2) (NativeNearCutOriginalThom.space m hm F) (NativeGHPowers.degree m r + m + 1) :=
  CupOne.cup _ (m + 1) (NativeGHPowers.degree m r) (NativeGHPowers.degree m r + m + 1) (by omega)
    (cochainPullback (NativeNearCutOriginalThom.underlying m hm F) (m + 1) (evaluation m))
    (NativeNearCutPowerSubstitution.retainedPower m hm F r)

def nearCorrection : singularCochainGroup (ZMod 2) (NativeNearCutOriginalThom.space m hm F) (NativeGHPowers.degree m r + m) :=
  CupOne.cup _ m (NativeGHPowers.degree m r) (NativeGHPowers.degree m r + m) (by omega)
    (cochainPullback (NativeNearCutOriginalThom.underlying m hm F) m (correction m))
    (NativeNearCutPowerSubstitution.retainedPower m hm F r)

theorem near_boundary : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m r + m) (nearCorrection m hm F r) =
    near m hm F r - NativeBVSourceEvaluation.near m hm F r := by
  unfold nearCorrection
  rw [NormalizedCupBoundary.boundary_right_closed _ _ _ _ _ _ _
    (NativeNearCutPowerSubstitution.retainedPower_closed m hm F r), cochainPullback_cochainCoboundary, correction_boundary]
  have hp := map_sub ((singularCochainComplexZMod2.map (NativeNearCutOriginalThom.underlying m hm F).op).f (m + 1)).hom
    (evaluation m) (NativeBVSourceEvaluation.evaluation m)
  change cochainPullback _ (m + 1) (_ - _) = cochainPullback _ (m + 1) _ - cochainPullback _ (m + 1) _ at hp
  rw [hp, NormalizedCupBoundary.cup_sub_left]
  rfl

def sourceCorrection : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  CochainDegreeTransport.pre _ (NativeBVSourceEvaluation.degree_match m r)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) _ (nearCorrection m hm F r))

def source : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) :=
  CochainDegreeTransport.pre _ (by rw [NativeBVSourceEvaluation.degree_match]; omega)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) _ (near m hm F r))

private theorem boundary_pre {X : TopCat.{0}} {i j a b : ℕ} (hi : i = a) (hj : j = b)
    (K : singularCochainGroup (ZMod 2) X a) (T U : singularCochainGroup (ZMod 2) X b)
    (h : (chains X).d b a ≫ K = T - U) :
    (chains X).d j i ≫ CochainDegreeTransport.pre X hi K =
      CochainDegreeTransport.pre X hj T - CochainDegreeTransport.pre X hj U := by
  subst a b
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using h

theorem source_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1) + 1)
    (NativeGHPowers.degree m (r + 1)) ≫ sourceCorrection m hm F r = source m hm F r - NativeBVSourceEvaluation.source m hm F r := by
  have hb := NativeBVThomBoundary.source_boundary m (rhoPos m hm F) (rhoLt m hm F)
    (NativeGHPowers.degree m r + m) (nearCorrection m hm F r)
  rw [near_boundary] at hb
  unfold NativeBVThomBoundary.source at hb
  rw [Preadditive.comp_sub] at hb
  exact boundary_pre (NativeBVSourceEvaluation.degree_match m r)
    (show NativeGHPowers.degree m (r + 1) + 1 = m + (NativeGHPowers.degree m r + m + 1) by rw [NativeBVSourceEvaluation.degree_match]; omega) _ _ _ hb

theorem sourceCorrection_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1)) (sourceCorrection m hm F r) = 0 := by
  unfold sourceCorrection
  rw [← NormalizedCutScalarPullback.pre_pullback, NativeBVThomBoundary.source_constants_zero]
  exact comp_zero

theorem near_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m r + m + 1) (near m hm F r) = 0 :=
  CupCapOrder.closed _ _ _ _ _ _ _ (cochainPullback_cocycle _ _ _ (evaluation_closed m))
    (NativeNearCutPowerSubstitution.retainedPower_closed m hm F r)

theorem source_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1) + 1) (source m hm F r) = 0 :=
  CochainDegreeTransport.closed _ _ _ (DegreeLoweringCochainPullback.closed
    (GlobalThomTime.operation m (rhoPos m hm F) (rhoLt m hm F)) _ _ (near_closed m hm F r))

theorem source_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1) + 1) (source m hm F r) = 0 := by
  unfold source
  rw [← NormalizedCutScalarPullback.pre_pullback, NativeBVThomBoundary.source_constants_zero]
  exact comp_zero

end
end Finsler.NativeBVNormalizedSource
