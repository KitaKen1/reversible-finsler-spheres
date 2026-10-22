module

public import Finsler.Loop.NativeBVNormalizedSource

/-! The SAME original BV coefficient is now the rotation of an ordinary
source cup: normalized sphere evaluation cup bare ORIGINAL Thom/time
of retained GH_r. Normalization and source projection are combined by an
actual constant-relative primitive, stable under full-period H1 rotation.
No ordinary-cup rotation derivation formula is assumed. -/
@[expose] public section
namespace Finsler.NativeBVSourceCupProjection
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

private theorem align_cup (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (a q N D : ℕ) (hN : a + q = N) (hD : D = m + (a + q))
    (A : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) a)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q) :
    CochainDegreeTransport.pre _ hD (NativeBVThomBoundary.source m hρ hρr (a + q) (cochainCup a q A B)) =
      CochainDegreeTransport.pre _ (show D = m + N by omega)
        (NativeBVThomBoundary.source m hρ hρr N (CupOne.cup _ a q N hN A B)) := by
  subst N
  rw [CupOne.cup_comparison]

private theorem boundary_pre {X : TopCat.{0}} {i j a b : ℕ} (hi : i = a) (hj : j = b)
    (K : singularCochainGroup (ZMod 2) X a) (T U : singularCochainGroup (ZMod 2) X b)
    (h : (chains X).d b a ≫ K = T - U) :
    (chains X).d j i ≫ CochainDegreeTransport.pre X hi K =
      CochainDegreeTransport.pre X hj T - CochainDegreeTransport.pre X hj U := by
  subst a b
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using h

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def ordinaryCup : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) :=
  CupOne.cup _ (m + 1) (m + NativeGHPowers.degree m r) (NativeGHPowers.degree m (r + 1) + 1)
    (by rw [NativeNearCutPowerSubstitution.degree_match]; omega)
    (NativeBVNormalizedSource.evaluation m) (NativeSourceGHProjection.bareSource m hm F r)

theorem ordinaryCup_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1) + 1) (ordinaryCup m hm F r) = 0 :=
  CupCapOrder.closed _ _ _ _ _ _ _ (NativeBVNormalizedSource.evaluation_closed m)
    (NativeSourceGHProjection.bareSource_closed m hm F r)

theorem ordinaryCup_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1) + 1) (ordinaryCup m hm F r) = 0 :=
  CupCapOrder.restriction_zero _ _ _ _ _ _ _ (Or.inr (NativeSourceGHProjection.bareSource_constants_zero m hm F r))

theorem source_aligned : CochainDegreeTransport.pre _
    (show NativeGHPowers.degree m (r + 1) + 1 = m + ((m + 1) + NativeGHPowers.degree m r) by
      rw [NativeNearCutPowerSubstitution.degree_match]; omega)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) ((m + 1) + NativeGHPowers.degree m r)
      (NativeSourceThomProjection.near m (m + 1) (NativeGHPowers.degree m r)
        (NativeBVNormalizedSource.evaluation m) (NativeNearCutPowerSubstitution.retainedPower m hm F r))) =
    NativeBVNormalizedSource.source m hm F r := by
  unfold NativeSourceThomProjection.near NativeSourceThomProjection.alpha
  rw [← pullback_comp]
  exact align_cup _ _ _ _ _ _ _ _ _ _ _

theorem projection_exists : ∃ K : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)),
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1)) K = 0 ∧
    (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1) + 1) (NativeGHPowers.degree m (r + 1)) ≫ K =
      ordinaryCup m hm F r - NativeBVNormalizedSource.source m hm F r := by
  obtain ⟨K, hK, hb⟩ := NativeSourceTimeProjection.exists_boundary_at_degree m (rhoPos m hm F) (rhoLt m hm F)
    (m + 1) (NativeGHPowers.degree m r) (NativeGHPowers.degree m (r + 1) + 1) (by omega)
    (by rw [NativeNearCutPowerSubstitution.degree_match]; omega) (NativeBVNormalizedSource.evaluation m)
    (NativeNearCutPowerSubstitution.retainedPower m hm F r) (NativeBVNormalizedSource.evaluation_normalized m)
    (NativeBVNormalizedSource.evaluation_closed m) (NativeNearCutPowerSubstitution.retainedPower_closed m hm F r)
  rw [source_aligned] at hb
  refine ⟨CochainDegreeTransport.pre _ (show NativeGHPowers.degree m (r + 1) = NativeGHPowers.degree m (r + 1) + 1 - 1 by omega) K, ?_, ?_⟩
  · rw [← NormalizedCutScalarPullback.pre_pullback, hK]
    exact comp_zero
  · exact boundary_pre (by omega) rfl _ _ _ hb

def projectionPrimitive := Classical.choose (projection_exists m hm F r)

theorem projection_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1)) (projectionPrimitive m hm F r) = 0 :=
  (Classical.choose_spec (projection_exists m hm F r)).1

theorem projection_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1) + 1)
    (NativeGHPowers.degree m (r + 1)) ≫ projectionPrimitive m hm F r =
      ordinaryCup m hm F r - NativeBVNormalizedSource.source m hm F r :=
  (Classical.choose_spec (projection_exists m hm F r)).2

def correction := projectionPrimitive m hm F r + NativeBVNormalizedSource.sourceCorrection m hm F r

theorem correction_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1) + 1)
    (NativeGHPowers.degree m (r + 1)) ≫ correction m hm F r =
      ordinaryCup m hm F r - NativeBVSourceEvaluation.source m hm F r := by
  rw [correction, Preadditive.comp_add, projection_boundary, NativeBVNormalizedSource.source_boundary]
  abel

theorem correction_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1)) (correction m hm F r) = 0 := by
  change (push (GlobalTimeCupConstantsVanish.inclusion (m + 1))).f _ ≫ (_ + _) = 0
  rw [Preadditive.comp_add]
  exact (congrArg₂ (· + ·) (projection_constants_zero m hm F r)
    (NativeBVNormalizedSource.sourceCorrection_constants_zero m hm F r)).trans (zero_add _)

def test : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (ordinaryCup m hm F r)

theorem test_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1)) (test m hm F r) = 0 :=
  SelfSweepCochain.closed _ _ _ (ordinaryCup_closed m hm F r)

theorem test_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1)) (test m hm F r) = 0 :=
  NativeBVRelativeCochain.rotation_constants_zero _ _ _ (ordinaryCup_constants_zero m hm F r)

def rotatedCorrection : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) - 1) :=
  (H1LoopRotation.chainHomotopy (m + 1)).hom (NativeGHPowers.degree m (r + 1) - 1)
    (NativeGHPowers.degree m (r + 1)) ≫ correction m hm F r

theorem rotated_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
    (NativeGHPowers.degree m (r + 1) - 1) ≫ rotatedCorrection m hm F r =
      test m hm F r - NativeBVSourceEvaluation.test m hm F r := by
  unfold rotatedCorrection
  rw [NativeBVRelativeCochain.boundary_at (m + 1) _ _ (NativeGHPowers.degree m (r + 1) + 1)
    (by have := NativeGHPowers.degree_ge m (r + 1); omega) rfl, correction_boundary, Preadditive.comp_sub]
  rfl

theorem rotated_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1) - 1) (rotatedCorrection m hm F r) = 0 :=
  NativeBVRelativeCochain.rotation_constants_zero_at (m + 1) _ _
    (by have := NativeGHPowers.degree_ge m (r + 1); omega) _ (correction_constants_zero m hm F r)

theorem cycle_values : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ test m hm F r =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeBVSourceEvaluation.test m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary m hm F r, ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

theorem relative_cycle_values {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains (Loops (m + 1))).X (NativeGHPowers.degree m (r + 1)))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f (NativeGHPowers.degree m (r + 1))) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d
        (NativeGHPowers.degree m (r + 1)) (NativeGHPowers.degree m (r + 1) - 1) = 0) :
    u ≫ test m hm F r = u ≫ NativeBVSourceEvaluation.test m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary m hm F r]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (rotated_constants_zero m hm F r)

theorem coefficient_on_cycle (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) : NativeBVOriginalScalar.coefficient m hm P v₀ r =
    ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ test m hm F r).hom c := by
  rw [cycle_values]
  exact NativeBVSourceEvaluation.coefficient_on_cycle m hm F r P v₀ c hc

end
end Finsler.NativeBVSourceCupProjection
