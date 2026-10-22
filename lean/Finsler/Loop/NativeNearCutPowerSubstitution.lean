module

public import Finsler.Loop.NativeNearCutOriginalThom
public import Finsler.Loop.NativeBVTestedTransgression

/-! Cup the ACTUAL near rejoining primitive with the SAME retained GH_r,
then use the ORIGINAL Thom/time operation. The resulting relative
boundary identifies a source-GH_0 test with GH_(r+1) plus ONE retained
ordinary-cup remainder. The remainder is not assumed zero and this is
not a source/output BV transfer theorem. -/
@[expose] public section
namespace Finsler.NativeNearCutPowerSubstitution
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

private theorem cast_boundary (X : TopCat.{0}) (i j : ℕ) (h : i + 1 = j)
    (K : singularCochainGroup (ZMod 2) X i) :
    cochainCast h (cochainCoboundary (ZMod 2) X i K) = (chains X).d j i ≫ K := by
  subst j
  rfl

private theorem cup_boundary (X : TopCat.{0}) (i j q : ℕ) (h : i + 1 = j)
    (K : singularCochainGroup (ZMod 2) X i) (B : singularCochainGroup (ZMod 2) X q)
    (hB : cochainCoboundary (ZMod 2) X q B = 0) :
    (chains X).d (j + q) (i + q) ≫ cochainCup i q K B =
      cochainCup j q ((chains X).d j i ≫ K) B := by
  subst j
  have he := cochainCupZMod2_coboundary_left' i q K B hB
  rw [cast_boundary _ _ _ (by omega)] at he
  exact he.symm

private theorem boundary_pre {X : TopCat.{0}} {i j a b : ℕ} (hi : i = a) (hj : j = b)
    (K : singularCochainGroup (ZMod 2) X a) (T : singularCochainGroup (ZMod 2) X b)
    (h : (chains X).d b a ≫ K = T) :
    (chains X).d j i ≫ CochainDegreeTransport.pre X hi K = CochainDegreeTransport.pre X hj T := by
  subst a b
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using h

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (K : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h K) =
      CochainDegreeTransport.pre X h (cochainPullback f j K) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def retainedPower : singularCochainGroup (ZMod 2) (NativeNearCutOriginalThom.space m hm F)
    (NativeGHPowers.degree m r) :=
  cochainPullback (TopCat.ofHom (retained (m + 1) (radiusLe m hm F))) (NativeGHPowers.degree m r)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r)

theorem retainedPower_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m r)
    (retainedPower m hm F r) = 0 :=
  cochainPullback_cocycle _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r)

def nearPrimitive : singularCochainGroup (ZMod 2) (NativeNearCutOriginalThom.space m hm F)
    ((m - 1) + NativeGHPowers.degree m r) :=
  cochainCup (m - 1) (NativeGHPowers.degree m r)
    (NativeNearCutOriginalThom.primitive m hm F) (retainedPower m hm F r)

def nearSource : singularCochainGroup (ZMod 2) (NativeNearCutOriginalThom.space m hm F)
    (m + NativeGHPowers.degree m r) :=
  cochainCup m (NativeGHPowers.degree m r)
    (NativeNearCutOriginalThom.before m hm F) (retainedPower m hm F r)

def nearRemainder : singularCochainGroup (ZMod 2) (NativeNearCutOriginalThom.space m hm F)
    (m + NativeGHPowers.degree m r) :=
  cochainPullback (TopCat.ofHom (retained (m + 1) (radiusLe m hm F))) (m + NativeGHPowers.degree m r)
    (cochainCup m (NativeGHPowers.degree m r) (NativeNearCutPrimitiveGH.original m hm F)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F r))

theorem nearSource_closed : cochainCoboundary (ZMod 2) _ (m + NativeGHPowers.degree m r)
    (nearSource m hm F r) = 0 :=
  cochainCupZMod2_respects_cocycles _ _ _ _
    (cochainPullback_cocycle _ _ _ (NativeNearCutPrimitiveGH.original_closed m hm F))
    (retainedPower_closed m hm F r)

theorem nearRemainder_closed : cochainCoboundary (ZMod 2) _ (m + NativeGHPowers.degree m r)
    (nearRemainder m hm F r) = 0 :=
  cochainPullback_cocycle _ _ _ (cochainCupZMod2_respects_cocycles _ _ _ _
    (NativeNearCutPrimitiveGH.original_closed m hm F)
    (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r))

theorem near_outputs : cochainCup m (NativeGHPowers.degree m r)
    (NativeNearCutOriginalThom.after m hm F) (retainedPower m hm F r) =
      GeometricTimeCupCochain.splitCup m m (radiusLe m hm F)
        (NativeNearCutPrimitiveGH.original m hm F) (NativeGHPowers.degree m r)
        (NativeClosingArcPowerVanishing.powerCocycle m hm F r) + nearRemainder m hm F r := by
  unfold NativeNearCutOriginalThom.after nearRemainder
  rw [cochainCup_naturality]
  exact map_add (cupRightMor _ m (NativeGHPowers.degree m r) (retainedPower m hm F r)).hom _ _

theorem near_boundary : (chains (NativeNearCutOriginalThom.space m hm F)).d
    (m + NativeGHPowers.degree m r) ((m - 1) + NativeGHPowers.degree m r) ≫ nearPrimitive m hm F r =
      nearSource m hm F r -
        (GeometricTimeCupCochain.splitCup m m (radiusLe m hm F)
          (NativeNearCutPrimitiveGH.original m hm F) (NativeGHPowers.degree m r)
          (NativeClosingArcPowerVanishing.powerCocycle m hm F r) + nearRemainder m hm F r) := by
  unfold nearPrimitive
  rw [cup_boundary _ _ _ _ (by omega) _ _ (retainedPower_closed m hm F r),
    NativeNearCutOriginalThom.primitive_boundary]
  have hs := map_sub (cupRightMor (NativeNearCutOriginalThom.space m hm F) m
    (NativeGHPowers.degree m r) (retainedPower m hm F r)).hom
    (NativeNearCutOriginalThom.before m hm F) (NativeNearCutOriginalThom.after m hm F)
  change cochainCup m (NativeGHPowers.degree m r) (_ - _) _ = _ at hs
  exact hs.trans (congrArg (fun a => nearSource m hm F r - a) (near_outputs m hm F r))

theorem parameter_endpoints (t : IntervalSobolev.ClosedInterval) (ht : t = 0 ∨ t = 1) :
    cochainPullback (SelfCutThomCocycle.atTime (m + 1) t)
      ((m + 1) + ((m - 1) + NativeGHPowers.degree m r))
      (NativeBVThomBoundary.parameter m (rhoPos m hm F) (rhoLt m hm F) _ (nearPrimitive m hm F r)) = 0 :=
  NativeBVThomBoundary.parameter_endpoint _ _ _ _ _ t ht

theorem parameter_diagonal {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
    (hf : ∀ x, f x ∈ FilteredGlobalThomTime.endpointCarrier (m + 1)) :
    cochainPullback f ((m + 1) + ((m - 1) + NativeGHPowers.degree m r))
      (NativeBVThomBoundary.parameter m (rhoPos m hm F) (rhoLt m hm F) _ (nearPrimitive m hm F r)) = 0 :=
  NativeBVThomBoundary.parameter_diagonal _ _ _ _ _ f hf

theorem parameter_far {X : TopCat.{0}} (f : X ⟶ SelfCutThomCocycle.parameters (m + 1))
    (hf : ∀ x, f x ∈ exterior (m + 1) (NativeOrderedDoubleCutSupported.thomRadius m hm F)) :
    cochainPullback f ((m + 1) + ((m - 1) + NativeGHPowers.degree m r))
      (NativeBVThomBoundary.parameter m (rhoPos m hm F) (rhoLt m hm F) _ (nearPrimitive m hm F r)) = 0 :=
  NativeBVThomBoundary.parameter_far _ _ _ _ _ f hf

theorem degree_match : NativeGHPowers.degree m (r + 1) = m + (m + NativeGHPowers.degree m r) := by
  rw [NativeGHPowers.degree]
  omega

include hm in
theorem primitive_degree : NativeGHPowers.degree m (r + 1) - 1 =
    m + ((m - 1) + NativeGHPowers.degree m r) := by
  rw [degree_match]
  omega

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) - 1) :=
  CochainDegreeTransport.pre _ (primitive_degree m hm r)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F)
      ((m - 1) + NativeGHPowers.degree m r) (nearPrimitive m hm F r))

def sourceTest : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  CochainDegreeTransport.pre _ (degree_match m r)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F)
      (m + NativeGHPowers.degree m r) (nearSource m hm F r))

def remainder : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  CochainDegreeTransport.pre _ (degree_match m r)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F)
      (m + NativeGHPowers.degree m r) (nearRemainder m hm F r))

theorem sourceTest_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1))
    (sourceTest m hm F r) = 0 :=
  CochainDegreeTransport.closed _ _ _ (DegreeLoweringCochainPullback.closed
    (GlobalThomTime.operation m (rhoPos m hm F) (rhoLt m hm F)) _ _ (nearSource_closed m hm F r))

theorem remainder_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1))
    (remainder m hm F r) = 0 :=
  CochainDegreeTransport.closed _ _ _ (DegreeLoweringCochainPullback.closed
    (GlobalThomTime.operation m (rhoPos m hm F) (rhoLt m hm F)) _ _ (nearRemainder_closed m hm F r))

theorem tested_term : CochainDegreeTransport.pre _ (degree_match m r)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F)
      (m + NativeGHPowers.degree m r)
      (GeometricTimeCupCochain.splitCup m m (radiusLe m hm F)
        (NativeNearCutPrimitiveGH.original m hm F) (NativeGHPowers.degree m r)
        (NativeClosingArcPowerVanishing.powerCocycle m hm F r))) =
      NativeBVTestedTransgression.after m hm F r :=
  NativeBVCutTestBoundary.source_geometric m (rhoPos m hm F) (rhoLt m hm F)
    (radiusLe m hm F) m (NativeGHPowers.degree m r) _ _

theorem boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
    (NativeGHPowers.degree m (r + 1) - 1) ≫ primitive m hm F r =
      sourceTest m hm F r - (NativeBVTestedTransgression.after m hm F r + remainder m hm F r) := by
  have hb := NativeBVThomBoundary.lowering_boundary_at
    (GlobalThomTime.operation m (rhoPos m hm F) (rhoLt m hm F))
    ((m - 1) + NativeGHPowers.degree m r) (m + NativeGHPowers.degree m r) (by omega)
    (nearPrimitive m hm F r)
  rw [near_boundary, Preadditive.comp_sub, Preadditive.comp_add] at hb
  have h := boundary_pre (primitive_degree m hm r) (degree_match m r) _ _ hb
  simp only [CochainDegreeTransport.pre, Preadditive.comp_sub, Preadditive.comp_add] at h
  change (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
      (NativeGHPowers.degree m (r + 1) - 1) ≫ primitive m hm F r =
    sourceTest m hm F r - (CochainDegreeTransport.pre _ (degree_match m r)
      (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F)
        (m + NativeGHPowers.degree m r)
        (GeometricTimeCupCochain.splitCup m m (radiusLe m hm F)
          (NativeNearCutPrimitiveGH.original m hm F) (NativeGHPowers.degree m r)
          (NativeClosingArcPowerVanishing.powerCocycle m hm F r))) + remainder m hm F r) at h
  rw [tested_term] at h
  exact h

theorem primitive_constants_zero : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
    (NativeGHPowers.degree m (r + 1) - 1) (primitive m hm F r) = 0 := by
  unfold primitive
  rw [pullback_pre, NativeBVThomBoundary.source_constants_zero]
  exact comp_zero

theorem relative_cycle_values {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains (Loops (m + 1))).X (NativeGHPowers.degree m (r + 1)))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f
      (NativeGHPowers.degree m (r + 1))) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d
        (NativeGHPowers.degree m (r + 1)) (NativeGHPowers.degree m (r + 1) - 1) = 0) :
    u ≫ sourceTest m hm F r = u ≫ NativeBVTestedTransgression.after m hm F r + u ≫ remainder m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_add, ← Preadditive.comp_sub, ← boundary m hm F r]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (primitive_constants_zero m hm F r)

theorem cycle_values : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ sourceTest m hm F r =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeBVTestedTransgression.after m hm F r +
      (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ remainder m hm F r := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_add, ← Preadditive.comp_sub, ← boundary m hm F r, ← Category.assoc,
    HomologicalComplex.iCycles_d, zero_comp]

theorem value_one_plus_remainder (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ sourceTest m hm F r).hom c =
      1 + ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ remainder m hm F r).hom c := by
  rw [cycle_values]
  change ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
      NativeBVTestedTransgression.after m hm F r).hom c +
    ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ remainder m hm F r).hom c =
      1 + ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ remainder m hm F r).hom c
  congr 1
  calc
    _ = (kroneckerMap _ _).hom (cocycleClass _ _ (NativeBVTestedTransgression.after m hm F r)
        (NativeBVTestedTransgression.after_closed m hm F r))
        (((chains (Loops (m + 1))).homologyπ _).hom c) := by
      rw [kroneckerMap_cocycleClass]
      exact (kroneckerFunctional_apply _ _ _ (NativeBVTestedTransgression.after_closed m hm F r) c).symm
    _ = 1 := by
      rw [NativeBVTestedTransgression.after_class, hc]
      exact NativeRaisedBVCandidates.pairing_one m hm F P v₀ r

end
end Finsler.NativeNearCutPowerSubstitution
