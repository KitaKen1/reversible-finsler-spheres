module

public import Finsler.Loop.ComplementCapTimeNaturality
public import Finsler.Loop.NativeBVComplementTest

/-! Move the SAME original high-GH/evaluation test's complement across
the ORIGINAL normalized Thom cap. Every original BV coefficient is now
the value of the ORIGINAL source rotation, cut-time prism, complement
on cut parameters, and original Thom cap, in that order. Actual
subdivision and Thom errors are one constant-relative boundary. -/
@[expose] public section
namespace Finsler.NativeBVComplementCapTest
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.MeridianLoopFamily Finsler.NativeInnerCutPullback
open Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

private theorem boundary_pre {X : TopCat.{0}} {i j a b : ℕ} (hi : i = a) (hj : j = b)
    (K : singularCochainGroup (ZMod 2) X a) (T U : singularCochainGroup (ZMod 2) X b)
    (h : (chains X).d b a ≫ K = T - U) :
    (chains X).d j i ≫ CochainDegreeTransport.pre X hi K =
      CochainDegreeTransport.pre X hj T - CochainDegreeTransport.pre X hj U := by
  subst a b
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using h

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def near : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) (NativeClosingArcPowerVanishing.radius m hm F)))
    (NativeGHPowers.degree m r + m + 1) :=
  CupOne.cup _ (m + 1) (NativeGHPowers.degree m r) (NativeGHPowers.degree m r + m + 1) (by omega)
    (cochainPullback (TopCat.ofHom (tested (m + 1) (radiusLe m hm F))) (m + 1) (NativeBVGeometricTest.evaluation m))
    (cochainPullback (TopCat.ofHom (retained (m + 1) (radiusLe m hm F))) (NativeGHPowers.degree m r)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F r))

theorem near_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m r + m + 1) (near m hm F r) = 0 :=
  CupCapOrder.closed _ _ _ _ _ _ _
    (cochainPullback_cocycle _ _ _ (NativeBVGeometricTest.evaluation_closed m))
    (cochainPullback_cocycle _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r))

private theorem rho_le_two : NativeOrderedDoubleCutSupported.thomRadius m hm F ≤ 2 :=
  (rhoLt m hm F).le.trans ((radiusLe m hm F).trans (by norm_num))

def test : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) :=
  CochainDegreeTransport.pre _ (by have := NativeBVReorderedTest.degree_match m r; omega)
    (ComplementCapTimeNaturality.before m (rhoPos m hm F) (rhoLt m hm F)
      (NativeGHPowers.degree m r + m + 1) (near m hm F r))

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  ComplementCapTimeNaturality.primitive m (by omega) (rhoPos m hm F)
    (by exact (rhoLt m hm F).le.trans ((radiusLe m hm F).trans (by norm_num))) (rhoLt m hm F)
    (NativeGHPowers.degree m r + m + 1) (near m hm F r) (NativeGHPowers.degree m (r + 1))

theorem previous_test : NativeBVComplementTest.test m hm F r =
    CochainDegreeTransport.pre _ (by have := NativeBVReorderedTest.degree_match m r; omega)
      (ComplementCapTimeNaturality.after m (rhoPos m hm F) (rhoLt m hm F)
        (NativeGHPowers.degree m r + m + 1) (near m hm F r)) := rfl

theorem boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1) + 1)
    (NativeGHPowers.degree m (r + 1)) ≫ primitive m hm F r = test m hm F r - NativeBVComplementTest.test m hm F r := by
  rw [previous_test]
  have he := boundary_pre (X := Loops (m + 1)) rfl
    (show NativeGHPowers.degree m (r + 1) + 1 = m + (NativeGHPowers.degree m r + m + 1) by
      have := NativeBVReorderedTest.degree_match m r; omega)
    _ _ _ (ComplementCapTimeNaturality.boundary m (by omega) (rhoPos m hm F) (rho_le_two m hm F)
      (rhoLt m hm F) (NativeGHPowers.degree m r + m + 1) (near m hm F r)
      (NativeGHPowers.degree m (r + 1)) (by have := NativeBVReorderedTest.degree_match m r; omega) (near_closed m hm F r))
  simpa only [primitive, test, CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using he

theorem test_closed : cochainCoboundary (ZMod 2) (Loops (m + 1))
    (NativeGHPowers.degree m (r + 1) + 1) (test m hm F r) = 0 := by
  have hb := boundary m hm F r
  change cochainCoboundary (ZMod 2) _ _ (primitive m hm F r) = _ at hb
  have he : test m hm F r = cochainCoboundary (ZMod 2) _ _ (primitive m hm F r) + NativeBVComplementTest.test m hm F r :=
    sub_eq_iff_eq_add.mp hb.symm
  rw [he]
  change ((cochainCxZMod2 (Loops (m + 1))).d _ _).hom (_ + _) = 0
  rw [map_add]
  change cochainCoboundary (ZMod 2) _ _ (cochainCoboundary (ZMod 2) _ _ (primitive m hm F r)) +
    cochainCoboundary (ZMod 2) _ _ (NativeBVComplementTest.test m hm F r) = 0
  rw [cochainCoboundary_cochainCoboundary, NativeBVComplementTest.test_closed, zero_add]

theorem primitive_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1))
      (primitive m hm F r) = 0 :=
  ComplementCapTimeNaturality.primitive_constants_zero m (by omega) (rhoPos m hm F) (rho_le_two m hm F) (rhoLt m hm F)
    (NativeGHPowers.degree m r + m + 1) (near m hm F r) (NativeGHPowers.degree m (r + 1))
    (by have := NativeBVReorderedTest.degree_match m r; omega)

def rotatedPrimitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) - 1) :=
  (H1LoopRotation.chainHomotopy (m + 1)).hom (NativeGHPowers.degree m (r + 1) - 1)
    (NativeGHPowers.degree m (r + 1)) ≫ primitive m hm F r

theorem rotated_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
    (NativeGHPowers.degree m (r + 1) - 1) ≫ rotatedPrimitive m hm F r =
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r) -
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVComplementTest.test m hm F r) := by
  have hd := NativeBVReorderedTest.degree_match m r
  unfold rotatedPrimitive SelfSweepCochain.cochain SelfHomotopySweep.component
  rw [NativeBVRelativeCochain.boundary_at (m + 1) _ _ (NativeGHPowers.degree m (r + 1) + 1)
    (by omega) rfl, boundary, Preadditive.comp_sub]

theorem rotatedPrimitive_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1) - 1)
      (rotatedPrimitive m hm F r) = 0 := by
  have hd := NativeBVReorderedTest.degree_match m r
  exact NativeBVRelativeCochain.rotation_constants_zero_at (m + 1) _ _ (by omega) _ (primitive_constants_zero m hm F r)

theorem rotation_relative_values {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains (Loops (m + 1))).X (NativeGHPowers.degree m (r + 1)))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f
      (NativeGHPowers.degree m (r + 1))) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d
        (NativeGHPowers.degree m (r + 1)) (NativeGHPowers.degree m (r + 1) - 1) = 0) :
    u ≫ SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r) =
      u ≫ SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVComplementTest.test m hm F r) := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (rotatedPrimitive_constants_zero m hm F r)

theorem rotation_cycle_values :
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r) =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVComplementTest.test m hm F r) := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary, ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

theorem coefficient_on_cycle (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    NativeBVOriginalScalar.coefficient m hm P v₀ r =
      ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
        SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r)).hom c := by
  rw [rotation_cycle_values]
  exact NativeBVComplementTest.coefficient_on_cycle m hm F r P v₀ c hc

end
end Finsler.NativeBVComplementCapTest
