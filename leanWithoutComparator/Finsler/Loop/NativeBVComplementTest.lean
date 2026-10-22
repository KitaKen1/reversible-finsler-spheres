module

public import Finsler.Loop.NativeComplementOutputCochain
public import Finsler.Loop.NativeBVReorderedTest

/-! Apply the actual simultaneous complementary-output H1 homotopy to
the SAME evaluation and GH cocycles. Transport its concrete primitive
through the ORIGINAL Thom/time and rotation maps. Every original c_r is
now computed using the genuinely complemented near-space split test.
This does not yet move complement across the Thom/time insertion. -/
@[expose] public section
namespace Finsler.NativeBVComplementTest
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.MeridianLoopFamily Finsler.NativeInnerCutPullback
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

private theorem boundary_pre {X : TopCat.{0}} {i j a b : ℕ} (hi : i = a) (hj : j = b)
    (K : singularCochainGroup (ZMod 2) X a)
    (T U : singularCochainGroup (ZMod 2) X b)
    (h : (chains X).d b a ≫ K = T - U) :
    (chains X).d j i ≫ CochainDegreeTransport.pre X hi K =
      CochainDegreeTransport.pre X hj T - CochainDegreeTransport.pre X hj U := by
  subst a b
  simpa only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp] using h

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (K : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h K) =
      CochainDegreeTransport.pre X h (cochainPullback f j K) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  CochainDegreeTransport.pre _ (NativeBVReorderedTest.degree_match m r)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) (NativeGHPowers.degree m r + m)
      (NativeComplementOutputCochain.primitive (m + 1) (radiusLe m hm F)
        (m + 1) (NativeGHPowers.degree m r) (NativeGHPowers.degree m r + m) (by omega)
        (NativeBVGeometricTest.evaluation m) (NativeClosingArcPowerVanishing.powerCocycle m hm F r)))

def test : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) :=
  CochainDegreeTransport.pre _ (by have := NativeBVReorderedTest.degree_match m r; omega)
    (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) (NativeGHPowers.degree m r + m + 1)
      (NativeComplementOutputCochain.complemented (m + 1) (radiusLe m hm F)
        (m + 1) (NativeGHPowers.degree m r) (NativeGHPowers.degree m r + m) (by omega)
        (NativeBVGeometricTest.evaluation m) (NativeClosingArcPowerVanishing.powerCocycle m hm F r)))

theorem reordered_original : NativeBVReorderedTest.test m hm F r =
    CochainDegreeTransport.pre _ (by have := NativeBVReorderedTest.degree_match m r; omega)
      (NativeBVThomBoundary.source m (rhoPos m hm F) (rhoLt m hm F) (NativeGHPowers.degree m r + m + 1)
        (NativeComplementOutputCochain.original (m + 1) (radiusLe m hm F)
          (m + 1) (NativeGHPowers.degree m r) (NativeGHPowers.degree m r + m) (by omega)
          (NativeBVGeometricTest.evaluation m) (NativeClosingArcPowerVanishing.powerCocycle m hm F r))) := rfl

theorem boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1) + 1)
    (NativeGHPowers.degree m (r + 1)) ≫ primitive m hm F r =
      NativeBVReorderedTest.test m hm F r - test m hm F r := by
  rw [reordered_original]
  apply boundary_pre (NativeBVReorderedTest.degree_match m r) (by have := NativeBVReorderedTest.degree_match m r; omega)
  unfold NativeBVThomBoundary.source
  rw [NativeBVThomBoundary.lowering_boundary_at (GlobalThomTime.operation m (rhoPos m hm F) (rhoLt m hm F))
    (NativeGHPowers.degree m r + m) (NativeGHPowers.degree m r + m + 1) rfl]
  change _ ≫ cochainCoboundary (ZMod 2) _ _ (NativeComplementOutputCochain.primitive _ _ _ _ _ _ _ _) = _
  rw [NativeComplementOutputCochain.boundary _ _ _ _ _ _ _ _
    (NativeBVGeometricTest.evaluation_closed m) (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r),
    Preadditive.comp_sub]

theorem test_closed : cochainCoboundary (ZMod 2) (Loops (m + 1))
    (NativeGHPowers.degree m (r + 1) + 1) (test m hm F r) = 0 := by
  have hb := boundary m hm F r
  change cochainCoboundary (ZMod 2) _ _ (primitive m hm F r) =
    NativeBVReorderedTest.test m hm F r - test m hm F r at hb
  have he : test m hm F r = NativeBVReorderedTest.test m hm F r -
      cochainCoboundary (ZMod 2) _ _ (primitive m hm F r) := by rw [hb]; abel
  rw [he]
  change ((cochainCxZMod2 (Loops (m + 1))).d _ _).hom (_ - _) = 0
  rw [map_sub]
  change cochainCoboundary (ZMod 2) _ _ (NativeBVReorderedTest.test m hm F r) -
    cochainCoboundary (ZMod 2) _ _ (cochainCoboundary (ZMod 2) _ _ (primitive m hm F r)) = 0
  rw [NativeBVReorderedTest.test_closed, cochainCoboundary_cochainCoboundary, sub_self]

theorem test_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1) + 1)
      (test m hm F r) = 0 := by
  unfold test
  rw [pullback_pre, NativeBVThomBoundary.source_constants_zero]
  exact comp_zero

theorem primitive_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1))
      (primitive m hm F r) = 0 := by
  unfold primitive
  rw [pullback_pre, NativeBVThomBoundary.source_constants_zero]
  exact comp_zero

def rotatedPrimitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) - 1) :=
  (H1LoopRotation.chainHomotopy (m + 1)).hom (NativeGHPowers.degree m (r + 1) - 1)
    (NativeGHPowers.degree m (r + 1)) ≫ primitive m hm F r

theorem rotated_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
    (NativeGHPowers.degree m (r + 1) - 1) ≫ rotatedPrimitive m hm F r =
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVReorderedTest.test m hm F r) -
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r) := by
  have hd := NativeBVReorderedTest.degree_match m r
  unfold rotatedPrimitive SelfSweepCochain.cochain SelfHomotopySweep.component
  rw [NativeBVRelativeCochain.boundary_at (m + 1) _ _ (NativeGHPowers.degree m (r + 1) + 1)
    (by omega) rfl, boundary, Preadditive.comp_sub]

theorem rotatedPrimitive_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1) - 1)
      (rotatedPrimitive m hm F r) = 0 := by
  have hd := NativeBVReorderedTest.degree_match m r
  exact NativeBVRelativeCochain.rotation_constants_zero_at (m + 1) _ _ (by omega) _
    (primitive_constants_zero m hm F r)

theorem rotation_relative_values {M : ModuleCat.{0} (ZMod 2)}
    (u : M ⟶ (chains (Loops (m + 1))).X (NativeGHPowers.degree m (r + 1)))
    (hu : (u ≫ ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplexπ coeff).f
      (NativeGHPowers.degree m (r + 1))) ≫
      ((RelativePrismSweep.targetPair (consts (m + 1))).singularChainComplex coeff).d
        (NativeGHPowers.degree m (r + 1)) (NativeGHPowers.degree m (r + 1) - 1) = 0) :
    u ≫ SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVReorderedTest.test m hm F r) =
      u ≫ SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r) := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary]
  exact NativeBVThomBoundary.relative_boundary_zero (RelativePrismSweep.targetPair (consts (m + 1)))
    _ _ u hu _ (rotatedPrimitive_constants_zero m hm F r)

theorem rotation_cycle_values :
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVReorderedTest.test m hm F r) =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r) := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← rotated_boundary, ← Category.assoc, HomologicalComplex.iCycles_d, zero_comp]

theorem coefficient_on_cycle (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    NativeBVOriginalScalar.coefficient m hm P v₀ r =
      ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
        SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r)).hom c := by
  rw [← rotation_cycle_values]
  exact NativeBVReorderedTest.coefficient_on_cycle m hm F r P v₀ c hc

end
end Finsler.NativeBVComplementTest
