module

public import Finsler.Loop.NativeBVThomCupOne
public import Finsler.Loop.NativeBVDefectCochain
public import Finsler.Loop.NativeBVCutTestBoundary

/-! Apply the actual near-space cup-one correction to the SAME supported
GH power and normalized evaluation test. The new representative has
retained evaluation first in the ordinary cup; its two cut-output maps
have NOT been exchanged. Its original BV value is exactly unchanged. -/
@[expose] public section
namespace Finsler.NativeBVReorderedTest
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedSelfCut Finsler.MeridianLoopFamily
open Finsler.NativeInnerCutPullback
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

private theorem source_cup_pre (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r)
    (p q j i : ℕ) (h : p + q = j) (hi : i = m + j)
    (A : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) p)
    (B : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q) :
    CochainDegreeTransport.pre _ hi (NativeBVThomBoundary.source m hρ hρr j (CupOne.cup _ p q j h A B)) =
    CochainDegreeTransport.pre _ (hi.trans (congrArg (m + ·) h.symm))
      (NativeBVThomBoundary.source m hρ hρr (p + q) (cochainCup p q A B)) := by
  subst j
  rw [CupOne.cup_comparison]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def tested : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) (NativeClosingArcPowerVanishing.radius m hm F)))
    (NativeGHPowers.degree m r) :=
  NormalizedSelfCut.testedCocycle (m + 1) _ (radiusLe m hm F)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r)

def retained : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) (NativeClosingArcPowerVanishing.radius m hm F))) (m + 1) :=
  cochainPullback (TopCat.ofHom (SupportedSelfCut.retained (m + 1) (radiusLe m hm F)))
    (m + 1) (NativeBVGeometricTest.evaluation m)

theorem tested_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m r) (tested m hm F r) = 0 :=
  cochainPullback_cocycle _ _ _ (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r)

theorem retained_closed : cochainCoboundary (ZMod 2) _ (m + 1) (retained m hm F) = 0 :=
  cochainPullback_cocycle _ _ _ (NativeBVGeometricTest.evaluation_closed m)

theorem degree_match : NativeGHPowers.degree m (r + 1) = m + (NativeGHPowers.degree m r + m) := by
  rw [NativeGHPowers.degree]
  omega

def primitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  CochainDegreeTransport.pre _ (degree_match m r)
    (NativeBVThomCupOne.primitive m (rhoPos m hm F) (rhoLt m hm F)
      (NativeGHPowers.degree m r) (m + 1) (NativeGHPowers.degree m r + m) (by omega)
      (tested m hm F r) (retained m hm F))

def test : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) :=
  CochainDegreeTransport.pre _ (by have := degree_match m r; omega)
    (NativeBVThomCupOne.reordered m (rhoPos m hm F) (rhoLt m hm F)
      (NativeGHPowers.degree m r) (m + 1) (NativeGHPowers.degree m r + m) (by omega)
      (tested m hm F r) (retained m hm F))

theorem original_ordered : NativeBVGeometricTest.test m hm F r =
    CochainDegreeTransport.pre _ (by have := degree_match m r; omega)
      (NativeBVThomCupOne.ordered m (rhoPos m hm F) (rhoLt m hm F)
        (NativeGHPowers.degree m r) (m + 1) (NativeGHPowers.degree m r + m) (by omega)
        (tested m hm F r) (retained m hm F)) := by
  have hc := NativeBVCutTestBoundary.source_geometric m (rhoPos m hm F) (rhoLt m hm F)
    (radiusLe m hm F) (NativeGHPowers.degree m r) (m + 1)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r) (NativeBVGeometricTest.evaluation m)
  unfold NativeBVGeometricTest.test NativeBVGeometricTest.raw
  rw [← hc]
  unfold NativeBVThomCupOne.ordered
  rw [source_cup_pre]
  unfold CochainDegreeTransport.pre
  rw [← Category.assoc, eqToHom_trans]
  rfl

theorem boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1) + 1)
    (NativeGHPowers.degree m (r + 1)) ≫ primitive m hm F r =
      NativeBVGeometricTest.test m hm F r - test m hm F r := by
  rw [original_ordered]
  exact boundary_pre (degree_match m r) (by have := degree_match m r; omega) _ _ _
    (NativeBVThomCupOne.boundary m (rhoPos m hm F) (rhoLt m hm F) _ _ _ _
      (tested m hm F r) (retained m hm F) (tested_closed m hm F r) (retained_closed m hm F))

theorem test_closed : cochainCoboundary (ZMod 2) (Loops (m + 1))
    (NativeGHPowers.degree m (r + 1) + 1) (test m hm F r) = 0 := by
  have hb := boundary m hm F r
  have he : test m hm F r = NativeBVGeometricTest.test m hm F r -
      cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1)) (primitive m hm F r) := by
    change cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1)) (primitive m hm F r) =
      NativeBVGeometricTest.test m hm F r - test m hm F r at hb
    rw [hb]
    abel
  rw [he]
  change ((cochainCxZMod2 (Loops (m + 1))).d _ _).hom (_ - _) = 0
  rw [map_sub]
  change cochainCoboundary (ZMod 2) _ _ (NativeBVGeometricTest.test m hm F r) -
    cochainCoboundary (ZMod 2) _ _ (cochainCoboundary (ZMod 2) _ _ (primitive m hm F r)) = 0
  rw [NativeBVGeometricTest.test_closed, cochainCoboundary_cochainCoboundary, sub_self]

theorem test_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1) + 1)
      (test m hm F r) = 0 := by
  unfold test NativeBVThomCupOne.reordered
  rw [pullback_pre, NativeBVThomBoundary.source_constants_zero]
  exact comp_zero

theorem primitive_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1))
      (primitive m hm F r) = 0 := by
  unfold primitive
  rw [pullback_pre, NativeBVThomCupOne.primitive_constants_zero]
  exact comp_zero

def rotatedPrimitive : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) - 1) :=
  (H1LoopRotation.chainHomotopy (m + 1)).hom (NativeGHPowers.degree m (r + 1) - 1)
    (NativeGHPowers.degree m (r + 1)) ≫ primitive m hm F r

theorem rotated_boundary : (chains (Loops (m + 1))).d (NativeGHPowers.degree m (r + 1))
    (NativeGHPowers.degree m (r + 1) - 1) ≫ rotatedPrimitive m hm F r =
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVGeometricTest.test m hm F r) -
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (test m hm F r) := by
  have hd := degree_match m r
  unfold rotatedPrimitive SelfSweepCochain.cochain SelfHomotopySweep.component
  rw [NativeBVRelativeCochain.boundary_at (m + 1) _ _ (NativeGHPowers.degree m (r + 1) + 1)
    (by omega) rfl, boundary, Preadditive.comp_sub]

theorem rotatedPrimitive_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1) - 1)
      (rotatedPrimitive m hm F r) = 0 := by
  have hd := degree_match m r
  exact NativeBVRelativeCochain.rotation_constants_zero_at (m + 1) _ _ (by omega) _
    (primitive_constants_zero m hm F r)

theorem rotation_cycle_values :
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVGeometricTest.test m hm F r) =
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
  exact NativeBVGeometricTest.coefficient_on_cycle m hm F P v₀ r c hc

end
end Finsler.NativeBVReorderedTest
