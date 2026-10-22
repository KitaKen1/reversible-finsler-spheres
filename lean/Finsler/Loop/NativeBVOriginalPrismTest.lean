module

public import Finsler.Loop.NativeRaisedBVCandidates
public import Finsler.Loop.NativeBVOriginalScalar

/-! The remaining BV coefficient is the actual original rotation-prism
value on ANY cycle representing the concrete raised cube, tested with the
SAME original high-power GH/evaluation cochain. -/
@[expose] public section
namespace Finsler.NativeBVOriginalPrismTest
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.MeridianLoopFamily Finsler.SmallChainCarrier
open Finsler.NativeThetaBVShiftBridge Finsler.NativeBVOriginalScalar
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

def test (m r : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) :=
  CochainDegreeTransport.pre (Loops (m + 1)) (degree_match m r)
    (classRepr (Loops (m + 1)) (NativeThetaPowers.degree m r) (NativeHighPowerUnitComparison.ghEvaluationTest m r))

theorem test_closed (m r : ℕ) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) (test m r) = 0 :=
  CochainDegreeTransport.closed (Loops (m + 1)) (degree_match m r) _ (classRepr_isCocycle _ _ _)

private theorem pairing_transport (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (φ : singularCochainGroup (ZMod 2) X j) (hφ : cochainCoboundary (ZMod 2) X j φ = 0)
    (z : homologyZMod2 X i) :
    (kroneckerMap X j).hom (cocycleClass X j φ hφ)
      ((eqToHom (congrArg (homologyZMod2 X) h)).hom z) =
    (kroneckerMap X i).hom
      (cocycleClass X i (CochainDegreeTransport.pre X h φ) (CochainDegreeTransport.closed X h φ hφ)) z := by
  subst j
  simp only [eqToHom_refl, ModuleCat.hom_id, LinearMap.id_apply, CochainDegreeTransport.pre, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))
  (P : Sphere (m + 1)) (v₀ : equator P)

theorem coefficient_on_cycle (r : ℕ) (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    coefficient m hm P v₀ r =
      (((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
        (H1LoopRotation.chainHomotopy (m + 1)).hom (NativeGHPowers.degree m (r + 1))
          (NativeGHPowers.degree m (r + 1) + 1)) ≫ test m r).hom c := by
  have hs := NativeThetaCoefficientSixQuarters.sweep_pairing (H1LoopRotation.chainHomotopy (m + 1))
    (NativeGHPowers.degree m (r + 1)) (test m r) (test_closed m r) c
  rw [hc] at hs
  have ht := pairing_transport (Loops (m + 1)) (degree_match m r)
    (classRepr _ _ (NativeHighPowerUnitComparison.ghEvaluationTest m r)) (classRepr_isCocycle _ _ _)
    ((H1LoopRotation.BV (m + 1) (NativeGHPowers.degree m (r + 1))).hom
      (NativeRaisedBVCandidates.full m hm F P v₀ r))
  rw [cocycleClass_classRepr] at ht
  unfold coefficient
  rw [← NativeRaisedBVCandidates.full_eq_detector m hm F P v₀ r]
  exact ht.trans hs

theorem detectsTheta_iff_prism_one (r : ℕ)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    detectsTheta m hm F P v₀ r ↔
      (((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
        (H1LoopRotation.chainHomotopy (m + 1)).hom (NativeGHPowers.degree m (r + 1))
          (NativeGHPowers.degree m (r + 1) + 1)) ≫ test m r).hom c = 1 := by
  rw [← coefficient_on_cycle m hm F P v₀ r c hc]
  exact (coefficient_one_iff m hm F P v₀ r).symm

end
end Finsler.NativeBVOriginalPrismTest
