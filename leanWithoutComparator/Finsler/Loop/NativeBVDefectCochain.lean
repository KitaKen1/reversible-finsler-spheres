module

public import Finsler.Loop.NativeBVGeometricTest
public import Finsler.Loop.NativeBVScalarRecurrence
public import Finsler.Loop.NativeBVCutOutputCorrection
public import Finsler.Loop.NativeBVRelativeCochain

/-! The ORIGINAL adjacent BV-coefficient obstruction as ONE actual
cochain on the SAME source. Both terms use the genuine rotation prism,
the original geometric GH/evaluation test and original primitive cut.
Its value is identified, not assumed zero. -/
@[expose] public section
namespace Finsler.NativeBVDefectCochain
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (K : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h K) =
      CochainDegreeTransport.pre X h (cochainPullback f j K) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1))

theorem cut_homology (q : ℕ) : (NativeBVCutOutputCorrection.cut m hm F 0).homology q =
    CanonicalGlobalSelfCut.map m m q (MeridianLoopClass.H1TransgressionClass m) := by
  unfold NativeBVCutOutputCorrection.cut
  exact (CanonicalGlobalSelfCut.original_prism_eq m (by omega) _ q _ _ _ _ _).trans
    (congrArg (CanonicalGlobalSelfCut.map m m q)
      (NativeGHPowerTimeCupAssociativity.power_class m hm F 0))

def before (r : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1 + 1)) :=
  SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVGeometricTest.test m hm F (r + 1))

def after (r : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1 + 1)) :=
  (NativeBVCutOutputCorrection.cut m hm F 0).component (NativeGHPowers.degree m (r + 1)) ≫
    SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVGeometricTest.test m hm F r)

def defect (r : ℕ) : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1 + 1)) :=
  before m hm F r - after m hm F r

theorem before_closed (r : ℕ) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1 + 1)) (before m hm F r) = 0 :=
  SelfSweepCochain.closed _ _ _ (NativeBVGeometricTest.test_closed m hm F (r + 1))

theorem after_closed (r : ℕ) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1 + 1)) (after m hm F r) = 0 :=
  DegreeLoweringCochainPullback.closed _ _ _
    (SelfSweepCochain.closed _ _ _ (NativeBVGeometricTest.test_closed m hm F r))

theorem defect_closed (r : ℕ) :
    cochainCoboundary (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1 + 1)) (defect m hm F r) = 0 := by
  change (chains (Loops (m + 1))).d _ _ ≫ (before m hm F r - after m hm F r) = 0
  rw [Preadditive.comp_sub]
  exact (congrArg₂ (fun a b => a - b) (before_closed m hm F r) (after_closed m hm F r)).trans (sub_self 0)

theorem test_constants_zero (r : ℕ) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
      (NativeGHPowers.degree m (r + 1) + 1) (NativeBVGeometricTest.test m hm F r) = 0 := by
  have hz : cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
      ((m + NativeGHPowers.degree m r) + (m + 1)) (NativeBVGeometricTest.raw m hm F r) = 0 :=
    GlobalTimeCupConstantsVanish.cochain_zero _ _ _ _ _ _ _ _
  unfold NativeBVGeometricTest.test
  rw [pullback_pre, hz]
  exact comp_zero

theorem before_constants_zero (r : ℕ) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
      (NativeGHPowers.degree m (r + 1 + 1)) (before m hm F r) = 0 :=
  NativeBVRelativeCochain.rotation_constants_zero _ _ _ (test_constants_zero m hm F (r + 1))

theorem after_constants_zero (r : ℕ) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
      (NativeGHPowers.degree m (r + 1 + 1)) (after m hm F r) = 0 := by
  have he : after m hm F r =
      GeometricTimeCupCochain.cochain m (NativeGHPowers.degree m 0)
        (NativeInnerCutPullback.rhoPos m hm F) (NativeInnerCutPullback.rhoLt m hm F)
        (NativeInnerCutPullback.radiusLe m hm F) (NativeClosingArcPowerVanishing.powerCocycle m hm F 0)
        (NativeGHPowers.degree m (r + 1))
        (SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVGeometricTest.test m hm F r)) :=
    GeometricTimeCupCochain.operation_dual _ _ _ _ _ _ _ _ _
  rw [he]
  exact GlobalTimeCupConstantsVanish.cochain_zero _ _ _ _ _ _ _ _

theorem defect_constants_zero (r : ℕ) :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1))
      (NativeGHPowers.degree m (r + 1 + 1)) (defect m hm F r) = 0 := by
  change (SupportedCapNaturality.push (GlobalTimeCupConstantsVanish.inclusion (m + 1))).f _ ≫
    (before m hm F r - after m hm F r) = 0
  rw [Preadditive.comp_sub]
  exact (congrArg₂ (fun a b => a - b) (before_constants_zero m hm F r)
    (after_constants_zero m hm F r)).trans (sub_self 0)

variable (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ)

theorem cut_candidate_cycle
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1 + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ _).hom c = NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) :
    ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom
      (((NativeBVCutOutputCorrection.cut m hm F 0).cycles (NativeGHPowers.degree m (r + 1))).hom c) =
      NativeRaisedBVCandidates.full m hm F P v₀ r := by
  have h := ConcreteCategory.congr_hom
    ((NativeBVCutOutputCorrection.cut m hm F 0).homologyπ_homology (NativeGHPowers.degree m (r + 1))) c
  change ((NativeBVCutOutputCorrection.cut m hm F 0).homology (NativeGHPowers.degree m (r + 1))).hom
      (((chains (Loops (m + 1))).homologyπ _).hom c) =
    ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom
      (((NativeBVCutOutputCorrection.cut m hm F 0).cycles (NativeGHPowers.degree m (r + 1))).hom c) at h
  have he := congrArg ((NativeBVCutOutputCorrection.cut m hm F 0).homology
    (NativeGHPowers.degree m (r + 1))).hom hc
  have hmorphism := ConcreteCategory.congr_hom (cut_homology m hm F (NativeGHPowers.degree m (r + 1)))
    (NativeRaisedBVCandidates.full m hm F P v₀ (r + 1))
  exact h.symm.trans (he.trans (hmorphism.trans (NativeRaisedBVCandidates.full_succ_cut m hm F P v₀ r)))

theorem before_value
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1 + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ _).hom c = NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) :
    ((chains (Loops (m + 1))).iCycles _ ≫ before m hm F r).hom c =
      NativeBVOriginalScalar.coefficient m hm P v₀ (r + 1) :=
  (NativeBVGeometricTest.coefficient_on_cycle m hm F P v₀ (r + 1) c hc).symm

theorem after_value
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1 + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ _).hom c = NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) :
    ((chains (Loops (m + 1))).iCycles _ ≫ after m hm F r).hom c =
      NativeBVOriginalScalar.coefficient m hm P v₀ r := by
  have he : (chains (Loops (m + 1))).iCycles _ ≫ after m hm F r =
      (NativeBVCutOutputCorrection.cut m hm F 0).cycles (NativeGHPowers.degree m (r + 1)) ≫
        (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
          SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVGeometricTest.test m hm F r) := by
    have hi : (NativeBVCutOutputCorrection.cut m hm F 0).cycles (NativeGHPowers.degree m (r + 1)) ≫
        (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) =
      (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1 + 1)) ≫
        (NativeBVCutOutputCorrection.cut m hm F 0).component (NativeGHPowers.degree m (r + 1)) :=
      (NativeBVCutOutputCorrection.cut m hm F 0).cycles_i _
    simpa only [after, Category.assoc] using congrArg
      (fun k => k ≫ SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _
        (NativeBVGeometricTest.test m hm F r)) hi.symm
  rw [he]
  exact (NativeBVGeometricTest.coefficient_on_cycle m hm F P v₀ r
    (((NativeBVCutOutputCorrection.cut m hm F 0).cycles (NativeGHPowers.degree m (r + 1))).hom c)
    (cut_candidate_cycle m hm F P v₀ r c hc)).symm

theorem defect_value
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1 + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ _).hom c = NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) :
    ((chains (Loops (m + 1))).iCycles _ ≫ defect m hm F r).hom c =
      NativeBVOriginalScalar.coefficient m hm P v₀ (r + 1) - NativeBVOriginalScalar.coefficient m hm P v₀ r := by
  unfold defect
  rw [Preadditive.comp_sub, ModuleCat.hom_sub, LinearMap.sub_apply,
    before_value m hm F P v₀ r c hc, after_value m hm F P v₀ r c hc]

theorem original_defect_value
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1 + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ _).hom c = NativeRaisedBVCandidates.full m hm F P v₀ (r + 1)) :
    ((chains (Loops (m + 1))).iCycles _ ≫ defect m hm F r).hom c =
      NativeBVOriginalScalar.thetaPairing m r
        (NativeBVScalarRecurrence.defect m r (NativeRaisedBVCandidates.full m hm F P v₀ (r + 1))) := by
  rw [defect_value m hm F P v₀ r c hc, NativeBVScalarRecurrence.candidate_defect_scalar]

end
end Finsler.NativeBVDefectCochain
