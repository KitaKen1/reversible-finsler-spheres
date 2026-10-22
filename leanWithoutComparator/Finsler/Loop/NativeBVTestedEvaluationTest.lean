module

public import Finsler.Loop.NativeBVForwardSquare
public import Finsler.Loop.NativeBVReflectedSquareTest

/-! The SAME original BV coefficients are now computed by the original
forward cut/time and source rotation, with evaluation in the TESTED
slot and the SAME supported GH power in the retained slot. No remaining
complement or time reflection occurs in this test. -/
@[expose] public section
namespace Finsler.NativeBVTestedEvaluationTest
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily
open Finsler.NativeInnerCutPullback Finsler.SelfCutThomCocycle Finsler.SupportedSelfCut
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

private theorem pullback_pre {X Y : TopCat.{0}} (f : X ⟶ Y) {i j : ℕ} (h : i = j)
    (T : singularCochainGroup (ZMod 2) Y j) :
    cochainPullback f i (CochainDegreeTransport.pre Y h T) =
      CochainDegreeTransport.pre X h (cochainPullback f j T) := by
  subst j
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]

private theorem double_prism_at (n q k : ℕ) (h : q + 1 = k)
    (T : singularCochainGroup (ZMod 2) (parameters n) (k + 1)) :
    (H1LoopRotation.chainHomotopy n).hom q (q + 1) ≫
      CochainDegreeTransport.pre _ h (SelfCutTimePrism.prism n k ≫ T) =
    NativeGlobalTimeSquare.squarePrism (Loops n) q ≫
      cochainPullback (NativeBVRotationSquare.intoCut n) (q + 2)
        (CochainDegreeTransport.pre _ (congrArg (fun a => a + 1) h) T) := by
  subst k
  simp only [CochainDegreeTransport.pre, eqToHom_refl, Category.id_comp]
  change _ ≫ (_ ≫ T) = _ ≫ ((push (NativeBVRotationSquare.intoCut n)).f (q + 2) ≫ T)
  rw [← Category.assoc, NativeBVRotationSquare.double_prism, Category.assoc]

private theorem source_component (m : ℕ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ < r) (q : ℕ)
    (K : singularCochainGroup (ZMod 2) (TopCat.of (neighborhood (m + 1) r)) q) :
    (GlobalThomTime.operation m hρ hρr).component q ≫ K =
      SelfCutTimePrism.prism (m + 1) (m + q) ≫ (GlobalThomTime.aligned m hρ hρr q ≫ K) := by
  change (SelfCutTimePrism.prism (m + 1) (m + q) ≫ GlobalThomTime.aligned m hρ hρr q) ≫ K = _
  exact Category.assoc _ _ _

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def source : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1) + 1) :=
  CochainDegreeTransport.pre _ (by have := NativeBVReorderedTest.degree_match m r; omega)
    ((GlobalThomTime.operation m (rhoPos m hm F) (rhoLt m hm F)).component
      (NativeGHPowers.degree m r + m + 1) ≫ NativeBVComplementCapTest.near m hm F r)

theorem source_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1) + 1)
    (source m hm F r) = 0 := by
  apply CochainDegreeTransport.closed
  have he := NativeBVThomBoundary.source_boundary m (rhoPos m hm F) (rhoLt m hm F)
    (NativeGHPowers.degree m r + m + 1) (NativeBVComplementCapTest.near m hm F r)
  rw [NativeBVComplementCapTest.near_closed] at he
  exact he.trans comp_zero

theorem source_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1) + 1)
      (source m hm F r) = 0 := by
  unfold source
  rw [pullback_pre]
  have hz := NativeBVThomBoundary.source_constants_zero m (rhoPos m hm F) (rhoLt m hm F)
    (NativeGHPowers.degree m r + m + 1) (NativeBVComplementCapTest.near m hm F r)
  change cochainPullback _ _ (_ ≫ _) = 0 at hz
  rw [hz]
  exact comp_zero

def test : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (source m hm F r)

theorem test_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1)) (test m hm F r) = 0 :=
  SelfSweepCochain.closed _ _ _ (source_closed m hm F r)

theorem test_constants_zero :
    cochainPullback (GlobalTimeCupConstantsVanish.inclusion (m + 1)) (NativeGHPowers.degree m (r + 1))
      (test m hm F r) = 0 := NativeBVRelativeCochain.rotation_constants_zero _ _ _ (source_constants_zero m hm F r)

theorem forward_square : test m hm F r =
    NativeGlobalTimeSquare.squarePrism (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) ≫
      cochainPullback (NativeBVRotationSquare.intoCut (m + 1)) (NativeGHPowers.degree m (r + 1) + 2)
        (NativeBVReflectedSquareTest.parameter m hm F r) := by
  unfold test source SelfSweepCochain.cochain SelfHomotopySweep.component NativeBVReflectedSquareTest.parameter
  rw [source_component]
  exact double_prism_at (m + 1) (NativeGHPowers.degree m (r + 1)) (m + (NativeGHPowers.degree m r + m + 1))
    (by have := NativeBVReorderedTest.degree_match m r; omega)
    (GlobalThomTime.aligned m (rhoPos m hm F) (rhoLt m hm F) (NativeGHPowers.degree m r + m + 1) ≫
      NativeBVComplementCapTest.near m hm F r)

theorem reflected_cycle_values :
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeBVReflectedSquareTest.test m hm F r =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ test m hm F r := by
  rw [forward_square]
  apply NativeBVForwardSquare.reflected_square_values
  · exact NativeBVReflectedSquareTest.parameter_closed m hm F r
  · exact CochainCarrierPullbackZero.family_zero (FilteredGlobalThomTime.endpointCarrier (m + 1)) _ _
      (NativeBVReflectedSquareTest.parameter_diagonal_zero m hm F r) _ (fun _ => rfl)

theorem original_cycle_values :
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
      SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) _ (NativeBVComplementCapTest.test m hm F r) =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ test m hm F r :=
  (NativeBVReflectedSquareTest.cycle_values m hm F r).symm.trans (reflected_cycle_values m hm F r)

theorem coefficient_on_cycle (P : Sphere (m + 1)) (v₀ : equator P)
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) :
    NativeBVOriginalScalar.coefficient m hm P v₀ r =
      ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ test m hm F r).hom c := by
  rw [← reflected_cycle_values]
  exact NativeBVReflectedSquareTest.coefficient_on_cycle m hm F r P v₀ c hc

end
end Finsler.NativeBVTestedEvaluationTest
