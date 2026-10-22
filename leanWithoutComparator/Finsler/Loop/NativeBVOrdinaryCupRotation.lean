module

public import Finsler.Loop.NativeBVSourceCupProjection
public import Finsler.Loop.PrismCupLeibniz
public import Finsler.Loop.NativeLoopResidueVanishing

/-! Apply the PROVED ordinary-cup prism rule to the SAME original BV
source test. For n>=4 the bare Thom/time factor's rotation lies in the
actual missing residue, so the SECOND cup term is exact. Consequently
c_r = 1 + the SAME retained ordinary-cup remainder on SAME raised inputs.
Remainder zero and the exceptional n=3 case are not assumed. -/
@[expose] public section
namespace Finsler.NativeBVOrdinaryCupRotation
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.Geometry Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.NativeInnerCutPullback
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

private theorem pullback_id (X : TopCat.{0}) (n : ℕ) (T : singularCochainGroup (ZMod 2) X n) :
    cochainPullback (𝟙 X) n T = T := by
  exact congrArg (fun f => (f.f n).hom T) (singularCochainComplexZMod2.map_id (Opposite.op X))

private theorem cup_class_congr (X : TopCat.{0}) (a b N : ℕ) (hN : a + b = N)
    (A A' : singularCochainGroup (ZMod 2) X a) (B : singularCochainGroup (ZMod 2) X b)
    (hA : cochainCoboundary (ZMod 2) X a A = 0) (hA' : cochainCoboundary (ZMod 2) X a A' = 0)
    (hB : cochainCoboundary (ZMod 2) X b B = 0) (h : cocycleClass X a A hA = cocycleClass X a A' hA') :
    cocycleClass X N (CupOne.cup X a b N hN A B) (CupCapOrder.closed _ _ _ _ _ _ _ hA hB) =
      cocycleClass X N (CupOne.cup X a b N hN A' B) (CupCapOrder.closed _ _ _ _ _ _ _ hA' hB) := by
  subst N
  have he := congrArg (fun x => cupZMod2 x (cocycleClass X b B hB)) h
  rw [cupZMod2_mk, cupZMod2_mk] at he
  simpa only [CupOne.cup_comparison] using he

private theorem cup_class_zero_right (X : TopCat.{0}) (a b N : ℕ) (hN : a + b = N)
    (A : singularCochainGroup (ZMod 2) X a) (B : singularCochainGroup (ZMod 2) X b)
    (hA : cochainCoboundary (ZMod 2) X a A = 0) (hB : cochainCoboundary (ZMod 2) X b B = 0)
    (h : cocycleClass X b B hB = 0) :
    cocycleClass X N (CupOne.cup X a b N hN A B) (CupCapOrder.closed _ _ _ _ _ _ _ hA hB) = 0 := by
  subst N
  have he := (cupZMod2_mk A hA B hB).symm
  rw [h, Cup.cup_zero] at he
  simpa only [CupOne.cup_comparison] using he

private theorem cycle_class_eq (X : TopCat.{0}) (n : ℕ) (T U : singularCochainGroup (ZMod 2) X n)
    (hT : cochainCoboundary (ZMod 2) X n T = 0) (hU : cochainCoboundary (ZMod 2) X n U = 0)
    (h : cocycleClass X n T hT = cocycleClass X n U hU) :
    (chains X).iCycles n ≫ T = (chains X).iCycles n ≫ U := by
  apply ConcreteCategory.hom_ext
  intro c
  have he := congrArg (fun a => (kroneckerMap X n).hom a (((chains X).homologyπ n).hom c)) h
  rw [kroneckerMap_cocycleClass, kroneckerMap_cocycleClass] at he
  exact (kroneckerFunctional_apply X n T hT c).symm.trans
    (he.trans (kroneckerFunctional_apply X n U hU c))

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def evaluationRotation : singularCochainGroup (ZMod 2) (Loops (m + 1)) m :=
  SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) m (NativeBVNormalizedSource.evaluation m)

theorem evaluationRotation_closed : cochainCoboundary (ZMod 2) _ m (evaluationRotation m) = 0 :=
  SelfSweepCochain.closed _ _ _ (NativeBVNormalizedSource.evaluation_closed m)

theorem evaluationRotation_class : cocycleClass _ m (evaluationRotation m) (evaluationRotation_closed m) =
    cocycleClass _ m (NativeNearCutPrimitiveGH.original m hm F) (NativeNearCutPrimitiveGH.original_closed m hm F) :=
  (NativeBVEvaluationTransgression.rotation_class m _ (NativeBVNormalizedSource.evaluation_closed m)
    (NativeBVNormalizedSource.evaluation_class m)).trans (NativeNearCutPrimitiveGH.original_class m hm F).symm

abbrev bareDegree := m + NativeGHPowers.degree m r

def bareRotation : singularCochainGroup (ZMod 2) (Loops (m + 1)) (bareDegree m r - 1) :=
  SelfSweepCochain.cochain (H1LoopRotation.chainHomotopy (m + 1)) (bareDegree m r - 1)
    (CochainDegreeTransport.pre _ (show bareDegree m r - 1 + 1 = bareDegree m r by dsimp [bareDegree]; omega)
      (NativeSourceGHProjection.bareSource m hm F r))

theorem bareRotation_closed : cochainCoboundary (ZMod 2) _ (bareDegree m r - 1) (bareRotation m hm F r) = 0 :=
  SelfSweepCochain.closed _ _ _ (CochainDegreeTransport.closed _ _ _ (NativeSourceGHProjection.bareSource_closed m hm F r))

def firstTerm : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  CupOne.cup _ m (bareDegree m r) (NativeGHPowers.degree m (r + 1))
    (NativeNearCutPowerSubstitution.degree_match m r).symm (evaluationRotation m) (NativeSourceGHProjection.bareSource m hm F r)

def secondTerm : singularCochainGroup (ZMod 2) (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) :=
  CupOne.cup _ (m + 1) (bareDegree m r - 1) (NativeGHPowers.degree m (r + 1))
    (by rw [NativeNearCutPowerSubstitution.degree_match]; dsimp [bareDegree]; omega)
    (NativeBVNormalizedSource.evaluation m) (bareRotation m hm F r)

theorem firstTerm_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1)) (firstTerm m hm F r) = 0 :=
  CupCapOrder.closed _ _ _ _ _ _ _ (evaluationRotation_closed m) (NativeSourceGHProjection.bareSource_closed m hm F r)

theorem secondTerm_closed : cochainCoboundary (ZMod 2) _ (NativeGHPowers.degree m (r + 1)) (secondTerm m hm F r) = 0 :=
  CupCapOrder.closed _ _ _ _ _ _ _ (NativeBVNormalizedSource.evaluation_closed m) (bareRotation_closed m hm F r)

theorem formula : NativeBVSourceCupProjection.test m hm F r = firstTerm m hm F r + secondTerm m hm F r := by
  have h := PrismCupLeibniz.formula (H1LoopRotation.homotopy (m + 1)) m (bareDegree m r - 1)
    (NativeGHPowers.degree m (r + 1))
    (by rw [NativeNearCutPowerSubstitution.degree_match]; dsimp [bareDegree]; omega)
    (NativeBVNormalizedSource.evaluation m)
    (CochainDegreeTransport.pre _ (show bareDegree m r - 1 + 1 = bareDegree m r by dsimp [bareDegree]; omega)
      (NativeSourceGHProjection.bareSource m hm F r))
  rw [pullback_id, pullback_id, NativeInnerRetainedComparison.cup_right_pre,
    NativeInnerRetainedComparison.cup_right_pre] at h
  exact h

theorem firstTerm_class : cocycleClass _ _ (firstTerm m hm F r) (firstTerm_closed m hm F r) =
    cocycleClass _ _ (NativeSourceGHProjection.ordinaryCup m hm F r) (NativeSourceGHProjection.ordinaryCup_closed m hm F r) :=
  cup_class_congr _ _ _ _ _ _ _ _ (evaluationRotation_closed m) (NativeNearCutPrimitiveGH.original_closed m hm F)
    (NativeSourceGHProjection.bareSource_closed m hm F r) (evaluationRotation_class m hm F)

theorem firstTerm_cycle_values : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ firstTerm m hm F r =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeSourceGHProjection.ordinaryCup m hm F r :=
  cycle_class_eq _ _ _ _ (firstTerm_closed m hm F r) (NativeSourceGHProjection.ordinaryCup_closed m hm F r) (firstTerm_class m hm F r)

include hm in
theorem preceding_degree : bareDegree m r - 1 = (2 * r + 1) * m + (m - 1) := by
  dsimp [bareDegree]
  rw [NativeGHPowers.degree_formula]
  omega

variable (h3 : 3 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)

include h3 P v₀ in
theorem bareRotation_class_zero : cocycleClass _ _ (bareRotation m hm F r) (bareRotation_closed m hm F r) = 0 := by
  have hz : ∀ a : cohomologyZMod2 (Loops (m + 1)) (bareDegree m r - 1), a = 0 := by
    rw [preceding_degree m hm r]
    exact NativeLoopResidueVanishing.cohomology_eq_zero m (m - 1) (by omega) (by omega) P v₀ (2 * r + 1)
  exact hz _

include h3 P v₀ in
theorem secondTerm_class_zero : cocycleClass _ _ (secondTerm m hm F r) (secondTerm_closed m hm F r) = 0 :=
  cup_class_zero_right _ _ _ _ _ _ _ (NativeBVNormalizedSource.evaluation_closed m) (bareRotation_closed m hm F r)
    (bareRotation_class_zero m hm F r h3 P v₀)

include h3 P v₀ in
theorem secondTerm_cycles_zero : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ secondTerm m hm F r = 0 := by
  have h := cycle_class_eq (Loops (m + 1)) (NativeGHPowers.degree m (r + 1)) (secondTerm m hm F r) 0
    (secondTerm_closed m hm F r) (map_zero _)
    ((secondTerm_class_zero m hm F r h3 P v₀).trans (cocycleClass_zero _ _ _).symm)
  exact h.trans comp_zero

include h3 P v₀ in
theorem cycle_values : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeBVSourceCupProjection.test m hm F r =
    (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeSourceGHProjection.ordinaryCup m hm F r := by
  rw [formula, Preadditive.comp_add, firstTerm_cycle_values, secondTerm_cycles_zero m hm F r h3 P v₀, add_zero]

include h3 in
theorem coefficient_one_plus_remainder
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) : NativeBVOriginalScalar.coefficient m hm P v₀ r =
    1 + ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeNearCutPowerSubstitution.remainder m hm F r).hom c := by
  rw [NativeBVSourceCupProjection.coefficient_on_cycle m hm F r P v₀ c hc, cycle_values m hm F r h3 P v₀]
  exact NativeSourceGHProjection.value_one_plus_remainder m hm F r P v₀ c hc

include h3 in
theorem coefficient_one_iff_remainder_zero
    (c : (chains (Loops (m + 1))).cycles (NativeGHPowers.degree m (r + 1)))
    (hc : ((chains (Loops (m + 1))).homologyπ (NativeGHPowers.degree m (r + 1))).hom c =
      NativeRaisedBVCandidates.full m hm F P v₀ r) : NativeBVOriginalScalar.coefficient m hm P v₀ r = 1 ↔
    ((chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫ NativeNearCutPowerSubstitution.remainder m hm F r).hom c = 0 := by
  rw [coefficient_one_plus_remainder m hm F r h3 P v₀ c hc]
  exact add_eq_left

end
end Finsler.NativeBVOrdinaryCupRotation
