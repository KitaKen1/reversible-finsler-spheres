module

public import Finsler.Loop.NativeLoopCupSquare

/-! The SAME ordinary GH_0 cup GH_r vanishes by induction, without a
new divided-power model. Stage140 says GH_(r+1) equals GH_0 cup A_r
modulo the original Thom/time of GH_0 cup GH_r. The induction hypothesis
kills that remainder and the proved GH_0 square kills the next product. -/
@[expose] public section
namespace Finsler.NativeOrdinaryGHCupVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.Geometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.SmallChainCarrier Finsler.SupportedCapNaturality Finsler.NativeInnerCutPullback
open Finsler.SupportedSelfCut Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

private theorem cast_zero (X : TopCat.{0}) {i j : ℕ} (h : i = j) :
    CupUnit.absoluteCast X h 0 = 0 := by
  subst j
  rfl

private theorem class_cycles (X : TopCat.{0}) (n : ℕ) (T : singularCochainGroup (ZMod 2) X n)
    (hT : cochainCoboundary (ZMod 2) X n T = 0) (hz : cocycleClass X n T hT = 0) :
    (chains X).iCycles n ≫ T = 0 := by
  apply ConcreteCategory.hom_ext
  intro c
  have he := congrArg (fun a => (kroneckerMap X n).hom a (((chains X).homologyπ n).hom c)) hz
  rw [kroneckerMap_cocycleClass, map_zero, LinearMap.zero_apply] at he
  exact (kroneckerFunctional_apply X n T hT c).symm.trans he

private theorem cycles_class (X : TopCat.{0}) (n : ℕ) (T U : singularCochainGroup (ZMod 2) X n)
    (hT : cochainCoboundary (ZMod 2) X n T = 0) (hU : cochainCoboundary (ZMod 2) X n U = 0)
    (h : (chains X).iCycles n ≫ T = (chains X).iCycles n ≫ U) :
    cocycleClass X n T hT = cocycleClass X n U hU := by
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := ((ModuleCat.epi_iff_surjective ((chains X).homologyπ n)).mp inferInstance) z
  rw [kroneckerMap_cocycleClass, kroneckerMap_cocycleClass]
  exact (kroneckerFunctional_apply X n T hT c).trans
    ((ConcreteCategory.congr_hom h c).trans (kroneckerFunctional_apply X n U hU c).symm)

private theorem lowering_zero {X Y : TopCat.{0}} {d : ℕ}
    (f : DegreeLoweringHomology.Map (chains X) (chains Y) d) (q : ℕ)
    (B : singularCochainGroup (ZMod 2) Y q) (hB : cochainCoboundary (ZMod 2) Y q B = 0)
    (hz : cocycleClass Y q B hB = 0) :
    cocycleClass X (d + q) (f.component q ≫ B) (DegreeLoweringCochainPullback.closed f q B hB) = 0 := by
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  have h := DegreeLoweringCochainPullback.pairing f q B hB z
  rw [hz, map_zero, LinearMap.zero_apply] at h
  exact h.trans (by simp)

private theorem transport_zero (X : TopCat.{0}) {i j : ℕ} (h : i = j)
    (T : singularCochainGroup (ZMod 2) X j) (hT : cochainCoboundary (ZMod 2) X j T = 0)
    (hz : cocycleClass X j T hT = 0) :
    cocycleClass X i (CochainDegreeTransport.pre X h T) (CochainDegreeTransport.closed X h T hT) = 0 := by
  subst j
  exact hz

private theorem cup_class (X : TopCat.{0}) (p q N : ℕ) (hN : p + q = N)
    (A : singularCochainGroup (ZMod 2) X p) (B : singularCochainGroup (ZMod 2) X q)
    (hA : cochainCoboundary (ZMod 2) X p A = 0) (hB : cochainCoboundary (ZMod 2) X q B = 0) :
    cocycleClass X N (CupOne.cup X p q N hN A B) (CupCapOrder.closed _ _ _ _ _ _ _ hA hB) =
      CupAtDegree.cup X p q N hN (cocycleClass X p A hA) (cocycleClass X q B hB) := by
  subst N
  simpa only [CupOne.cup_comparison, CupAtDegree.cup, CupAtDegree.cast_self] using (cupZMod2_mk A hA B hB).symm

variable (m : ℕ) (hm : 2 ≤ m) (F : ReversibleMetric (m + 1)) (r : ℕ)

def ordinary : cohomologyZMod2 (Loops (m + 1)) (m + NativeGHPowers.degree m r) :=
  cupZMod2 (MeridianLoopClass.H1TransgressionClass m) (NativeGHPowers.power m r)

theorem nearRemainder_class : cocycleClass _ _ (NativeNearCutPowerSubstitution.nearRemainder m hm F r)
    (NativeNearCutPowerSubstitution.nearRemainder_closed m hm F r) =
    (cohPullback (TopCat.ofHom (retained (m + 1) (radiusLe m hm F))) (m + NativeGHPowers.degree m r)).hom
      (ordinary m r) := by
  have h := (cohPullback_cocycleClass (TopCat.ofHom (retained (m + 1) (radiusLe m hm F)))
    (m + NativeGHPowers.degree m r)
    (cochainCup m (NativeGHPowers.degree m r) (NativeNearCutPrimitiveGH.original m hm F)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F r))
    (cochainCupZMod2_respects_cocycles _ _ _ _ (NativeNearCutPrimitiveGH.original_closed m hm F)
      (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r))).symm
  have ha : cocycleClass (Loops (m + 1)) m (NativeNearCutPrimitiveGH.original m hm F)
      (NativeNearCutPrimitiveGH.original_closed m hm F) = MeridianLoopClass.H1TransgressionClass m :=
    NativeNearCutPrimitiveGH.original_class m hm F
  have hb : cocycleClass (Loops (m + 1)) (NativeGHPowers.degree m r)
      (NativeClosingArcPowerVanishing.powerCocycle m hm F r)
      (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r) = NativeGHPowers.power m r :=
    NativeClosingArcPowerVanishing.powerCocycle_class m hm F r
  rw [← cupZMod2_mk (NativeNearCutPrimitiveGH.original m hm F) (NativeNearCutPrimitiveGH.original_closed m hm F)
    (NativeClosingArcPowerVanishing.powerCocycle m hm F r) (NativeClosingArcPowerVanishing.powerCocycle_closed m hm F r), ha, hb] at h
  exact h

theorem remainder_class_zero_of (h : ordinary m r = 0) :
    cocycleClass _ _ (NativeNearCutPowerSubstitution.remainder m hm F r)
      (NativeNearCutPowerSubstitution.remainder_closed m hm F r) = 0 := by
  have hn : cocycleClass _ _ (NativeNearCutPowerSubstitution.nearRemainder m hm F r)
      (NativeNearCutPowerSubstitution.nearRemainder_closed m hm F r) = 0 := by
    rw [nearRemainder_class, h, map_zero]
  exact transport_zero _ (NativeNearCutPowerSubstitution.degree_match m r) _ _
    (lowering_zero (GlobalThomTime.operation m (rhoPos m hm F) (rhoLt m hm F)) _ _ _ hn)

theorem source_class_of (h : ordinary m r = 0) :
    cocycleClass _ _ (NativeSourceGHProjection.ordinaryCup m hm F r)
      (NativeSourceGHProjection.ordinaryCup_closed m hm F r) = NativeGHPowers.power m (r + 1) := by
  have hz := class_cycles _ _ _ (NativeNearCutPowerSubstitution.remainder_closed m hm F r)
    (remainder_class_zero_of m hm F r h)
  have he := NativeNearCutPowerSubstitution.cycle_values m hm F r
  rw [← NativeSourceGHProjection.projection_cycle_values, hz, add_zero] at he
  exact (cycles_class _ _ _ _ (NativeSourceGHProjection.ordinaryCup_closed m hm F r)
    (NativeBVTestedTransgression.after_closed m hm F r) he).trans (NativeBVTestedTransgression.after_class m hm F r)

theorem source_cup_class : cocycleClass _ _ (NativeSourceGHProjection.ordinaryCup m hm F r)
    (NativeSourceGHProjection.ordinaryCup_closed m hm F r) =
    CupAtDegree.cup (Loops (m + 1)) m (m + NativeGHPowers.degree m r) (NativeGHPowers.degree m (r + 1))
      (NativeNearCutPowerSubstitution.degree_match m r).symm (MeridianLoopClass.H1TransgressionClass m)
      (cocycleClass _ _ (NativeSourceGHProjection.bareSource m hm F r) (NativeSourceGHProjection.bareSource_closed m hm F r)) := by
  have h := cup_class _ _ _ _ (NativeNearCutPowerSubstitution.degree_match m r).symm
    (NativeNearCutPrimitiveGH.original m hm F) (NativeSourceGHProjection.bareSource m hm F r)
    (NativeNearCutPrimitiveGH.original_closed m hm F) (NativeSourceGHProjection.bareSource_closed m hm F r)
  rw [NativeNearCutPrimitiveGH.original_class] at h
  exact h

variable (P : Sphere (m + 1)) (v₀ : equator P)

include hm F P v₀ in
theorem successor_zero (h : ordinary m r = 0) : ordinary m (r + 1) = 0 := by
  have he := (source_class_of m hm F r h).symm.trans (source_cup_class m hm F r)
  unfold ordinary
  rw [he]
  change CupAtDegree.cup _ m (NativeGHPowers.degree m (r + 1)) (m + NativeGHPowers.degree m (r + 1)) rfl _ _ = 0
  rw [← CupAtDegree.assoc (Loops (m + 1)) m m (m + NativeGHPowers.degree m r) (m + m)
    (NativeGHPowers.degree m (r + 1)) (m + NativeGHPowers.degree m (r + 1)) rfl
    (NativeNearCutPowerSubstitution.degree_match m r).symm
    (by rw [NativeNearCutPowerSubstitution.degree_match]; omega) rfl]
  have hs : CupAtDegree.cup (Loops (m + 1)) m m (m + m) rfl
      (MeridianLoopClass.H1TransgressionClass m) (MeridianLoopClass.H1TransgressionClass m) = 0 :=
    NativeLoopCupSquare.primitive_square_zero m hm P v₀
  rw [hs]
  unfold CupAtDegree.cup
  rw [Cup.zero_cup]
  exact cast_zero _ _

include hm F P v₀ in
theorem ordinary_zero : ordinary m r = 0 := by
  induction r with
  | zero => exact NativeLoopCupSquare.primitive_square_zero m hm P v₀
  | succ r ih => exact successor_zero m hm F r P v₀ ih

include P v₀ in
theorem remainder_class_zero : cocycleClass _ _ (NativeNearCutPowerSubstitution.remainder m hm F r)
    (NativeNearCutPowerSubstitution.remainder_closed m hm F r) = 0 :=
  remainder_class_zero_of m hm F r (ordinary_zero m hm F r P v₀)

include P v₀ in
theorem remainder_cycles_zero : (chains (Loops (m + 1))).iCycles (NativeGHPowers.degree m (r + 1)) ≫
    NativeNearCutPowerSubstitution.remainder m hm F r = 0 :=
  class_cycles _ _ _ (NativeNearCutPowerSubstitution.remainder_closed m hm F r) (remainder_class_zero m hm F r P v₀)

include P v₀ in
theorem source_class : cocycleClass _ _ (NativeSourceGHProjection.ordinaryCup m hm F r)
    (NativeSourceGHProjection.ordinaryCup_closed m hm F r) = NativeGHPowers.power m (r + 1) :=
  source_class_of m hm F r (ordinary_zero m hm F r P v₀)

end
end Finsler.NativeOrdinaryGHCupVanishing
