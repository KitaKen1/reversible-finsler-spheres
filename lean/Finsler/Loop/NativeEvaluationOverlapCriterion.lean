module

public import Finsler.Loop.NativeEvaluationMayerVietoris
public import Finsler.Topology.SpherePuncturedEvaluation

/-! Make the actual overlap test sharp. Positive homology on the
two punctured BASE spheres vanishes by the pinned actual theorem,
so the base connecting map is injective. With patch-imageZERO, the
actual joint overlap test is EQUIVALENT to evaluation injectivity. -/
@[expose] public section
namespace Finsler.NativeEvaluationOverlapCriterion
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.H1PuncturedEvaluationChart Finsler.MeridianLoopFamily
open Finsler.NativeEvaluationMayerVietoris
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev basePatches {n : ℕ} (y : Sphere n) (k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  homologyZMod2 (TopCat.of (base y)) k ⊞ homologyZMod2 (TopCat.of (base (antipode y))) k

def baseFromPatches {n : ℕ} (y : Sphere n) (k : ℕ) :
    basePatches y k ⟶ homologyZMod2 (BorelEvaluation.sphere n) k :=
  SSet.mayerVietorisFromBiprod coeff
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (base y))))
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (base (antipode y))))) k

theorem baseFromPatches_zero {n : ℕ} (y : Sphere n) (k : ℕ) (hk : 1 ≤ k) :
    baseFromPatches y k = 0 := by
  have hu : IsZero (homologyZMod2 (TopCat.of (base y)) k) :=
    SpherePuncturedEvaluation.homology_isZero n (antipode y) k hk
  have hv : IsZero (homologyZMod2 (TopCat.of (base (antipode y))) k) :=
    SpherePuncturedEvaluation.homology_isZero n (antipode (antipode y)) k hk
  apply biprod.hom_ext'
  · exact hu.eq_of_src _ _
  · exact hv.eq_of_src _ _

theorem baseDelta_injective {n : ℕ} (y : Sphere n) (k : ℕ) : Function.Injective (baseDelta y k).hom := by
  have hs := TopCat.mayerVietoris_exact₃ (X := BorelEvaluation.sphere n) coeff
    (base_open y) (base_open (antipode y)) (base_cover y) (k + 1) k rfl
  intro a b he
  have hz : (baseDelta y k).hom (a - b) = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp hs (a - b) hz
  change (baseFromPatches y (k + 1)).hom c = a - b at hc
  rw [baseFromPatches_zero y (k + 1) (by omega), ModuleCat.hom_zero, LinearMap.zero_apply] at hc
  exact sub_eq_zero.mp hc.symm

theorem joint_overlap_of_evaluation_injective {n : ℕ} (y : Sphere n) (k : ℕ)
    (hi : Function.Injective (homologyPushZMod2 (BorelEvaluation.fullEval n) (k + 1)).hom)
    (z : homologyZMod2 (overlap y) k)
    (he : (homologyPushZMod2 (overlapEvaluation y) k).hom z = 0)
    (hp : (toPatches y k).hom z = 0) : z = 0 := by
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp (exact_overlap y k) z hp
  change (delta y k).hom a = z at ha
  have hn := ConcreteCategory.congr_hom (evaluation_naturality y k) a
  change (homologyPushZMod2 (overlapEvaluation y) k).hom ((delta y k).hom a) =
    (baseDelta y k).hom ((homologyPushZMod2 (BorelEvaluation.fullEval n) (k + 1)).hom a) at hn
  rw [ha, he] at hn
  have hva : (homologyPushZMod2 (BorelEvaluation.fullEval n) (k + 1)).hom a = 0 := by
    apply baseDelta_injective y k
    exact hn.symm.trans (map_zero _).symm
  have haz : a = 0 := hi (hva.trans (map_zero _).symm)
  rw [haz, map_zero] at ha
  exact ha.symm

theorem evaluation_injective_iff_joint_overlap {n : ℕ} (y : Sphere n) (k : ℕ)
    (hp : fromPatches y (k + 1) = 0) :
    Function.Injective (homologyPushZMod2 (BorelEvaluation.fullEval n) (k + 1)).hom ↔
      ∀ z : homologyZMod2 (overlap y) k,
        (homologyPushZMod2 (overlapEvaluation y) k).hom z = 0 → (toPatches y k).hom z = 0 → z = 0 :=
  ⟨fun hi z he hz => joint_overlap_of_evaluation_injective y k hi z he hz,
    evaluation_injective_of_actual_cover_obligations y k hp⟩

end
end Finsler.NativeEvaluationOverlapCriterion
