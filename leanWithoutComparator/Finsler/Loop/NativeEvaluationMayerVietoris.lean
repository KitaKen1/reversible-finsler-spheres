module

public import Finsler.Loop.H1PuncturedRelativeChart
public import Finsler.Loop.NativeUnitEvaluationKernelRoute
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic

/-! Use the ACTUAL two punctured evaluation opens and pinned TauCeti
Mayer-Vietoris maps on the original full loop space. The real evaluation
commutes with the real connecting map. Full evaluation injectivity reduces
to TWO explicit homological obligations in these same opens/overlap;
neither obligation is postulated or claimed proved here. -/
@[expose] public section
namespace Finsler.NativeEvaluationMayerVietoris
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.BorelLoop Finsler.CochainComparison
open Finsler.H1PuncturedRelativeChart Finsler.H1PuncturedEvaluationChart
open Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

abbrev overlap {n : ℕ} (y : Sphere n) : TopCat.{0} :=
  TopCat.of (fullDomain y ∩ fullDomain (antipode y) : Set (fullPair n).fst)
abbrev baseOverlap {n : ℕ} (y : Sphere n) : TopCat.{0} :=
  TopCat.of (base y ∩ base (antipode y) : Set (Sphere n))

def overlapEvaluation {n : ℕ} (y : Sphere n) : overlap y ⟶ baseOverlap y :=
  TopCat.ofHom ⟨fun u => ⟨BorelEvaluation.fullEval n u.val, u.property⟩,
    ((BorelEvaluation.fullEval n).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

abbrev patches {n : ℕ} (y : Sphere n) (k : ℕ) : ModuleCat.{0} (ZMod 2) :=
  homologyZMod2 (TopCat.of (fullDomain y)) k ⊞ homologyZMod2 (TopCat.of (fullDomain (antipode y))) k

def fromPatches {n : ℕ} (y : Sphere n) (k : ℕ) : patches y k ⟶ homologyZMod2 (fullPair n).fst k :=
  SSet.mayerVietorisFromBiprod coeff
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (fullDomain y))))
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.subtypeVal (fullDomain (antipode y))))) k

def toPatches {n : ℕ} (y : Sphere n) (k : ℕ) : homologyZMod2 (overlap y) k ⟶ patches y k :=
  SSet.mayerVietorisToBiprod coeff
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := fullDomain (antipode y))))))
    (TopCat.toSSet.map (TopCat.ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := fullDomain y))))) k

def delta {n : ℕ} (y : Sphere n) (k : ℕ) :
    homologyZMod2 (fullPair n).fst (k + 1) ⟶ homologyZMod2 (overlap y) k :=
  TopCat.mayerVietorisδ (X := (fullPair n).fst) coeff
    (fullDomain_open y) (fullDomain_open (antipode y)) (fullDomain_cover y) (k + 1) k rfl

def baseDelta {n : ℕ} (y : Sphere n) (k : ℕ) :
    homologyZMod2 (BorelEvaluation.sphere n) (k + 1) ⟶ homologyZMod2 (baseOverlap y) k :=
  TopCat.mayerVietorisδ (X := BorelEvaluation.sphere n) coeff
    (base_open y) (base_open (antipode y)) (base_cover y) (k + 1) k rfl

theorem fromPatches_delta {n : ℕ} (y : Sphere n) (k : ℕ) :
    fromPatches y (k + 1) ≫ delta y k = 0 :=
  TopCat.mayerVietorisFromBiprod_δ (X := (fullPair n).fst) coeff (fullDomain_open y) (fullDomain_open (antipode y))
    (fullDomain_cover y) (k + 1) k rfl

theorem delta_toPatches {n : ℕ} (y : Sphere n) (k : ℕ) : delta y k ≫ toPatches y k = 0 :=
  TopCat.mayerVietorisδ_toBiprod (X := (fullPair n).fst) coeff (fullDomain_open y) (fullDomain_open (antipode y))
    (fullDomain_cover y) (k + 1) k rfl

theorem exact_full {n : ℕ} (y : Sphere n) (k : ℕ) :
    (ShortComplex.mk (fromPatches y (k + 1)) (delta y k) (fromPatches_delta y k)).Exact :=
  TopCat.mayerVietoris_exact₃ (X := (fullPair n).fst) coeff (fullDomain_open y) (fullDomain_open (antipode y))
    (fullDomain_cover y) (k + 1) k rfl

theorem exact_overlap {n : ℕ} (y : Sphere n) (k : ℕ) :
    (ShortComplex.mk (delta y k) (toPatches y k) (delta_toPatches y k)).Exact :=
  TopCat.mayerVietoris_exact₁ (X := (fullPair n).fst) coeff (fullDomain_open y) (fullDomain_open (antipode y))
    (fullDomain_cover y) (k + 1) k rfl

theorem evaluation_naturality {n : ℕ} (y : Sphere n) (k : ℕ) :
    delta y k ≫ homologyPushZMod2 (overlapEvaluation y) k =
      homologyPushZMod2 (BorelEvaluation.fullEval n) (k + 1) ≫ baseDelta y k :=
  TopCat.mayerVietorisδ_naturality (X := (fullPair n).fst) (Y := BorelEvaluation.sphere n) coeff
    (fullDomain_open y) (fullDomain_open (antipode y)) (fullDomain_cover y)
    (base_open y) (base_open (antipode y)) (base_cover y)
    (BorelEvaluation.fullEval n) (fun _ h => h) (fun _ h => h) (k + 1) k rfl

theorem delta_injective_of_fromPatches_zero {n : ℕ} (y : Sphere n) (k : ℕ)
    (hp : fromPatches y (k + 1) = 0) : Function.Injective (delta y k).hom := by
  intro a b he
  have hz : (delta y k).hom (a - b) = 0 := by rw [map_sub, he, sub_self]
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp (exact_full y k) (a - b) hz
  change (fromPatches y (k + 1)).hom c = a - b at hc
  rw [hp, ModuleCat.hom_zero, LinearMap.zero_apply] at hc
  exact sub_eq_zero.mp hc.symm

theorem evaluation_injective_of_actual_cover_obligations {n : ℕ} (y : Sphere n) (k : ℕ)
    (hp : fromPatches y (k + 1) = 0)
    (ho : ∀ z : homologyZMod2 (overlap y) k,
      (homologyPushZMod2 (overlapEvaluation y) k).hom z = 0 → (toPatches y k).hom z = 0 → z = 0) :
    Function.Injective (homologyPushZMod2 (BorelEvaluation.fullEval n) (k + 1)).hom := by
  intro a b he
  have he0 : (homologyPushZMod2 (BorelEvaluation.fullEval n) (k + 1)).hom (a - b) = 0 := by
    rw [map_sub, he, sub_self]
  have hz : (delta y k).hom (a - b) = 0 := by
    apply ho
    · have hn := ConcreteCategory.congr_hom (evaluation_naturality y k) (a - b)
      change (homologyPushZMod2 (overlapEvaluation y) k).hom ((delta y k).hom (a - b)) =
        (baseDelta y k).hom ((homologyPushZMod2 (BorelEvaluation.fullEval n) (k + 1)).hom (a - b)) at hn
      rw [he0, map_zero] at hn
      exact hn
    · exact (ConcreteCategory.congr_hom (delta_toPatches y k) (a - b)).trans rfl
  apply sub_eq_zero.mp
  apply delta_injective_of_fromPatches_zero y k hp
  simpa only [map_zero] using hz

theorem original_UNIT_of_actual_cover_obligations (m : ℕ) (hm : 1 ≤ m) (y : Sphere (m + 1))
    (v₀ : equator y) (hp : fromPatches y (m + 1) = 0)
    (ho : ∀ z : homologyZMod2 (overlap y) m,
      (homologyPushZMod2 (overlapEvaluation y) m).hom z = 0 → (toPatches y m).hom z = 0 → z = 0) :
    NativeConstantUnitDefect.cutFull m hm y v₀ = AbsoluteFilteredUnits.absoluteCandidate (m + 1) (by omega) :=
  NativeUnitEvaluationKernelRoute.unit_of_full_evaluation_injective m hm y v₀
    (evaluation_injective_of_actual_cover_obligations y m hp ho)

end
end Finsler.NativeEvaluationMayerVietoris
