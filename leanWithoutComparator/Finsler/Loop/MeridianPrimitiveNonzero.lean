module

public import Finsler.Loop.MeridianSweepConnecting

/-! The actual primitive meridian sweep coefficient is ONE over F2.
This gives nonzero actual ordinary/H1 loop classes and absolute/relative
transgression classes. The degree is m=n-1; no manuscript power S or
required UNIT pairing is identified here. -/
@[expose] public section
namespace Finsler.MeridianPrimitiveNonzero
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.SmallChainCarrier
open Finsler.SupportedCapNaturality Finsler.MeridianLoopFamily Finsler.MeridianLoopClass
open Finsler.MeridianIntersectionMaps Finsler.MeridianSweepConnecting
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem sweep_connecting_fundamental (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (connecting P m).hom (sweepClass m hm P v₀) =
      -(HomologicalComplex.homologyMap (push (varying P)) m).hom
        (MeridianEquatorHomology.fundamental m hm P) := by
  have h := ConcreteCategory.congr_hom (sweep_connecting P v₀ m)
    (MeridianEquatorHomology.fundamental m hm P)
  change (connecting P m).hom (sweepClass m hm P v₀) =
    (HomologicalComplex.homologyMap (push (fixed P v₀)) m).hom _ -
      (HomologicalComplex.homologyMap (push (varying P)) m).hom _ at h
  rw [fixed_homology_zero P v₀ m (by omega)] at h
  simpa only [ModuleCat.hom_zero, LinearMap.zero_apply, zero_sub] using h

theorem sweep_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    sweepClass m hm P v₀ ≠ 0 := by
  intro hz
  have h := sweep_connecting_fundamental m hm P v₀
  rw [hz, map_zero] at h
  have hv : (HomologicalComplex.homologyMap (push (varying P)) m).hom
      (MeridianEquatorHomology.fundamental m hm P) = 0 := neg_eq_zero.mp h.symm
  apply MeridianEquatorHomology.fundamental_ne_zero m hm P
  apply varying_homology_injective P m
  simpa only [map_zero] using hv

theorem sweep_coefficient_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    sweepCoefficient m hm P v₀ = 1 := by
  have hn : sweepCoefficient m hm P v₀ ≠ 0 := by
    intro hz
    apply sweep_ne_zero m hm P v₀
    apply (SphereTopClass.homologyEquiv (m + 1) (by omega)).injective
    change SphereTopClass.homologyEquiv (m + 1) (by omega) (sweepClass m hm P v₀) = 0 at hz
    simpa only [map_zero] using hz
  exact Fin.eq_one_of_ne_zero _ hn

theorem ordinary_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    ordinaryClass m hm P v₀ ≠ 0 := by
  intro hz
  apply sweep_ne_zero m hm P v₀
  change (ContinuousLoopSweep.homology (m + 1) m).hom (ordinaryClass m hm P v₀) = 0
  rw [hz, map_zero]

theorem H1_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    H1Class m hm P v₀ ≠ 0 := by
  intro hz
  apply ordinary_ne_zero m hm P v₀
  rw [← inclusion_H1Class, hz, map_zero]

theorem ordinary_pairing_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (ContinuousLoopModel.space (m + 1)) m).hom (ordinaryTransgression m)
      (ordinaryClass m hm P v₀) = 1 := by
  rw [ordinary_pairing, sphere_top_evaluation]
  exact sweep_coefficient_one m hm P v₀

theorem H1_pairing_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    (kroneckerMap (BorelLoop.Loops (m + 1)) m).hom (H1TransgressionClass m) (H1Class m hm P v₀) = 1 := by
  rw [pairing_coefficient, sweep_coefficient_one]

theorem relative_pairing_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    RelativeKronecker.comparison (BorelLoop.fullPair (m + 1)) m (relativeTransgressionClass m)
      (ConstantRelativePairing.homologyToRelative (m + 1) m (H1Class m hm P v₀)) = 1 := by
  rw [relative_pairing_coefficient, sweep_coefficient_one]

theorem ordinary_transgression_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    ordinaryTransgression m ≠ 0 := by
  intro hz
  have h := ordinary_pairing_one m hm P v₀
  rw [hz, map_zero, LinearMap.zero_apply] at h
  exact zero_ne_one h

theorem H1_transgression_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    H1TransgressionClass m ≠ 0 := by
  intro hz
  have h := H1_pairing_one m hm P v₀
  rw [hz, map_zero, LinearMap.zero_apply] at h
  exact zero_ne_one h

theorem relative_transgression_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    relativeTransgressionClass m ≠ 0 := by
  intro hz
  apply H1_transgression_ne_zero m hm P v₀
  rw [← relative_absolute m hm, hz, map_zero]

theorem relative_homology_ne_zero (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) :
    ConstantRelativePairing.homologyToRelative (m + 1) m (H1Class m hm P v₀) ≠ 0 := by
  intro hz
  have h := relative_pairing_one m hm P v₀
  rw [hz, map_zero] at h
  exact zero_ne_one h

end
end Finsler.MeridianPrimitiveNonzero
