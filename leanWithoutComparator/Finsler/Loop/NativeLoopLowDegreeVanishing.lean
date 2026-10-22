module

public import Finsler.Loop.NativeGHCoverSurjectivity
public import Finsler.Loop.NativeEvaluationPatchGeneration

/-! Actual free-loop homology and cohomology vanish in degrees 0<q<n-1.
The proof uses the original evaluation cover and the existing based-path gap. -/
@[expose] public section
namespace Finsler.NativeLoopLowDegreeVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.MeridianLoopFamily Finsler.MeridianEquatorHomology
open Finsler.NativeEvaluationMayerVietoris
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem toPatches_below_injective (m q : ℕ) (hqm : q < m) (P : Sphere (m + 1)) :
    Function.Injective (toPatches P q).hom := by
  have hi := ProductFiberGeneration.second_injective_of_equiv
    (NativeEvaluationConnectedFiber.baseOverlapEquiv P) (TopCat.of (H1LocalFiber.based P)) q
    (SphereProductBelowDetection.second_below_injective m q hqm
      (orthogonal_dimension (antipode P)) _)
  intro a b hab
  apply sub_eq_zero.mp
  let e := NativeEvaluationProductDetection.homology P q
  apply e.injective
  rw [map_zero]
  apply hi
  rw [map_zero]
  exact NativeEvaluationProductDetection.fiber_projection_zero P q (a - b)
    (by rw [map_sub, hab, sub_self])

theorem fromPatches_below_surjective (m q : ℕ) (hq : 0 < q) (hqm : q ≤ m)
    (P : Sphere (m + 1)) : Function.Surjective (fromPatches P q).hom := by
  have hi := toPatches_below_injective m (q - 1) (by omega) P
  have hs : Function.Surjective (fromPatches P ((q - 1) + 1)).hom := by
    intro z
    apply (ShortComplex.moduleCat_exact_iff _).mp (exact_full P (q - 1)) z
    apply hi
    rw [map_zero]
    exact (ConcreteCategory.congr_hom (delta_toPatches P (q - 1)) z).trans rfl
  exact (congrArg (fun d => Function.Surjective (fromPatches P d).hom)
    (show q - 1 + 1 = q by omega)).mp hs

theorem full_zero (m q : ℕ) (hq : 0 < q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) :
    IsZero (homologyZMod2 (fullPair (m + 1)).fst q) := by
  let w : equator (antipode P) := (equator_nonempty (by omega) (antipode P)).some
  have hb : IsZero (homologyZMod2 (TopCat.of (H1LocalFiber.based (antipode P))) q) := by
    simpa only [Nat.zero_mul, Nat.zero_add] using
      PathSphereResidueVanishing.based_residue_zero m q hq hqm (antipode P) w 0
  have hp := ModuleCat.subsingleton_of_isZero
    (hb.of_iso (H1PuncturedPatchHomology.fullDomainHomologyIso (antipode P) q))
  have hs := NativeEvaluationPatchGeneration.south_generates P v₀ q
    (fromPatches_below_surjective m q hq hqm.le P)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hs a
  obtain ⟨y, rfl⟩ := hs b
  exact congrArg _ (hp.elim x y)

theorem h1_zero (m q : ℕ) (hq : 0 < q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) :
    IsZero (homologyZMod2 (Loops (m + 1)) q) := by
  have hs := ModuleCat.subsingleton_of_isZero (full_zero m q hq hqm P v₀)
  let e := NativeUnitEvaluationKernelRoute.fullHomology (m + 1) q
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => e.symm.injective (hs.elim _ _)⟩

theorem ordinary_zero (m q : ℕ) (hq : 0 < q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) :
    IsZero (homologyZMod2 (ContinuousLoopModel.space (m + 1)) q) := by
  have hs := ModuleCat.subsingleton_of_isZero (full_zero m q hq hqm P v₀)
  let e := NativeUnitEvaluationKernelRoute.ordinaryHomology (m + 1) q
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => e.symm.injective (hs.elim _ _)⟩

theorem cohomology_eq_zero (m q : ℕ) (hq : 0 < q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) (a : cohomologyZMod2 (Loops (m + 1)) q) : a = 0 := by
  have hs := ModuleCat.subsingleton_of_isZero (h1_zero m q hq hqm P v₀)
  apply kroneckerMap_injective (Loops (m + 1)) q
  rw [map_zero]
  apply LinearMap.ext
  intro z
  rw [hs.elim z 0, map_zero, LinearMap.zero_apply]

end
end Finsler.NativeLoopLowDegreeVanishing
