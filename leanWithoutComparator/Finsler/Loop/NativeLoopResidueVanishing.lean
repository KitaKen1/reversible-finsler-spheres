module

public import Finsler.Loop.NativeLoopLowDegreeVanishing

/-! The actual evaluation cover eliminates EVERY free-loop homology
degree k*m+q with 2 <= q < m. No loop-space decomposition is assumed. -/
@[expose] public section
namespace Finsler.NativeLoopResidueVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.MeridianLoopFamily Finsler.NativeEvaluationMayerVietoris
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000

theorem toPatches_residue_injective (m q : ℕ) (hq : 0 < q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    Function.Injective (toPatches P (k * m + q)).hom := by
  cases k with
  | zero =>
    exact (congrArg (fun d => Function.Injective (toPatches P d).hom)
      (show 0 * m + q = q by omega)).mpr
        (NativeLoopLowDegreeVanishing.toPatches_below_injective m q hqm P)
  | succ k =>
    obtain ⟨f, hf⟩ := NativeThetaRankOne.kernel_embedding m (k * m + q) P
    have hs := ModuleCat.subsingleton_of_isZero
      (PathSphereResidueVanishing.based_residue_zero m q hq hqm P v₀ k)
    have hi : Function.Injective (toPatches P (m + (k * m + q))).hom := by
      intro a b hab
      let z : LinearMap.ker (toPatches P (m + (k * m + q))).hom :=
        ⟨a - b, by change _ = 0; rw [map_sub, hab, sub_self]⟩
      have hz : z = 0 := hf (hs.elim _ _)
      exact sub_eq_zero.mp (congrArg Subtype.val hz)
    have he : m + (k * m + q) = (k + 1) * m + q := by ring
    exact (congrArg (fun d => Function.Injective (toPatches P d).hom) he).mp hi

theorem fromPatches_residue_surjective (m q : ℕ) (hq : 2 ≤ q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    Function.Surjective (fromPatches P (k * m + q)).hom := by
  have hi := toPatches_residue_injective m (q - 1) (by omega) (by omega) P v₀ k
  have hs : Function.Surjective (fromPatches P ((k * m + (q - 1)) + 1)).hom := by
    intro z
    apply (ShortComplex.moduleCat_exact_iff _).mp (exact_full P (k * m + (q - 1))) z
    apply hi
    rw [map_zero]
    exact (ConcreteCategory.congr_hom (delta_toPatches P (k * m + (q - 1))) z).trans rfl
  exact (congrArg (fun d => Function.Surjective (fromPatches P d).hom)
    (show k * m + (q - 1) + 1 = k * m + q by omega)).mp hs

theorem full_zero (m q : ℕ) (hq : 2 ≤ q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    IsZero (homologyZMod2 (fullPair (m + 1)).fst (k * m + q)) := by
  have hb := PathSphereResidueVanishing.based_residue_zero m q (by omega) hqm P v₀ k
  have hS := H1BasedFiberTransport.homology_zero_transport P (antipode P) (k * m + q) hb
  have hp := ModuleCat.subsingleton_of_isZero
    (hS.of_iso (H1PuncturedPatchHomology.fullDomainHomologyIso (antipode P) (k * m + q)))
  have hs := NativeEvaluationPatchGeneration.south_generates P v₀ (k * m + q)
    (fromPatches_residue_surjective m q hq hqm P v₀ k)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, rfl⟩ := hs a
  obtain ⟨y, rfl⟩ := hs b
  exact congrArg _ (hp.elim x y)

theorem h1_zero (m q : ℕ) (hq : 2 ≤ q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    IsZero (homologyZMod2 (Loops (m + 1)) (k * m + q)) := by
  have hs := ModuleCat.subsingleton_of_isZero (full_zero m q hq hqm P v₀ k)
  let e := NativeUnitEvaluationKernelRoute.fullHomology (m + 1) (k * m + q)
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => e.symm.injective (hs.elim _ _)⟩

theorem ordinary_zero (m q : ℕ) (hq : 2 ≤ q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    IsZero (homologyZMod2 (ContinuousLoopModel.space (m + 1)) (k * m + q)) := by
  have hs := ModuleCat.subsingleton_of_isZero (full_zero m q hq hqm P v₀ k)
  let e := NativeUnitEvaluationKernelRoute.ordinaryHomology (m + 1) (k * m + q)
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => e.symm.injective (hs.elim _ _)⟩

theorem cohomology_eq_zero (m q : ℕ) (hq : 2 ≤ q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ)
    (a : cohomologyZMod2 (Loops (m + 1)) (k * m + q)) : a = 0 := by
  have hs := ModuleCat.subsingleton_of_isZero (h1_zero m q hq hqm P v₀ k)
  apply kroneckerMap_injective (Loops (m + 1)) (k * m + q)
  rw [map_zero]
  apply LinearMap.ext
  intro z
  rw [hs.elim z 0, map_zero, LinearMap.zero_apply]

end
end Finsler.NativeLoopResidueVanishing
