module

public import Finsler.Loop.PathSphereResidueVanishing
public import Finsler.Loop.NativeThetaRankOne

/-! The actual evaluation-cover boundary vanishes in positive multiples
of n-1. The actual patch sum therefore generates those full-loop degrees. -/
@[expose] public section
namespace Finsler.NativeGHCoverSurjectivity
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop Finsler.MeridianLoopFamily
open Finsler.MeridianEquatorHomology Finsler.NativeEvaluationMayerVietoris
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem toPatches_prev_injective (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1))
    (v₀ : equator P) (k : ℕ) : Function.Injective (toPatches P ((k + 1) * m - 1)).hom := by
  cases k with
  | zero =>
    have hb : Function.Injective (toPatches P (m - 1)).hom := by
      have hi := ProductFiberGeneration.second_injective_of_equiv
        (NativeEvaluationConnectedFiber.baseOverlapEquiv P) (TopCat.of (H1LocalFiber.based P)) (m - 1)
        (SphereProductBelowDetection.second_below_injective m (m - 1) (by omega)
          (orthogonal_dimension (antipode P)) _)
      intro a b hab
      apply sub_eq_zero.mp
      let e := NativeEvaluationProductDetection.homology P (m - 1)
      apply e.injective
      rw [map_zero]
      apply hi
      rw [map_zero]
      exact NativeEvaluationProductDetection.fiber_projection_zero P (m - 1) (a - b)
        (by rw [map_sub, hab, sub_self])
    exact (congrArg (fun d => Function.Injective (toPatches P d).hom)
      (show (0 + 1) * m - 1 = m - 1 by simp)).mpr hb
  | succ k =>
    have h := NativeThetaRankOne.kernel_embedding m (k * m + (m - 1)) P
    rw [show m + (k * m + (m - 1)) = (k + 1 + 1) * m - 1 by
      simp only [Nat.add_mul, Nat.one_mul]; omega] at h
    obtain ⟨f, hf⟩ := h
    have hs := ModuleCat.subsingleton_of_isZero
      (PathSphereResidueVanishing.based_residue_zero m (m - 1) (by omega) (by omega) P v₀ k)
    intro a b hab
    let z : LinearMap.ker (toPatches P ((k + 1 + 1) * m - 1)).hom :=
      ⟨a - b, by change _ = 0; rw [map_sub, hab, sub_self]⟩
    have hz : z = 0 := hf (hs.elim _ _)
    exact sub_eq_zero.mp (congrArg Subtype.val hz)

theorem fromPatches_surjective (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1))
    (v₀ : equator P) (k : ℕ) : Function.Surjective (fromPatches P ((k + 1) * m)).hom := by
  have hi := toPatches_prev_injective m hm P v₀ k
  have hs : Function.Surjective (fromPatches P (((k + 1) * m - 1) + 1)).hom := by
    intro z
    apply (ShortComplex.moduleCat_exact_iff _).mp (exact_full P ((k + 1) * m - 1)) z
    apply hi
    rw [map_zero]
    exact (ConcreteCategory.congr_hom (delta_toPatches P ((k + 1) * m - 1)) z).trans rfl
  have he : ((k + 1) * m - 1) + 1 = (k + 1) * m := by
    have : 0 < (k + 1) * m := Nat.mul_pos (by omega) (by omega)
    omega
  exact (congrArg (fun d => Function.Surjective (fromPatches P d).hom) he).mp hs

end
end Finsler.NativeGHCoverSurjectivity
