module

public import Finsler.Loop.PathSphereHomologyTower

/-! In EVERY degree k*(n-1)+1 the actual free-loop homology embeds
by the actual evaluation-cover boundary, and is isomorphic to the
kernel of the actual overlap-to-patches map. This supplies the full
Theta tower, but does not assert that this kernel has rank one. -/
@[expose] public section
namespace Finsler.NativeThetaCoverKernel
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.MeridianLoopFamily Finsler.NativeEvaluationMayerVietoris
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

variable (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P)

include hm v₀ in
theorem fromPatches_zero (k : ℕ) : fromPatches P (k * m + 1) = 0 := by
  have hN := PathSphereHomologyTower.based_tower_zero m hm P v₀ k
  exact NativeEvaluationPatchGap.fromPatches_zero_of_based P (k * m + 1) hN
    (H1BasedFiberTransport.homology_zero_transport P (antipode P) (k * m + 1) hN)

include hm v₀ in
theorem boundary_injective (k : ℕ) : Function.Injective (delta P (k * m)).hom :=
  delta_injective_of_fromPatches_zero P (k * m) (fromPatches_zero m hm P v₀ k)

def boundaryToKernel (k : ℕ) :
    homologyZMod2 (fullPair (m + 1)).fst (k * m + 1) →ₗ[ZMod 2]
      LinearMap.ker (toPatches P (k * m)).hom :=
  (delta P (k * m)).hom.codRestrict (LinearMap.ker (toPatches P (k * m)).hom) (by
    intro z
    exact (ConcreteCategory.congr_hom (delta_toPatches P (k * m)) z).trans rfl)

def kernelEquiv (k : ℕ) :
    homologyZMod2 (fullPair (m + 1)).fst (k * m + 1) ≃ₗ[ZMod 2]
      LinearMap.ker (toPatches P (k * m)).hom :=
  LinearEquiv.ofBijective (boundaryToKernel m P k) (by
    constructor
    · intro x y h
      exact boundary_injective m hm P v₀ k (congrArg Subtype.val h)
    · intro z
      obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp (exact_overlap P (k * m))
        z.val z.property
      exact ⟨w, Subtype.ext hw⟩)

def h1KernelEquiv (k : ℕ) :
    homologyZMod2 (Loops (m + 1)) (k * m + 1) ≃ₗ[ZMod 2]
      LinearMap.ker (toPatches P (k * m)).hom :=
  (NativeUnitEvaluationKernelRoute.fullHomology (m + 1) (k * m + 1)).symm.trans
    (kernelEquiv m hm P v₀ k)

theorem kernelEquiv_apply (k : ℕ) (z : homologyZMod2 (fullPair (m + 1)).fst (k * m + 1)) :
    (kernelEquiv m hm P v₀ k z).val = (delta P (k * m)).hom z := rfl

end
end Finsler.NativeThetaCoverKernel
