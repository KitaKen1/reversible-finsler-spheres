module

public import Finsler.Loop.SphereProductBelowDetection
public import Finsler.Loop.StartingPathReducedKernel

/-! Actual based-path homology vanishes in every nonzero residue
modulo n-1. This supplies the preceding-degree gap needed for GH inputs. -/
@[expose] public section
namespace Finsler.PathSphereResidueVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
open Finsler.MeridianEquatorHomology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem path_below_zero (m q : ℕ) (hq : 0 < q) (hqm : q < m)
    (x a : Sphere (m + 1)) (v : equator a) :
    IsZero (homologyZMod2 (TopCat.of (Path x a)) q) := by
  have hi := ProductFiberGeneration.second_injective_of_equiv
    (NativeEvaluationConnectedFiber.baseOverlapEquiv a) (TopCat.of (Path x a)) q
    (SphereProductBelowDetection.second_below_injective m q hqm (orthogonal_dimension (antipode a)) _)
  have he : q = (q - 1) + 1 := by omega
  have hf : ∃ f : homologyZMod2 (TopCat.of (Path x a)) q →ₗ[ZMod 2]
      ProductReducedKernelStep.kernel (NativeEvaluationMayerVietoris.baseOverlap a) (TopCat.of (Path x a)) q,
      Function.Injective f := by
    exact (congrArg (fun d => ∃ f : homologyZMod2 (TopCat.of (Path x a)) d →ₗ[ZMod 2]
      ProductReducedKernelStep.kernel (NativeEvaluationMayerVietoris.baseOverlap a) (TopCat.of (Path x a)) d,
      Function.Injective f) he).mpr (StartingPathReducedKernel.into_kernel x a v (q - 1))
  obtain ⟨f, hf⟩ := hf
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun z w => hf (Subtype.ext (hi ?_))⟩
  exact (f z).property.trans (f w).property.symm

theorem path_residue_zero (m q : ℕ) (hq : 0 < q) (hqm : q < m)
    (x a : Sphere (m + 1)) (v : equator a) (k : ℕ) :
    IsZero (homologyZMod2 (TopCat.of (Path x a)) (k * m + q)) := by
  induction k with
  | zero => simpa only [Nat.zero_mul, Nat.zero_add] using path_below_zero m q hq hqm x a v
  | succ k ih =>
    have h := StartingPathReducedKernel.degree_step m (k * m + q) (by omega) x a v
    rw [show m + (k * m + q) = (k + 1) * m + q by ring] at h
    obtain ⟨f, hf⟩ := h
    have hs := ModuleCat.subsingleton_of_isZero ih
    exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun z w => hf (hs.elim _ _)⟩

theorem based_residue_zero (m q : ℕ) (hq : 0 < q) (hqm : q < m)
    (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    IsZero (homologyZMod2 (TopCat.of (H1LocalFiber.based P)) (k * m + q)) :=
  NativeEvaluationOrdinaryBasedGap.based_zero_of_path_zero P (k * m + q)
    (path_residue_zero m q hq hqm P P v₀ k)

end
end Finsler.PathSphereResidueVanishing
