module

public import Finsler.Loop.PathSphereRankTower
public import Finsler.Loop.NativeThetaCoverKernel

/-! Compute the actual evaluation-cover kernel and actual free-loop homology
in every original Theta-power degree. The original nonzero Theta power spans. -/
@[expose] public section
namespace Finsler.NativeThetaRankOne
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.BorelLoop
open Finsler.MeridianLoopFamily Finsler.MeridianEquatorHomology
open Finsler.NativeEvaluationMayerVietoris
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem kernel_embedding (m q : ℕ) (P : Sphere (m + 1)) :
    ∃ f : LinearMap.ker (toPatches P (m + q)).hom →ₗ[ZMod 2]
      homologyZMod2 (TopCat.of (H1LocalFiber.based P)) q, Function.Injective f := by
  let e := NativeEvaluationProductDetection.homology P (m + q)
  let f : LinearMap.ker (toPatches P (m + q)).hom →ₗ[ZMod 2]
      ProductReducedKernelStep.kernel (baseOverlap P) (TopCat.of (H1LocalFiber.based P)) (m + q) :=
    (e.toLinearMap.comp (LinearMap.ker (toPatches P (m + q)).hom).subtype).codRestrict _ (by
      intro z
      exact NativeEvaluationProductDetection.fiber_projection_zero P (m + q) z.val z.property)
  have hf : Function.Injective f := fun a b h => Subtype.ext (e.injective (congrArg Subtype.val h))
  obtain ⟨g, hg⟩ := SphereProductReducedKernel.embedding_of_equiv m q
    (orthogonal_dimension (antipode P)) (NativeEvaluationConnectedFiber.baseOverlapEquiv P)
    (TopCat.of (H1LocalFiber.based P))
  exact ⟨g.comp f, hg.comp hf⟩

theorem full_embedding (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    ∃ f : homologyZMod2 (fullPair (m + 1)).fst ((k + 1) * m + 1) →ₗ[ZMod 2] ZMod 2,
      Function.Injective f := by
  let e := NativeThetaCoverKernel.kernelEquiv m hm P v₀ (k + 1)
  have hi := kernel_embedding m (k * m) P
  rw [show m + k * m = (k + 1) * m by ring] at hi
  obtain ⟨f, hf⟩ := hi
  obtain ⟨g, hg⟩ := PathSphereRankTower.based_embedding m (by omega) P v₀ k
  exact ⟨g.comp (f.comp e.toLinearMap), hg.comp (hf.comp e.injective)⟩

theorem theta_embedding (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    ∃ f : homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r) →ₗ[ZMod 2] ZMod 2,
      Function.Injective f := by
  have hd : NativeThetaPowers.degree m r = ((2 * r + 2) + 1) * m + 1 := by
    rw [NativeThetaPowers.degree_formula]
    ring
  rw [hd]
  obtain ⟨f, hf⟩ := full_embedding m hm P v₀ (2 * r + 2)
  let e := (NativeUnitEvaluationKernelRoute.fullHomology (m + 1) (((2 * r + 2) + 1) * m + 1)).symm
  exact ⟨f.comp e.toLinearMap, hf.comp e.injective⟩

theorem theta_finrank_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    Module.finrank (ZMod 2) (homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r)) = 1 := by
  obtain ⟨f, hf⟩ := theta_embedding m hm P v₀ r
  have := Module.Finite.of_injective f hf
  have hle := (LinearMap.finrank_le_finrank_of_injective hf).trans_eq (Module.finrank_self (ZMod 2))
  have hpos : 0 < Module.finrank (ZMod 2) (homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨NativeThetaPowers.fullPower m hm (Geometry.roundMetric (m + 1)) P v₀ r,
        NativeThetaPowers.fullPower_ne_zero m hm (Geometry.roundMetric (m + 1)) P v₀ r⟩
  omega

theorem full_finrank_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    Module.finrank (ZMod 2) (homologyZMod2 (fullPair (m + 1)).fst (NativeThetaPowers.degree m r)) = 1 :=
  (NativeUnitEvaluationKernelRoute.fullHomology (m + 1) (NativeThetaPowers.degree m r)).finrank_eq.trans
    (theta_finrank_one m hm P v₀ r)

theorem ordinary_finrank_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    Module.finrank (ZMod 2) (homologyZMod2 (ContinuousLoopModel.space (m + 1)) (NativeThetaPowers.degree m r)) = 1 :=
  (NativeUnitEvaluationKernelRoute.ordinaryHomology (m + 1) (NativeThetaPowers.degree m r)).finrank_eq.symm.trans
    (full_finrank_one m hm P v₀ r)

theorem cover_kernel_finrank_one (m : ℕ) (hm : 2 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ) :
    Module.finrank (ZMod 2) (LinearMap.ker (toPatches P ((2 * r + 3) * m)).hom) = 1 := by
  have h := theta_finrank_one m hm P v₀ r
  have hd : NativeThetaPowers.degree m r = (2 * r + 3) * m + 1 := by
    rw [NativeThetaPowers.degree_formula]
    ring
  rw [hd] at h
  exact (NativeThetaCoverKernel.h1KernelEquiv m hm P v₀ (2 * r + 3)).finrank_eq.symm.trans h

theorem theta_spans (m : ℕ) (hm : 2 ≤ m) (F : Geometry.ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r)) :
    ∃ c : ZMod 2, c • NativeThetaPowers.fullPower m hm F P v₀ r = z :=
  exists_smul_eq_of_finrank_eq_one (theta_finrank_one m hm P v₀ r)
    (NativeThetaPowers.fullPower_ne_zero m hm F P v₀ r) z

theorem nonzero_eq_theta (m : ℕ) (hm : 2 ≤ m) (F : Geometry.ReversibleMetric (m + 1))
    (P : Sphere (m + 1)) (v₀ : equator P) (r : ℕ)
    (z : homologyZMod2 (Loops (m + 1)) (NativeThetaPowers.degree m r)) (hz : z ≠ 0) :
    z = NativeThetaPowers.fullPower m hm F P v₀ r := by
  obtain ⟨c, hc⟩ := theta_spans m hm F P v₀ r z
  have hcases : c = 0 ∨ c = 1 := by fin_cases c <;> simp
  rcases hcases with rfl | rfl
  · simp only [zero_smul] at hc
    exact (hz hc.symm).elim
  · simpa only [one_smul] using hc.symm

theorem fullPower_independent (m : ℕ) (hm : 2 ≤ m)
    (F G : Geometry.ReversibleMetric (m + 1)) (P Q : Sphere (m + 1))
    (v₀ : equator P) (w₀ : equator Q) (r : ℕ) :
    NativeThetaPowers.fullPower m hm G Q w₀ r = NativeThetaPowers.fullPower m hm F P v₀ r :=
  nonzero_eq_theta m hm F P v₀ r _ (NativeThetaPowers.fullPower_ne_zero m hm G Q w₀ r)

end
end Finsler.NativeThetaRankOne
