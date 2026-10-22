module

public import Finsler.Loop.StartingPathReducedKernel

/-! Actual path and strong-H1 based homology in every multiple of n-1
embeds in the coefficient field. No polynomial-ring presentation is needed. -/
@[expose] public section
namespace Finsler.PathSphereRankTower
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem zero_embedding (X : TopCat.{0}) [PathConnectedSpace X] :
    ∃ f : homologyZMod2 X 0 →ₗ[ZMod 2] ZMod 2, Function.Injective f := by
  exact ⟨(X.singularHomology₀ε coeff).hom, (ModuleCat.mono_iff_injective _).mp inferInstance⟩

theorem path_embedding (m : ℕ) (hm : 1 ≤ m) (x a : Sphere (m + 1)) (v : equator a) (k : ℕ) :
    ∃ f : homologyZMod2 (TopCat.of (Path x a)) (k * m) →ₗ[ZMod 2] ZMod 2,
      Function.Injective f := by
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    have := SpherePathSpaceConnected.pathConnected (by omega : 2 ≤ m + 1) x a
    exact zero_embedding _
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    have hs := StartingPathReducedKernel.degree_step m (k * m) hm x a v
    rw [show m + k * m = (k + 1) * m by ring] at hs
    obtain ⟨f, hf⟩ := hs
    exact ⟨g.comp f, hg.comp hf⟩

theorem based_embedding (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    ∃ f : homologyZMod2 (TopCat.of (H1LocalFiber.based P)) (k * m) →ₗ[ZMod 2] ZMod 2,
      Function.Injective f := by
  obtain ⟨f, hf⟩ := path_embedding m hm P P v₀ k
  let e := (BasedLoopPathSpace.homologyIso P (k * m)).toLinearEquiv
  let j := (homologyPushZMod2 (BasedContinuousLoopModel.inclusion P) (k * m)).hom
  have hj : Function.Injective j := BasedLoopHomologyInjection.homology_injective P (k * m)
  exact ⟨f.comp (e.toLinearMap.comp j), hf.comp (e.injective.comp hj)⟩

theorem based_finite_rank_le_one (m : ℕ) (hm : 1 ≤ m) (P : Sphere (m + 1)) (v₀ : equator P) (k : ℕ) :
    Module.Finite (ZMod 2) (homologyZMod2 (TopCat.of (H1LocalFiber.based P)) (k * m)) ∧
      Module.finrank (ZMod 2) (homologyZMod2 (TopCat.of (H1LocalFiber.based P)) (k * m)) ≤ 1 := by
  obtain ⟨f, hf⟩ := based_embedding m hm P v₀ k
  have := Module.Finite.of_injective f hf
  exact ⟨inferInstance, (LinearMap.finrank_le_finrank_of_injective hf).trans_eq (Module.finrank_self _)⟩

end
end Finsler.PathSphereRankTower
