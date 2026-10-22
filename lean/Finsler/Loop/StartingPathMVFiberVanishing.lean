module

public import Finsler.Loop.StartingPathSphereCover

/-! Exactness on the ACTUAL starting-path cover kills a fixed-fiber
group if that actual fiber generates the overlap and its two actual
patch maps are injective. No finite-rank or dimension assumption. -/
@[expose] public section
namespace Finsler.StartingPathMVFiberVanishing
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
open Finsler.StartingPathSphereCover Finsler.H1PuncturedEvaluationChart
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

theorem fiber_zero {n : ℕ} (x axis z : Sphere n) (hz : z ∈ base axis ∩ base (antipode axis)) (k : ℕ)
    (hj : Function.Surjective (homologyPushZMod2 (fiberToOverlap x axis z hz) (k + 1)).hom)
    (hN : Function.Injective (homologyPushZMod2 (fiberToOverlap x axis z hz ≫ north x axis) (k + 1)).hom)
    (hS : Function.Injective (homologyPushZMod2 (fiberToOverlap x axis z hz ≫ south x axis) (k + 1)).hom) :
    IsZero (homologyZMod2 (TopCat.of (Path x z)) (k + 1)) := by
  have hfst : toPatches x axis (k + 1) ≫ biprod.fst = homologyPushZMod2 (north x axis) (k + 1) :=
    SSet.mayerVietorisToBiprod_fst coeff _ _ _
  have hsnd : toPatches x axis (k + 1) ≫ biprod.snd = -homologyPushZMod2 (south x axis) (k + 1) :=
    SSet.mayerVietorisToBiprod_snd coeff _ _ _
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun a b => ?_⟩
  let u := (homologyPushZMod2 (fiberToOverlap x axis z hz ≫ north x axis) (k + 1)).hom (a - b)
  let c : patches x axis (k + 1) :=
    (biprod.inl : homologyZMod2 (patch x axis) (k + 1) ⟶ patches x axis (k + 1)).hom u
  obtain ⟨w, hw⟩ := toPatches_surjective x axis k c
  obtain ⟨v, hv⟩ := hj w
  have hSc : (homologyPushZMod2 (fiberToOverlap x axis z hz ≫ south x axis) (k + 1)).hom v = 0 := by
    have he := ConcreteCategory.congr_hom hsnd w
    change (biprod.snd : patches x axis (k + 1) ⟶ _).hom ((toPatches x axis (k + 1)).hom w) =
      -(homologyPushZMod2 (south x axis) (k + 1)).hom w at he
    rw [hw] at he
    have hc : (biprod.snd : patches x axis (k + 1) ⟶ _).hom c = 0 := by
      change ((biprod.inl : homologyZMod2 (patch x axis) (k + 1) ⟶ patches x axis (k + 1)) ≫
        biprod.snd).hom u = 0
      simp only [biprod.inl_snd, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [hc] at he
    rw [← SplitPairHomologyKernel.push_comp_apply, hv]
    exact neg_eq_zero.mp he.symm
  have hv0 : v = 0 := hS (hSc.trans (map_zero _).symm)
  have hw0 : w = 0 := by rw [← hv, hv0, map_zero]
  have hNc : u = 0 := by
    have he := ConcreteCategory.congr_hom hfst w
    change (biprod.fst : patches x axis (k + 1) ⟶ _).hom ((toPatches x axis (k + 1)).hom w) =
      (homologyPushZMod2 (north x axis) (k + 1)).hom w at he
    rw [hw, hw0, map_zero] at he
    have hc : (biprod.fst : patches x axis (k + 1) ⟶ _).hom c = u := by
      change ((biprod.inl : homologyZMod2 (patch x axis) (k + 1) ⟶ patches x axis (k + 1)) ≫
        biprod.fst).hom u = u
      simp only [biprod.inl_fst, ModuleCat.hom_id, LinearMap.id_apply]
    exact hc.symm.trans he
  exact sub_eq_zero.mp (hN (hNc.trans (map_zero _).symm))

end
end Finsler.StartingPathMVFiberVanishing
