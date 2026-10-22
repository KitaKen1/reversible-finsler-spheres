module

public import Finsler.Loop.SphereProductReducedKernel
public import Finsler.Loop.PathSphereHomologyTower

/-! The contractible actual starting-path total space supplies a section
of its MV map. The south-only summand lands in the north-projection kernel,
and yields a genuine injection lowering based-path degree by n-1. -/
@[expose] public section
namespace Finsler.StartingPathReducedKernel
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.SphereGeometry Finsler.CochainComparison Finsler.MeridianLoopFamily
open Finsler.H1PuncturedEvaluationChart Finsler.StartingPathSphereCover
open Finsler.StartingPathRotorHomology Finsler.MeridianEquatorHomology
open Finsler.ProductReducedKernelStep
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000

theorem into_kernel {n : ℕ} (x a : Sphere n) (v : equator a) (k : ℕ) :
    ∃ f : homologyZMod2 (TopCat.of (Path x a)) (k + 1) →ₗ[ZMod 2]
      kernel (NativeEvaluationMayerVietoris.baseOverlap a) (TopCat.of (Path x a)) (k + 1),
      Function.Injective f := by
  let hz := PathSphereHomologyGap.equator_in_overlap a v
  let e := (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (k + 1)).obj coeff).mapIso
    (StartingPathOverlapChart.iso x a)).toLinearEquiv
  let h := (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) (k + 1)).obj coeff).mapIso
    (TopCat.isoOfHomeo (X := TopCat.of (Path x v.val)) (Y := TopCat.of (Path x a))
      (StartingPathRotorChart.fixedFiberHomeomorph x a ⟨v.val, hz.1⟩))).toLinearEquiv
  let j := (homologyPushZMod2 (fiberToOverlap x a v.val hz ≫ south x a) (k + 1)).hom.comp h.symm.toLinearMap
  have hj : Function.Injective j := (south_injective x a v.val hz (k + 1)).comp h.symm.injective
  obtain ⟨g, hg⟩ := (toPatches x a (k + 1)).hom.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (toPatches_surjective x a k))
  let i := (biprod.inr : homologyZMod2 (patch x (antipode a)) (k + 1) ⟶ patches x a (k + 1)).hom
  let w := g.comp (i.comp j)
  have hw (z : homologyZMod2 (TopCat.of (Path x a)) (k + 1)) :
      (toPatches x a (k + 1)).hom (w z) = i (j z) := LinearMap.congr_fun hg (i (j z))
  have hN : toPatches x a (k + 1) ≫ biprod.fst = homologyPushZMod2 (north x a) (k + 1) :=
    SSet.mayerVietorisToBiprod_fst coeff _ _ (k + 1)
  have hn (z : homologyZMod2 (TopCat.of (Path x a)) (k + 1)) :
      (homologyPushZMod2 (north x a) (k + 1)).hom (w z) = 0 := by
    have he := ConcreteCategory.congr_hom hN (w z)
    change (biprod.fst : patches x a (k + 1) ⟶ _).hom
      ((toPatches x a (k + 1)).hom (w z)) = _ at he
    rw [hw] at he
    have hi := ConcreteCategory.congr_hom (biprod.inr_fst
      (X := homologyZMod2 (patch x a) (k + 1)) (Y := homologyZMod2 (patch x (antipode a)) (k + 1))) (j z)
    exact he.symm.trans hi
  have hsquare : (StartingPathOverlapChart.iso x a).hom ≫
      ProductHomologyZeroDetection.second (NativeEvaluationMayerVietoris.baseOverlap a) (TopCat.of (Path x a)) =
      north x a ≫ alignment x a := by ext p : 1; rfl
  let f : homologyZMod2 (TopCat.of (Path x a)) (k + 1) →ₗ[ZMod 2]
      kernel (NativeEvaluationMayerVietoris.baseOverlap a) (TopCat.of (Path x a)) (k + 1) :=
    (e.toLinearMap.comp w).codRestrict _ (by
      intro z
      change (homologyPushZMod2 (ProductHomologyZeroDetection.second _ _) (k + 1)).hom
        ((homologyPushZMod2 (StartingPathOverlapChart.iso x a).hom (k + 1)).hom (w z)) = 0
      rw [SplitPairHomologyKernel.push_comp_apply, hsquare,
        ← SplitPairHomologyKernel.push_comp_apply, hn, map_zero])
  refine ⟨f, fun u z huz => hj ?_⟩
  have he : e (w u) = e (w z) := congrArg Subtype.val huz
  have hi : i (j u) = i (j z) := (hw u).symm.trans
    ((congrArg (toPatches x a (k + 1)).hom (e.injective he)).trans (hw z))
  have hu := ConcreteCategory.congr_hom (biprod.inr_snd
    (X := homologyZMod2 (patch x a) (k + 1)) (Y := homologyZMod2 (patch x (antipode a)) (k + 1))) (j u)
  have hz' := ConcreteCategory.congr_hom (biprod.inr_snd
    (X := homologyZMod2 (patch x a) (k + 1)) (Y := homologyZMod2 (patch x (antipode a)) (k + 1))) (j z)
  exact hu.symm.trans ((congrArg (biprod.snd : patches x a (k + 1) ⟶ _).hom hi).trans hz')

theorem degree_step (m q : ℕ) (hm : 1 ≤ m) (x a : Sphere (m + 1)) (v : equator a) :
    ∃ f : homologyZMod2 (TopCat.of (Path x a)) (m + q) →ₗ[ZMod 2]
      homologyZMod2 (TopCat.of (Path x a)) q, Function.Injective f := by
  have hi : ∃ f : homologyZMod2 (TopCat.of (Path x a)) (m + q) →ₗ[ZMod 2]
      kernel (NativeEvaluationMayerVietoris.baseOverlap a) (TopCat.of (Path x a)) (m + q),
      Function.Injective f := by
    have he : m + q = (m + q - 1) + 1 := by omega
    exact (congrArg (fun d => ∃ f : homologyZMod2 (TopCat.of (Path x a)) d →ₗ[ZMod 2]
      kernel (NativeEvaluationMayerVietoris.baseOverlap a) (TopCat.of (Path x a)) d,
      Function.Injective f) he).mpr (into_kernel x a v (m + q - 1))
  obtain ⟨f, hf⟩ := hi
  obtain ⟨g, hg⟩ := SphereProductReducedKernel.embedding_of_equiv m q
    (orthogonal_dimension (antipode a)) (NativeEvaluationConnectedFiber.baseOverlapEquiv a) (TopCat.of (Path x a))
  exact ⟨g.comp f, hg.comp hf⟩

end
end Finsler.StartingPathReducedKernel
