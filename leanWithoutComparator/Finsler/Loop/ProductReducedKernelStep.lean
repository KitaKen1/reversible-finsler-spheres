module

public import Finsler.Loop.ProductMayerVietorisDetection

/-! Actual second-projection kernels descend by the actual product-cover
boundary. Only an injection is needed; no Kunneth decomposition is assumed. -/
@[expose] public section
namespace Finsler.ProductReducedKernelStep
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductHomologyDetectionTransport Finsler.ProductMayerVietorisCover
open Finsler.ProductMayerVietorisKernel Finsler.ProductMayerVietorisDetection
open scoped ContinuousMap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

abbrev kernel (X Y : TopCat.{0}) (k : ℕ) :=
  LinearMap.ker (homologyPushZMod2 (second X Y) k).hom

theorem transport {X X' : TopCat.{0}} (e : X ≃ₕ X') (Y : TopCat.{0}) (k : ℕ) :
    ∃ f : kernel X Y k →ₗ[ZMod 2] kernel X' Y k, Function.Injective f := by
  let h := (productEquiv e Y).singularHomologyIso coeff k
  have hh : h.hom = homologyPushZMod2 (mapFirst (TopCat.ofHom e.toFun) Y) k :=
    (productEquiv e Y).singularHomologyIso_hom coeff k
  let f : kernel X Y k →ₗ[ZMod 2] kernel X' Y k :=
    (h.hom.hom.comp (kernel X Y k).subtype).codRestrict _ (by
      intro z
      change (homologyPushZMod2 (second X' Y) k).hom (h.hom.hom z.val) = 0
      rw [hh]
      change (homologyPushZMod2 (second X' Y) k).hom
        ((homologyPushZMod2 (mapFirst (X := X) (X' := X') (TopCat.ofHom e.toFun) Y) k).hom z.val) = 0
      rw [SplitPairHomologyKernel.push_comp_apply, mapFirst_second]
      exact z.property)
  refine ⟨f, fun a b hab => Subtype.ext (h.toLinearEquiv.injective ?_)⟩
  exact congrArg Subtype.val hab

theorem boundary_injective {X : TopCat.{0}} [PathConnectedSpace X] {U V : Set X}
    [ContractibleSpace U] [ContractibleSpace V] (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ)
    (z : homologyZMod2 (product X Y) (k + 1))
    (hz : (homologyPushZMod2 (second X Y) (k + 1)).hom z = 0)
    (hd : (delta Y hU hV hUV k).hom z = 0) : z = 0 := by
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp (exact_full Y hU hV hUV k) z hd
  change (fromPatches U V Y (k + 1)).hom c = z at hc
  obtain ⟨x⟩ := PathConnectedSpace.nonempty (X := X)
  have he := ConcreteCategory.congr_hom (fromPatches_factor U V Y x (k + 1)) c
  change (homologyPushZMod2 (fiberSection X Y x) (k + 1)).hom
    ((homologyPushZMod2 (second X Y) (k + 1)).hom
      ((fromPatches U V Y (k + 1)).hom c)) = (fromPatches U V Y (k + 1)).hom c at he
  rw [hc, hz, map_zero] at he
  exact he.symm

theorem step {X : TopCat.{0}} [PathConnectedSpace X] {U V : Set X}
    [ContractibleSpace U] [ContractibleSpace V] (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ) :
    ∃ f : kernel X Y (k + 1) →ₗ[ZMod 2] kernel (TopCat.of (U ∩ V : Set X)) Y k,
      Function.Injective f := by
  let e := (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso
    (TopCat.isoOfHomeo (overlapHomeomorph U V Y))).toLinearEquiv
  let d := (delta Y hU hV hUV k).hom
  let f : kernel X Y (k + 1) →ₗ[ZMod 2] kernel (TopCat.of (U ∩ V : Set X)) Y k :=
    ((e.toLinearMap.comp d).comp (kernel X Y (k + 1)).subtype).codRestrict _ (by
      intro z
      change (homologyPushZMod2 (second _ Y) k).hom
        ((homologyPushZMod2 (TopCat.isoOfHomeo (overlapHomeomorph U V Y)).hom k).hom
          (d z.val)) = 0
      rw [SplitPairHomologyKernel.push_comp_apply, overlap_second_factor]
      exact delta_second_zero Y hU hV hUV k z.val)
  refine ⟨f, ?_⟩
  intro a b hab
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply boundary_injective Y hU hV hUV k (a.val - b.val)
  · rw [map_sub, a.property, b.property, sub_self]
  · have he : e (d a.val) = e (d b.val) := congrArg Subtype.val hab
    change d (a.val - b.val) = 0
    rw [map_sub, e.injective he, sub_self]

end
end Finsler.ProductReducedKernelStep
