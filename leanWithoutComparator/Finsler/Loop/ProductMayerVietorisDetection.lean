module

public import Finsler.Loop.ProductMayerVietorisKernel
public import Finsler.Loop.ProductHomologyContractiblePatch

/-! A genuine Mayer-Vietoris induction step for two-projection
detection. The first-factor opens are contractible; their images in
the total product are proved to lie in the same fiber section. -/
@[expose] public section
namespace Finsler.ProductMayerVietorisDetection
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductHomologyDetectionTransport Finsler.ProductHomologyContractiblePatch
open Finsler.ProductMayerVietorisCover Finsler.ProductMayerVietorisKernel
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem fromPatches_factor {X : TopCat.{0}} [PathConnectedSpace X] (U V : Set X)
    [ContractibleSpace U] [ContractibleSpace V] (Y : TopCat.{0}) (x : X) (k : ℕ) :
    fromPatches U V Y k ≫ homologyPushZMod2 (second X Y) k ≫
      homologyPushZMod2 (fiberSection X Y x) k = fromPatches U V Y k := by
  have hN : (biprod.inl : homologyZMod2 (patch U Y) k ⟶ patches U V Y k) ≫
      fromPatches U V Y k = homologyPushZMod2 (inclusion U Y) k :=
    SSet.inl_mayerVietorisFromBiprod coeff _ _ k
  have hS : (biprod.inr : homologyZMod2 (patch V Y) k ⟶ patches U V Y k) ≫
      fromPatches U V Y k = homologyPushZMod2 (inclusion V Y) k :=
    SSet.inr_mayerVietorisFromBiprod coeff _ _ k
  apply biprod.hom_ext'
  · rw [← Category.assoc, ← Category.assoc, hN, push_comp, inclusion_second]
    exact (patch_inclusion_factor U Y x k).symm
  · rw [← Category.assoc, ← Category.assoc, hS, push_comp, inclusion_second]
    exact (patch_inclusion_factor V Y x k).symm

theorem detects_of_open_cover {X : TopCat.{0}} [PathConnectedSpace X] {U V : Set X}
    [ContractibleSpace U] [ContractibleSpace V] (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ)
    (hd : Detects (TopCat.of (U ∩ V : Set X)) Y k) : Detects X Y (k + 1) := by
  intro z h₁ h₂
  have hδ : (delta Y hU hV hUV k).hom z = 0 := delta_zero Y hU hV hUV k hd z h₁
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp (exact_full Y hU hV hUV k) z hδ
  change (fromPatches U V Y (k + 1)).hom c = z at hc
  obtain ⟨x⟩ := PathConnectedSpace.nonempty (X := X)
  have he := ConcreteCategory.congr_hom (fromPatches_factor U V Y x (k + 1)) c
  change (homologyPushZMod2 (fiberSection X Y x) (k + 1)).hom
    ((homologyPushZMod2 (second X Y) (k + 1)).hom
      ((fromPatches U V Y (k + 1)).hom c)) = (fromPatches U V Y (k + 1)).hom c at he
  rw [hc, h₂, map_zero] at he
  exact he.symm

end
end Finsler.ProductMayerVietorisDetection
