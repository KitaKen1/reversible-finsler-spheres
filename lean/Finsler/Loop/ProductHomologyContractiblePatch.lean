module

public import Finsler.Loop.ProductHomologyDetectionTransport
public import Finsler.Loop.ProductMayerVietorisCover

/-! Maps from a contractible first factor have their whole homology
image in one actual fiber section. Path connectedness of the target
first factor makes the two patch sections agree in homology. -/
@[expose] public section
namespace Finsler.ProductHomologyContractiblePatch
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductHomologyDetectionTransport Finsler.ProductMayerVietorisCover
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem push_comp {A B C : TopCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (k : ℕ) :
    homologyPushZMod2 f k ≫ homologyPushZMod2 g k = homologyPushZMod2 (f ≫ g) k :=
  (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).map_comp f g).symm

theorem mapFirst_factor {A X : TopCat.{0}} [ContractibleSpace A] [PathConnectedSpace X]
    (f : A ⟶ X) (Y : TopCat.{0}) (x : X) (k : ℕ) :
    homologyPushZMod2 (mapFirst f Y) k =
      homologyPushZMod2 (second A Y) k ≫ homologyPushZMod2 (fiberSection X Y x) k := by
  let e := contractibleProductEquiv A Y
  let eH := e.singularHomologyIso coeff k
  let a : A := ((ContractibleSpace.hequiv_unit A).some).invFun ()
  have hf : eH.hom = homologyPushZMod2 (second A Y) k := by
    rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom]
    rfl
  have hi : eH.inv = homologyPushZMod2 (TopCat.ofHom e.invFun) k :=
    e.singularHomologyIso_inv coeff k
  have hs : eH.inv ≫ homologyPushZMod2 (second A Y) k = 𝟙 (homologyZMod2 Y k) := by
    rw [← hf]
    exact eH.inv_hom_id
  have hc : TopCat.ofHom e.invFun ≫ mapFirst f Y = fiberSection X Y (f a) := by
    ext y : 1
    rfl
  have hs' : homologyPushZMod2 (TopCat.ofHom e.invFun) k ≫
      homologyPushZMod2 (second A Y) k = 𝟙 (homologyZMod2 Y k) := by
    rw [← hi]
    exact hs
  apply (cancel_epi eH.inv).mp
  rw [hi]
  change (homologyPushZMod2 (TopCat.ofHom e.invFun) k ≫ homologyPushZMod2 (mapFirst f Y) k :
    homologyZMod2 Y k ⟶ homologyZMod2 (product X Y) k) =
    homologyPushZMod2 (TopCat.ofHom e.invFun) k ≫
      (homologyPushZMod2 (second A Y) k ≫ homologyPushZMod2 (fiberSection X Y x) k)
  rw [← Category.assoc, hs', Category.id_comp, push_comp, hc]
  exact fiberSection_homology_eq X Y (PathConnectedSpace.joined (f a) x) k

theorem patch_inclusion_factor {X : TopCat.{0}} [PathConnectedSpace X] (U : Set X)
    [ContractibleSpace U] (Y : TopCat.{0}) (x : X) (k : ℕ) :
    homologyPushZMod2 (inclusion U Y) k =
      homologyPushZMod2 (patchSecond U Y) k ≫ homologyPushZMod2 (fiberSection X Y x) k := by
  let e := TopCat.isoOfHomeo (patchHomeomorph U Y)
  let eH := ((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso e
  have h₁ : e.inv ≫ inclusion U Y =
      mapFirst (TopCat.ofHom (ContinuousMap.subtypeVal U)) Y := by ext p : 1; rfl
  have h₂ : e.inv ≫ patchSecond U Y = second (TopCat.of U) Y := by ext p : 1; rfl
  apply (cancel_epi eH.inv).mp
  change homologyPushZMod2 e.inv k ≫ homologyPushZMod2 (inclusion U Y) k =
    homologyPushZMod2 e.inv k ≫
      (homologyPushZMod2 (patchSecond U Y) k ≫ homologyPushZMod2 (fiberSection X Y x) k)
  rw [← Category.assoc, push_comp, push_comp, h₁, h₂]
  exact mapFirst_factor (TopCat.ofHom (ContinuousMap.subtypeVal U)) Y x k

end
end Finsler.ProductHomologyContractiblePatch
