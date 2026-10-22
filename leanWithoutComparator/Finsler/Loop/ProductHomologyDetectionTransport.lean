module

public import Finsler.Loop.ProductHomologyZeroDetection

/-! Transport actual two-projection detection along a homotopy
equivalence of the first factor. Contractible first factors need only
the second projection, in every degree. -/
@[expose] public section
namespace Finsler.ProductHomologyDetectionTransport
open CategoryTheory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open scoped ContinuousMap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def mapFirst {X X' : TopCat.{0}} (f : X ⟶ X') (Y : TopCat.{0}) : product X Y ⟶ product X' Y :=
  TopCat.ofHom (f.hom.prodMap (ContinuousMap.id Y))

theorem mapFirst_first {X X' : TopCat.{0}} (f : X ⟶ X') (Y : TopCat.{0}) :
    mapFirst f Y ≫ first X' Y = first X Y ≫ f := by ext p : 1; rfl

theorem mapFirst_second {X X' : TopCat.{0}} (f : X ⟶ X') (Y : TopCat.{0}) :
    mapFirst f Y ≫ second X' Y = second X Y := by ext p : 1; rfl

def productEquiv {X X' : TopCat.{0}} (e : X ≃ₕ X') (Y : TopCat.{0}) :
    product X Y ≃ₕ product X' Y := e.prodCongr (ContinuousMap.HomotopyEquiv.refl Y)

theorem detects_of_equiv {X X' : TopCat.{0}} (e : X ≃ₕ X') (Y : TopCat.{0}) (k : ℕ)
    (h : Detects X' Y k) : Detects X Y k := by
  intro z hz₁ hz₂
  let eH := (productEquiv e Y).singularHomologyIso coeff k
  have heH : eH.hom = homologyPushZMod2 (mapFirst (TopCat.ofHom e.toFun) Y) k :=
    (productEquiv e Y).singularHomologyIso_hom coeff k
  have hz' : eH.hom.hom z = 0 := by
    rw [heH]
    apply h
    · change (homologyPushZMod2 (first X' Y) k).hom
        ((homologyPushZMod2 (mapFirst (TopCat.ofHom e.toFun) Y) k).hom z) = 0
      rw [SplitPairHomologyKernel.push_comp_apply, mapFirst_first,
        ← SplitPairHomologyKernel.push_comp_apply, hz₁, map_zero]
    · change (homologyPushZMod2 (second X' Y) k).hom
        ((homologyPushZMod2 (mapFirst (TopCat.ofHom e.toFun) Y) k).hom z) = 0
      rw [SplitPairHomologyKernel.push_comp_apply, mapFirst_second]
      exact hz₂
  exact eH.toLinearEquiv.injective (hz'.trans (map_zero _).symm)

def contractibleProductEquiv (X Y : TopCat.{0}) [ContractibleSpace X] : product X Y ≃ₕ Y :=
  (((ContractibleSpace.hequiv_unit X).some).prodCongr
    (ContinuousMap.HomotopyEquiv.refl Y)).trans (Homeomorph.uniqueProd Unit Y).toHomotopyEquiv

theorem second_injective_of_contractible (X Y : TopCat.{0}) [ContractibleSpace X] (k : ℕ) :
    Function.Injective (homologyPushZMod2 (second X Y) k).hom := by
  have he : TopCat.ofHom (contractibleProductEquiv X Y).toFun = second X Y := by ext p : 1; rfl
  have hh : ((contractibleProductEquiv X Y).singularHomologyIso coeff k).hom =
      homologyPushZMod2 (second X Y) k := by
    rw [ContinuousMap.HomotopyEquiv.singularHomologyIso_hom, he]
    rfl
  rw [← hh]
  exact ((contractibleProductEquiv X Y).singularHomologyIso coeff k).toLinearEquiv.injective

theorem detects_of_contractible (X Y : TopCat.{0}) [ContractibleSpace X] (k : ℕ) : Detects X Y k := by
  intro z _ hz
  exact second_injective_of_contractible X Y k (hz.trans (map_zero _).symm)

def fiberSection (X Y : TopCat.{0}) (x : X) : Y ⟶ product X Y :=
  TopCat.ofHom ⟨fun y => (x, y), continuous_const.prodMk continuous_id⟩

theorem fiberSection_second (X Y : TopCat.{0}) (x : X) : fiberSection X Y x ≫ second X Y = 𝟙 Y := by
  ext y : 1
  rfl

def fiberSectionHomotopy (X Y : TopCat.{0}) {x x' : X} (p : Path x x') :
    ContinuousMap.Homotopy (fiberSection X Y x).hom (fiberSection X Y x').hom where
  toFun q := (p q.1, q.2)
  continuous_toFun := (p.continuous.comp continuous_fst).prodMk continuous_snd
  map_zero_left _ := by simp [fiberSection]
  map_one_left _ := by simp [fiberSection]

theorem fiberSection_homology_eq (X Y : TopCat.{0}) {x x' : X} (h : Joined x x') (k : ℕ) :
    homologyPushZMod2 (fiberSection X Y x) k = homologyPushZMod2 (fiberSection X Y x') k :=
  TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (fiberSectionHomotopy X Y h.somePath) coeff k

end
end Finsler.ProductHomologyDetectionTransport
