module

public import Finsler.Loop.ProductMayerVietorisCover

/-! The actual connecting class in a product cover is killed by
the second projection. If the first projection also kills the original
class, lower-degree projection detection kills that connecting class. -/
@[expose] public section
namespace Finsler.ProductMayerVietorisKernel
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.ProductHomologyZeroDetection
open Finsler.ProductMayerVietorisCover
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

theorem overlap_zero {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) (k : ℕ)
    (hd : Detects (TopCat.of (U ∩ V : Set X)) Y k)
    (z : homologyZMod2 (overlap U V Y) k)
    (h₁ : (homologyPushZMod2 (overlapFirst U V Y) k).hom z = 0)
    (h₂ : (homologyPushZMod2 (overlapSecond U V Y) k).hom z = 0) : z = 0 := by
  let e := (((singularHomologyFunctor (ModuleCat.{0} (ZMod 2)) k).obj coeff).mapIso
    (TopCat.isoOfHomeo (overlapHomeomorph U V Y))).toLinearEquiv
  have hz : e z = 0 := by
    apply hd
    · change (homologyPushZMod2 (first _ Y) k).hom
        ((homologyPushZMod2 (TopCat.isoOfHomeo (overlapHomeomorph U V Y)).hom k).hom z) = 0
      rw [SplitPairHomologyKernel.push_comp_apply, overlap_first_factor]
      exact h₁
    · change (homologyPushZMod2 (second _ Y) k).hom
        ((homologyPushZMod2 (TopCat.isoOfHomeo (overlapHomeomorph U V Y)).hom k).hom z) = 0
      rw [SplitPairHomologyKernel.push_comp_apply, overlap_second_factor]
      exact h₂
  exact e.injective (hz.trans (map_zero _).symm)

theorem north_zero_of_toPatches_zero {X : TopCat.{0}} (U V : Set X) (Y : TopCat.{0}) (k : ℕ)
    (z : homologyZMod2 (overlap U V Y) k) (hz : (toPatches U V Y k).hom z = 0) :
    (homologyPushZMod2 (north U V Y) k).hom z = 0 := by
  have hf : toPatches U V Y k ≫ biprod.fst = homologyPushZMod2 (north U V Y) k :=
    SSet.mayerVietorisToBiprod_fst coeff _ _ k
  have he := ConcreteCategory.congr_hom hf z
  change (biprod.fst : patches U V Y k ⟶ homologyZMod2 (patch U Y) k).hom
    ((toPatches U V Y k).hom z) = _ at he
  rw [hz, map_zero] at he
  exact he.symm

theorem delta_second_zero {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ)
    (z : homologyZMod2 (product X Y) (k + 1)) :
    (homologyPushZMod2 (overlapSecond U V Y) k).hom ((delta Y hU hV hUV k).hom z) = 0 := by
  have ht : (toPatches U V Y k).hom ((delta Y hU hV hUV k).hom z) = 0 :=
    (ConcreteCategory.congr_hom (delta_toPatches Y hU hV hUV k) z).trans rfl
  rw [← north_second U V Y, ← SplitPairHomologyKernel.push_comp_apply,
    north_zero_of_toPatches_zero U V Y k _ ht, map_zero]

theorem delta_first_zero {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ)
    (z : homologyZMod2 (product X Y) (k + 1))
    (hz : (homologyPushZMod2 (first X Y) (k + 1)).hom z = 0) :
    (homologyPushZMod2 (overlapFirst U V Y) k).hom ((delta Y hU hV hUV k).hom z) = 0 := by
  have he := ConcreteCategory.congr_hom (first_naturality Y hU hV hUV k) z
  change (homologyPushZMod2 (overlapFirst U V Y) k).hom ((delta Y hU hV hUV k).hom z) =
    (TopCat.mayerVietorisδ (X := X) coeff hU hV hUV (k + 1) k rfl).hom
      ((homologyPushZMod2 (first X Y) (k + 1)).hom z) at he
  rw [hz, map_zero] at he
  exact he

theorem delta_zero {X : TopCat.{0}} {U V : Set X} (Y : TopCat.{0})
    (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (k : ℕ)
    (hd : Detects (TopCat.of (U ∩ V : Set X)) Y k)
    (z : homologyZMod2 (product X Y) (k + 1))
    (hz : (homologyPushZMod2 (first X Y) (k + 1)).hom z = 0) :
    (delta Y hU hV hUV k).hom z = 0 :=
  overlap_zero U V Y k hd _ (delta_first_zero Y hU hV hUV k z hz)
    (delta_second_zero Y hU hV hUV k z)

end
end Finsler.ProductMayerVietorisKernel
