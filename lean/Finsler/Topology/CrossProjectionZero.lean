module

public import Finsler.Topology.FilteredBilinearLoopProduct
public import TauCeti.AlgebraicTopology.Singular.Contractible

/-! Positive degree in the first factor makes the actual external product
vanish under projection to the second factor. The proof uses actual cross
naturality and the positive homology of a point, without a Kunneth premise. -/

@[expose] public section

namespace Finsler.CrossProjectionZero

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open AlgebraicTopology SphereOddDegree Finsler.CochainComparison

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem cross_naturality {X Y X' Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p q m : ℕ) (h : p + q = m) :
    (PoolCap.push f p ⊗ₘ PoolCap.push g q) ≫ FilteredBilinearLoopProduct.crossMap X' Y' p q m h =
      FilteredBilinearLoopProduct.crossMap X Y p q m h ≫ PoolCap.push (f ⊗ₘ g) m := by
  let μ := (singularHomologyFunctor (ModuleCat (ZMod 2)) m).map (λ_ coeff).hom
  calc
    _ = TopCat.singularHomologyCross X Y coeff coeff p q m h ≫
        ((((singularHomologyFunctor (ModuleCat (ZMod 2)) m).obj (coeff ⊗ coeff)).map (f ⊗ₘ g)) ≫
          μ.app (X' ⊗ Y')) := by
      change (PoolCap.push f p ⊗ₘ PoolCap.push g q) ≫
        (TopCat.singularHomologyCross X' Y' coeff coeff p q m h ≫ μ.app (X' ⊗ Y')) = _
      rw [← Category.assoc, TopCat.singularHomologyCross_naturality, Category.assoc]
    _ = TopCat.singularHomologyCross X Y coeff coeff p q m h ≫
        (μ.app (X ⊗ Y) ≫ PoolCap.push (f ⊗ₘ g) m) :=
      congrArg (TopCat.singularHomologyCross X Y coeff coeff p q m h ≫ ·) (μ.naturality (f ⊗ₘ g))
    _ = _ := (Category.assoc _ _ _).symm

theorem cross_naturality_apply {X Y X' Y' : TopCat.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    (p q m : ℕ) (h : p + q = m) (x : PoolCap.homology X p) (y : PoolCap.homology Y q) :
    FilteredBilinearLoopProduct.cross X' Y' p q m h ((PoolCap.push f p).hom x) ((PoolCap.push g q).hom y) =
      (PoolCap.push (f ⊗ₘ g) m).hom (FilteredBilinearLoopProduct.cross X Y p q m h x y) := by
  have he := ConcreteCategory.congr_hom (cross_naturality f g p q m h) (x ⊗ₜ[ZMod 2] y)
  change (FilteredBilinearLoopProduct.crossMap X' Y' p q m h).hom
    ((PoolCap.push f p ⊗ₘ PoolCap.push g q) (x ⊗ₜ[ZMod 2] y)) = _ at he
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul] at he
  exact he

theorem projection_zero (X Y : TopCat.{0}) (p q : ℕ) (hp : p ≠ 0)
    (x : PoolCap.homology X p) (y : PoolCap.homology Y q) :
    (PoolCap.push (snd X Y) (p + q)).hom
      (FilteredBilinearLoopProduct.cross X Y p q (p + q) rfl x y) = 0 := by
  let pt : TopCat.{0} := TopCat.of PUnit
  let f : X ⟶ pt := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  have hz : IsZero (PoolCap.homology pt p) :=
    TauCeti.isZero_singularHomologyFunctor_of_contractibleSpace coeff pt hp
  letI : Subsingleton (PoolCap.homology pt p) := ModuleCat.isZero_iff_subsingleton.mp hz
  have hzero : (PoolCap.push f p).hom x = 0 := Subsingleton.elim _ _
  have hproj : (f ⊗ₘ 𝟙 Y) ≫ snd pt Y = snd X Y := by
    ext z : 1
    rfl
  have hmap : PoolCap.push (snd X Y) (p + q) =
      PoolCap.push (f ⊗ₘ 𝟙 Y) (p + q) ≫ PoolCap.push (snd pt Y) (p + q) :=
    (congrArg (fun m => PoolCap.push m (p + q)) hproj).symm.trans
      (((singularHomologyFunctor (ModuleCat (ZMod 2)) (p + q)).obj coeff).map_comp _ _)
  calc
    _ = (PoolCap.push (snd pt Y) (p + q)).hom
        ((PoolCap.push (f ⊗ₘ 𝟙 Y) (p + q)).hom
          (FilteredBilinearLoopProduct.cross X Y p q (p + q) rfl x y)) :=
      ConcreteCategory.congr_hom hmap _
    _ = (PoolCap.push (snd pt Y) (p + q)).hom
        (FilteredBilinearLoopProduct.cross pt Y p q (p + q) rfl
          ((PoolCap.push f p).hom x) ((PoolCap.push (𝟙 Y) q).hom y)) :=
      congrArg (PoolCap.push (snd pt Y) (p + q)).hom
        (cross_naturality_apply f (𝟙 Y) p q (p + q) rfl x y).symm
    _ = 0 := by rw [hzero, map_zero, LinearMap.zero_apply, map_zero]

theorem projection_cap_zero (X Y : TopCat.{0}) (p q : ℕ) (hp : p ≠ 0)
    (a : cohomologyZMod2 Y p) (x : PoolCap.homology X p) (y : PoolCap.homology Y q) :
    (PoolCap.push (snd X Y) q).hom
      (PoolCap.cap (X ⊗ Y) p q (p + q) rfl ((cohPullback (snd X Y) p).hom a)
        (FilteredBilinearLoopProduct.cross X Y p q (p + q) rfl x y)) = 0 := by
  rw [PoolCap.naturality, projection_zero X Y p q hp x y, map_zero]


end
end Finsler.CrossProjectionZero
