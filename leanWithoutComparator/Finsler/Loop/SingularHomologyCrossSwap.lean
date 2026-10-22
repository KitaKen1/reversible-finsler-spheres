module

public import Finsler.Loop.F2TensorHomologySwap
public import Finsler.Loop.SingularShuffleSwap
public import Finsler.Loop.SmallCrossHomologyBridge

/-! Symmetry of the actual specified coefficient-multiplied singular
homology cross, derived from actual cycles and shuffle homotopies. -/

@[expose] public section
namespace Finsler.SingularHomologyCrossSwap
open CategoryTheory MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

theorem map_eq (X Y : TopCat.{0}) (i j k : ℕ) (h : i + j = k) :
    FilteredBilinearLoopProduct.crossMap X Y i j k h ≫ PoolCap.push (β_ X Y).hom k =
      (β_ (PoolCap.homology X i) (PoolCap.homology Y j)).hom ≫
        FilteredBilinearLoopProduct.crossMap Y X j i k (by omega) := by
  change FilteredBilinearLoopProduct.crossMap X Y i j k h ≫ homologyMap (push (β_ X Y).hom) k = _
  rw [← SmallCrossHomologyBridge.ambient, ← SmallCrossHomologyBridge.ambient,
    Category.assoc, ← SingularShuffleSwap.ambient_homology,
    ← Category.assoc, F2TensorHomologySwap.homology, Category.assoc]
  rfl

theorem value (X Y : TopCat.{0}) (i j k : ℕ) (h : i + j = k)
    (x : PoolCap.homology X i) (y : PoolCap.homology Y j) :
    (PoolCap.push (β_ X Y).hom k).hom (FilteredBilinearLoopProduct.cross X Y i j k h x y) =
      FilteredBilinearLoopProduct.cross Y X j i k (by omega) y x := by
  have he := ConcreteCategory.congr_hom (map_eq X Y i j k h) (x ⊗ₜ[ZMod 2] y)
  change (PoolCap.push (β_ X Y).hom k).hom
      ((FilteredBilinearLoopProduct.crossMap X Y i j k h).hom (x ⊗ₜ[ZMod 2] y)) =
    (FilteredBilinearLoopProduct.crossMap Y X j i k (by omega)).hom
      ((β_ (PoolCap.homology X i) (PoolCap.homology Y j)).hom (x ⊗ₜ[ZMod 2] y)) at he
  rw [ModuleCat.MonoidalCategory.braiding_hom_apply] at he
  exact he

end
end Finsler.SingularHomologyCrossSwap
