module

public import Finsler.Topology.SmallRectangleCross
public import Finsler.Topology.FilteredBilinearLoopProduct

/-! Identify the real coefficient-multiplied small-chain cross with the
specified singular homology cross, using TauCeti's actual tensor cross
and the literal chain inclusion square. -/

@[expose] public section
namespace Finsler.SmallCrossHomologyBridge

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem ambient (X Y : TopCat.{0}) (i j n : ℕ) (h : i + j = n) :
    homologyCross (chains X) (chains Y) i j n h ≫
      homologyMap (SmallRectangleCross.ambient X Y) n =
    FilteredBilinearLoopProduct.crossMap X Y i j n h := by
  rw [SmallRectangleCross.ambient, homologyMap_comp, ← Category.assoc,
    FilteredBilinearLoopProduct.crossMap, TopCat.singularHomologyCross_def]
  rfl

variable {X Y : TopCat.{0}} {ι κ : Type*} (U : ι → Set X) (V : κ → Set Y)

theorem small_cross (i j n : ℕ) (h : i + j = n) :
    homologyCross (small X U) (small Y V) i j n h ≫
      homologyMap (SmallRectangleCross.cross U V ≫ inclusion (X ⊗ Y) (SmallRectangleShuffle.rectangles U V)) n =
    (homologyMap (inclusion X U) i ⊗ₘ homologyMap (inclusion Y V) j) ≫
      FilteredBilinearLoopProduct.crossMap X Y i j n h := by
  have hn : (homologyMap (inclusion X U) i ⊗ₘ homologyMap (inclusion Y V) j) ≫
      homologyCross (chains X) (chains Y) i j n h =
    homologyCross (small X U) (small Y V) i j n h ≫
      homologyMap (inclusion X U ⊗ₘ inclusion Y V) n :=
    homologyCross_naturality (inclusion X U) (inclusion Y V) i j n h
  rw [SmallRectangleCross.cross_inclusion, homologyMap_comp, ← Category.assoc,
    ← hn, Category.assoc, ambient]

end
end Finsler.SmallCrossHomologyBridge
