module

public import Finsler.Loop.DegreeLoweringComposition
public import Finsler.Topology.FilteredBilinearLoopProduct

/-! Evaluate an actual composite on the actual homology cross while
retaining and eliminating only the native associativity degree transport. -/

@[expose] public section
namespace Finsler.DegreeLoweringCompositionCross
open CategoryTheory MonoidalCategory AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000

theorem cross_transport (X Y : TopCat.{0}) (i j u v : ℕ) (h : i + j = u) (e : u = v)
    (x : PoolCap.homology X i) (y : PoolCap.homology Y j) :
    (eqToHom (congrArg (fun q : ℕ => (chains (X ⊗ Y)).homology q) e)).hom
      (FilteredBilinearLoopProduct.cross X Y i j u h x y) =
    FilteredBilinearLoopProduct.cross X Y i j v (h.trans e) x y := by
  subst v
  rfl

theorem value (X Y : TopCat.{0}) {D E : ChainComplex (ModuleCat.{0} (ZMod 2)) ℕ}
    {a b : ℕ} (f : DegreeLoweringHomology.Map (chains (X ⊗ Y)) D a)
    (g : DegreeLoweringHomology.Map D E b) (i j k : ℕ) (h : i + j = (a + b) + k)
    (x : PoolCap.homology X i) (y : PoolCap.homology Y j) :
    ((DegreeLoweringComposition.compose f g).homology k).hom
      (FilteredBilinearLoopProduct.cross X Y i j ((a + b) + k) h x y) =
    (g.homology k).hom ((f.homology (b + k)).hom
      (FilteredBilinearLoopProduct.cross X Y i j (a + (b + k)) (by omega) x y)) := by
  rw [DegreeLoweringComposition.homology]
  change (g.homology k).hom ((f.homology (b + k)).hom
    ((eqToHom (congrArg (fun q : ℕ => (chains (X ⊗ Y)).homology q) (Nat.add_assoc a b k))).hom
      (FilteredBilinearLoopProduct.cross X Y i j ((a + b) + k) h x y))) = _
  rw [cross_transport X Y i j ((a + b) + k) (a + (b + k)) h (Nat.add_assoc a b k) x y]

end
end Finsler.DegreeLoweringCompositionCross
