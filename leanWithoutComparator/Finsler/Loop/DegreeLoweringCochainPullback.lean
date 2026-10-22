module

public import Finsler.Topology.DegreeLoweringHomology
public import Finsler.Topology.Kronecker

/-! Actual cochain precomposition by a closed degree-lowering operation,
with closure and the genuine Lean Pool Kronecker pairing. -/

@[expose] public section
namespace Finsler.DegreeLoweringCochainPullback
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {X Y : TopCat.{0}} {d : ℕ}
  (f : DegreeLoweringHomology.Map (chainCxZMod2 X) (chainCxZMod2 Y) d)
  (q : ℕ) (B : singularCochainGroup (ZMod 2) Y q)

def cochain : singularCochainGroup (ZMod 2) X (d + q) := f.component q ≫ B

theorem closed (hB : cochainCoboundary (ZMod 2) Y q B = 0) :
    cochainCoboundary (ZMod 2) X (d + q) (cochain f q B) = 0 := by
  change (chainCxZMod2 X).d (d + (q + 1)) (d + q) ≫ (f.component q ≫ B) = 0
  rw [← Category.assoc, ← f.comm q, Category.assoc]
  change f.component (q + 1) ≫ cochainCoboundary (ZMod 2) Y q B = 0
  rw [hB, comp_zero]

theorem functional (hB : cochainCoboundary (ZMod 2) Y q B = 0) :
    kroneckerFunctional X (d + q) (cochain f q B) (closed f q B hB) =
      f.homology q ≫ kroneckerFunctional Y q B hB := by
  apply (cancel_epi ((chainCxZMod2 X).homologyπ (d + q))).mp
  rw [kroneckerFunctional_homologyπ, ← Category.assoc, f.homologyπ_homology,
    Category.assoc, kroneckerFunctional_homologyπ, ← Category.assoc, f.cycles_i, Category.assoc]
  rfl

theorem pairing (hB : cochainCoboundary (ZMod 2) Y q B = 0) (z : homologyZMod2 X (d + q)) :
    (kroneckerMap X (d + q)).hom
      (cocycleClass X (d + q) (cochain f q B) (closed f q B hB)) z =
    (kroneckerMap Y q).hom (cocycleClass Y q B hB) ((f.homology q).hom z) := by
  rw [kroneckerMap_cocycleClass, kroneckerMap_cocycleClass]
  exact ConcreteCategory.congr_hom (functional f q B hB) z

theorem class_eq_of_class_eq (B' : singularCochainGroup (ZMod 2) Y q)
    (hB : cochainCoboundary (ZMod 2) Y q B = 0)
    (hB' : cochainCoboundary (ZMod 2) Y q B' = 0)
    (hclass : cocycleClass Y q B hB = cocycleClass Y q B' hB') :
    cocycleClass X (d + q) (cochain f q B) (closed f q B hB) =
      cocycleClass X (d + q) (cochain f q B') (closed f q B' hB') := by
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  rw [pairing f q B hB z, pairing f q B' hB' z, hclass]

end
end Finsler.DegreeLoweringCochainPullback
