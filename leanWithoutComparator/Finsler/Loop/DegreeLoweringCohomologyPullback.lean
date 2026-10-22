module

public import Finsler.Loop.DegreeLoweringCochainPullback

/-! The actual cochain pullback descends to a linear cohomology map.
The Lean Pool universal-coefficient isomorphism supplies the bundled
map; its equality with actual pulled cocycle classes is proved. -/

@[expose] public section
namespace Finsler.DegreeLoweringCohomologyPullback
open CategoryTheory AlgebraicTopology SphereOddDegree
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 700000

variable {X Y : TopCat.{0}} {d : ℕ}
  (f : DegreeLoweringHomology.Map (chainCxZMod2 X) (chainCxZMod2 Y) d) (q : ℕ)

def map : cohomologyZMod2 Y q →ₗ[ZMod 2] cohomologyZMod2 X (d + q) :=
  (kroneckerEquiv X (d + q)).inv.hom.comp
    ((LinearMap.lcomp (ZMod 2) (ZMod 2) (f.homology q).hom).comp (kroneckerMap Y q).hom)

theorem pairing (a : cohomologyZMod2 Y q) (z : homologyZMod2 X (d + q)) :
    (kroneckerMap X (d + q)).hom (map f q a) z =
      (kroneckerMap Y q).hom a ((f.homology q).hom z) := by
  have h := ConcreteCategory.congr_hom (Iso.inv_hom_id (kroneckerEquiv X (d + q)))
    (((kroneckerMap Y q).hom a).comp (f.homology q).hom)
  exact congrArg (fun v : homologyDualZMod2 X (d + q) => v z) h

theorem map_cocycle (B : singularCochainGroup (ZMod 2) Y q)
    (hB : cochainCoboundary (ZMod 2) Y q B = 0) :
    map f q (cocycleClass Y q B hB) =
      cocycleClass X (d + q) (DegreeLoweringCochainPullback.cochain f q B)
        (DegreeLoweringCochainPullback.closed f q B hB) := by
  apply kroneckerMap_injective
  apply LinearMap.ext
  intro z
  rw [pairing, DegreeLoweringCochainPullback.pairing]

theorem map_eq_of_homology_eq
    (g : DegreeLoweringHomology.Map (chainCxZMod2 X) (chainCxZMod2 Y) d)
    (h : f.homology q = g.homology q) : map f q = map g q := by
  unfold map
  rw [h]

end
end Finsler.DegreeLoweringCohomologyPullback
