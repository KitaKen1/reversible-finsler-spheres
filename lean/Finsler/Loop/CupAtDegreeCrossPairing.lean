module

public import Finsler.Loop.CupAtDegree
public import Finsler.Topology.CrossCupPairing

/-! Evaluate actual projection-cups on the EXISTING specified-degree
crosses and transfer through an actual continuous map. -/
@[expose] public section
namespace Finsler.CupAtDegreeCrossPairing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SphereOddDegree
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem cross_cup_apply (X Y : TopCat.{0}) (p q N : ℕ) (h : p + q = N)
    (a : cohomologyZMod2 X p) (b : cohomologyZMod2 Y q)
    (x : PoolCap.homology X p) (y : PoolCap.homology Y q) :
    (kroneckerMap (X ⊗ Y) N).hom
      (CupAtDegree.cup (X ⊗ Y) p q N h ((cohPullback (fst X Y) p).hom a) ((cohPullback (snd X Y) q).hom b))
      (FilteredBilinearLoopProduct.cross X Y p q N h x y) =
      (kroneckerMap X p).hom a x * (kroneckerMap Y q).hom b y := by
  subst N
  exact CrossCupPairing.cross_cup_apply X Y p q a b x y

theorem pairing_push {X Y : TopCat.{0}} (f : X ⟶ Y) (N : ℕ)
    (a : cohomologyZMod2 Y N) (x : PoolCap.homology X N) :
    (kroneckerMap Y N).hom a ((homologyPushZMod2 f N).hom x) =
      (kroneckerMap X N).hom ((cohPullback f N).hom a) x :=
  (congrArg (fun g => g x) (kroneckerMap_naturality_apply f N a)).symm

end
end Finsler.CupAtDegreeCrossPairing
