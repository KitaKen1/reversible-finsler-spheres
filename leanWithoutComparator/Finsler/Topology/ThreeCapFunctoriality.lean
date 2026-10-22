module

public import Finsler.Topology.ThreeCapBlockVanishing
public import Finsler.Topology.PartialDoubleCap

/-! Naturality of the actual three successive AW caps, without any
cocycle or global zero-extension closure assumption. -/

@[expose] public section
namespace Finsler.ThreeCapFunctoriality

open CategoryTheory
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.RelativeCapAssociativity Finsler.ThreeCapBlockVanishing
open SphereOddDegree

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem natural {X Y : TopCat.{0}} (f : X ⟶ Y) (a b c d : ℕ)
    (A : singularCochainGroup (ZMod 2) Y a)
    (B : singularCochainGroup (ZMod 2) Y b)
    (C : singularCochainGroup (ZMod 2) Y c) :
    threeCap X a b c d (cochainPullback f a A) (cochainPullback f b B) (cochainPullback f c C) ≫
      (push f).f d = (push f).f (a + b + c + d) ≫ threeCap Y a b c d A B C := by
  change absoluteChain X a (b + (c + d)) (a + b + c + d) (by omega) (cochainPullback f a A) ≫
    (PartialDoubleCap.cap X b c d (cochainPullback f b B) (cochainPullback f c C) ≫ (push f).f d) =
    (push f).f (a + b + c + d) ≫
      (absoluteChain Y a (b + (c + d)) (a + b + c + d) (by omega) A ≫ PartialDoubleCap.cap Y b c d B C)
  have hA : absoluteChain X a (b + (c + d)) (a + b + c + d) (by omega) (cochainPullback f a A) ≫
      (push f).f (b + (c + d)) =
      (push f).f (a + b + c + d) ≫ absoluteChain Y a (b + (c + d)) (a + b + c + d) (by omega) A :=
    RelativeCapBoundary.absolute_chain_natural f a (b + (c + d)) (a + b + c + d) (by omega) A
  rw [PartialDoubleCap.cap_natural, ← Category.assoc, hA, Category.assoc]

end
end Finsler.ThreeCapFunctoriality
