module

public import Finsler.Loop.SmallChainPrimitiveCorrection
public import Finsler.Topology.CarrierCochainZero
public import Finsler.Topology.TubeExtensionPullback

/-! Globalize an actual local primitive by zero extension and the
actual subdivision prism. The exterior is an OPEN cover component;
its overlap with the patch has literal primitive zero. Every separate
carrier zero is preserved, without a zero-on-union premise. -/
@[expose] public section
namespace Finsler.PatchCochainPrimitive
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

private theorem pullback_sub {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ)
    (a b : singularCochainGroup (ZMod 2) Y n) :
    cochainPullback f n (a - b) = cochainPullback f n a - cochainPullback f n b :=
  map_sub ((singularCochainComplexZMod2.map f.op).f n).hom a b

variable (X : TopCat.{0}) (U V : Set X) (n : ℕ)
  (Φ : singularCochainGroup (ZMod 2) X (n + 1))
  (κ : singularCochainGroup (ZMod 2) (TopCat.of U) n)

def overlapMap (C : Set X) : TopCat.of ((SupportedCap.subspaceMap X C) ⁻¹' U) ⟶ TopCat.of U :=
  restriction (SupportedCap.subspaceMap X C) ((SupportedCap.subspaceMap X C) ⁻¹' U) U (fun _ h => h)

def extension : singularCochainGroup (ZMod 2) X n := TubeCochainExtension.extend X U n κ

theorem extension_restriction : cochainPullback (SupportedCap.subspaceMap X U) n (extension X U n κ) = κ :=
  TubeCochainExtension.restriction X U n κ

theorem extension_carrier_zero (C : Set X)
    (hκ : cochainPullback (overlapMap X U C) n κ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) n (extension X U n κ) = 0 :=
  TubeExtensionPullback.pullback_zero (SupportedCap.subspaceMap X C) U n κ hκ

theorem small_equality
    (hκ : cochainCoboundary (ZMod 2) (TopCat.of U) n κ = cochainPullback (SupportedCap.subspaceMap X U) (n + 1) Φ)
    (hΦV : cochainPullback (SupportedCap.subspaceMap X V) (n + 1) Φ = 0)
    (hκV : cochainPullback (overlapMap X U V) n κ = 0) :
    (SmallChainCarrier.inclusion X (SupportedCap.cover X U V)).f (n + 1) ≫ Φ =
      (SmallChainCarrier.inclusion X (SupportedCap.cover X U V)).f (n + 1) ≫
        cochainCoboundary (ZMod 2) X n (extension X U n κ) := by
  have hz := CarrierCochainZero.small_zero (SupportedCap.cover X U V) (n + 1)
    (SmallChainPrimitiveCorrection.difference n Φ (extension X U n κ)) (by
      intro i
      cases i
      · have he := SmallChainPrimitiveCorrection.pullback_boundary (SupportedCap.subspaceMap X U) n (n + 1) (extension X U n κ)
        change cochainCoboundary (ZMod 2) (TopCat.of U) n (cochainPullback (SupportedCap.subspaceMap X U) n (extension X U n κ)) =
          cochainPullback (SupportedCap.subspaceMap X U) (n + 1) (cochainCoboundary (ZMod 2) X n (extension X U n κ)) at he
        rw [extension_restriction, hκ] at he
        change cochainPullback (SupportedCap.subspaceMap X U) (n + 1)
          (Φ - cochainCoboundary (ZMod 2) X n (extension X U n κ)) = 0
        rw [pullback_sub, he, sub_self]
      · apply SmallChainPrimitiveCorrection.difference_support_zero n Φ (extension X U n κ) V hΦV
        exact extension_carrier_zero X U n κ V hκV)
  change (SmallChainCarrier.inclusion X (SupportedCap.cover X U V)).f (n + 1) ≫
    (Φ - cochainCoboundary (ZMod 2) X n (extension X U n κ)) = 0 at hz
  rw [Preadditive.comp_sub] at hz
  exact sub_eq_zero.mp hz

def primitive : singularCochainGroup (ZMod 2) X n :=
  SmallChainPrimitiveCorrection.primitive (SupportedCap.cover X U V) n Φ (extension X U n κ)

theorem primitive_boundary (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = Set.univ)
    (hΦ : cochainCoboundary (ZMod 2) X (n + 1) Φ = 0)
    (hκ : cochainCoboundary (ZMod 2) (TopCat.of U) n κ = cochainPullback (SupportedCap.subspaceMap X U) (n + 1) Φ)
    (hΦV : cochainPullback (SupportedCap.subspaceMap X V) (n + 1) Φ = 0)
    (hκV : cochainPullback (overlapMap X U V) n κ = 0) :
    cochainCoboundary (ZMod 2) X n (primitive X U V n Φ κ) = Φ :=
  SmallChainPrimitiveCorrection.primitive_boundary (SupportedCap.cover X U V) n Φ (extension X U n κ)
    (SupportedCap.cover_open X U V hU hV) (SupportedCap.cover_univ X U V hc) hΦ
    (small_equality X U V n Φ κ hκ hΦV hκV)

theorem primitive_carrier_zero (C : Set X)
    (hΦC : cochainPullback (SupportedCap.subspaceMap X C) (n + 1) Φ = 0)
    (hκC : cochainPullback (overlapMap X U C) n κ = 0) :
    cochainPullback (SupportedCap.subspaceMap X C) n (primitive X U V n Φ κ) = 0 :=
  SmallChainPrimitiveCorrection.primitive_support_zero (SupportedCap.cover X U V) n Φ (extension X U n κ) C hΦC
    (extension_carrier_zero X U n κ C hκC)

end
end Finsler.PatchCochainPrimitive
