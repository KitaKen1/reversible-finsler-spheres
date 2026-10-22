module

public import Finsler.Loop.SupportedCapCochainClass

/-! Compare the ORIGINAL ambient supported cap after a genuine family
map with the actual source-local cap, followed by the actual pulled
neighborhood cochain. Strict equality is proved on source small chains,
then the original subdivision homotopy gives equality of absolute
cochain classes. This does NOT assert a relative boundary comparison. -/
@[expose] public section
namespace Finsler.SupportedCapPullbackClass
open CategoryTheory CategoryTheory.Limits SphereOddDegree AlgebraicTopology
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1400000

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
  (hA : IsOpen A) (hB : IsOpen B) (hcX : A ∪ B = Set.univ)
  (hC : IsOpen C) (hD : IsOpen D) (hcY : C ∪ D = Set.univ)
  (hfA : Set.MapsTo f A C) (hfB : Set.MapsTo f B D) (p q : ℕ)
  (φ : singularCochainGroup (ZMod 2) Y p)
  (hs : cochainPullback (SupportedCap.subspaceMap Y C) p φ = 0)
  (hφ : cochainCoboundary (ZMod 2) Y p φ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) q)
  (hψ : cochainCoboundary (ZMod 2) (TopCat.of D) q ψ = 0)

def original : singularCochainGroup (ZMod 2) X (p + q) :=
  cochainPullback f (p + q)
    (SupportedCap.cut Y C D hC hD hcY p q (p + q) rfl φ hs ≫ ψ)

def localCochain : singularCochainGroup (ZMod 2) X (p + q) :=
  SupportedCap.cut X A B hA hB hcX p q (p + q) rfl (cochainPullback f p φ)
    (pullback_support f A C hfA p φ hs) ≫
      cochainPullback (restriction f B D hfB) q ψ

include hφ hψ in
theorem original_closed : cochainCoboundary (ZMod 2) X (p + q)
    (original f C D hC hD hcY p q φ hs ψ) = 0 := by
  have hy := DegreeLoweringCochainPullback.closed (SupportedCapHomology.operation Y C D hC hD hcY p φ hs hφ) q ψ hψ
  exact pullback_closed f (p + q) _ hy

include hφ hψ in
theorem local_closed : cochainCoboundary (ZMod 2) X (p + q)
    (localCochain f A B C D hA hB hcX hfA hfB p q φ hs ψ) = 0 :=
  DegreeLoweringCochainPullback.closed
    (SupportedCapHomology.operation X A B hA hB hcX p (cochainPullback f p φ)
      (pullback_support f A C hfA p φ hs) (pullback_closed f p φ hφ)) q _
    (pullback_closed (restriction f B D hfB) q ψ hψ)

theorem small_equality :
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫
      original f C D hC hD hcY p q φ hs ψ =
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f (p + q) ≫
      localCochain f A B C D hA hB hcX hfA hfB p q φ hs ψ := by
  have he := congrArg (fun a => a ≫ ψ)
    (SupportedCapSmallNaturality.naturality f A B C D hA hB hcX hC hD hcY hfA hfB p q φ hs)
  exact he

include hφ hψ in
theorem class_equality (hpq : 1 ≤ p + q) :
    CochainClass.classOf (cochainCxZMod2 X) (p + q)
      (original f C D hC hD hcY p q φ hs ψ)
      (original_closed f C D hC hD hcY p q φ hs hφ ψ hψ) =
    CochainClass.classOf (cochainCxZMod2 X) (p + q)
      (localCochain f A B C D hA hB hcX hfA hfB p q φ hs ψ)
      (local_closed f A B C D hA hB hcX hfA hfB p q φ hs hφ ψ hψ) :=
  SupportedCapCochainClass.class_eq_of_small (SupportedCap.cover X A B)
    (SupportedCap.cover_open X A B hA hB) (SupportedCap.cover_univ X A B hcX) (p + q) hpq _ _
    (original_closed f C D hC hD hcY p q φ hs hφ ψ hψ)
    (local_closed f A B C D hA hB hcX hfA hfB p q φ hs hφ ψ hψ)
    (small_equality f A B C D hA hB hcX hC hD hcY hfA hfB p q φ hs ψ)

end
end Finsler.SupportedCapPullbackClass
