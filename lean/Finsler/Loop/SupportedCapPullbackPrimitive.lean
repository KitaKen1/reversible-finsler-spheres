module

public import Finsler.Loop.SupportedCapPullbackClass
public import Finsler.Loop.SupportedSmallCochainComparison

/-! The original small-chain equality gives an explicit scalar primitive
for the actual supported-cap pullback comparison, at arbitrary source
degrees. The SAME subdivision primitive preserves every carrier on which
both compared values vanish. No naturality of a chosen retraction. -/
@[expose] public section
namespace Finsler.SupportedCapPullbackPrimitive
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
  (hA : IsOpen A) (hB : IsOpen B) (hcX : A ∪ B = Set.univ)
  (hC : IsOpen C) (hD : IsOpen D) (hcY : C ∪ D = Set.univ)
  (hfA : Set.MapsTo f A C) (hfB : Set.MapsTo f B D) (p q N : ℕ) (hN : p + q = N)
  (θ : singularCochainGroup (ZMod 2) Y p)
  (hs : cochainPullback (SupportedCap.subspaceMap Y C) p θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of D) q)

def original : singularCochainGroup (ZMod 2) X N :=
  cochainPullback f N (SupportedCap.cut Y C D hC hD hcY p q N hN θ hs ≫ ψ)

def localValue : singularCochainGroup (ZMod 2) X N :=
  SupportedCap.cut X A B hA hB hcX p q N hN (cochainPullback f p θ)
    (pullback_support f A C hfA p θ hs) ≫ cochainPullback (restriction f B D hfB) q ψ

theorem small_equality :
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f N ≫
      localValue f A B C D hA hB hcX hfA hfB p q N hN θ hs ψ =
    (SmallChainCarrier.inclusion X (SupportedCap.cover X A B)).f N ≫
      original f C D hC hD hcY p q N hN θ hs ψ := by
  subst N
  exact (SupportedCapPullbackClass.small_equality f A B C D hA hB hcX hC hD hcY hfA hfB p q θ hs ψ).symm

theorem local_closed (hθ : cochainCoboundary (ZMod 2) Y p θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of D) q ψ = 0) :
    cochainCoboundary (ZMod 2) X N (localValue f A B C D hA hB hcX hfA hfB p q N hN θ hs ψ) = 0 := by
  subst N
  exact SupportedCapPullbackClass.local_closed f A B C D hA hB hcX hfA hfB p q θ hs hθ ψ hψ

theorem original_closed (hθ : cochainCoboundary (ZMod 2) Y p θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of D) q ψ = 0) :
    cochainCoboundary (ZMod 2) X N (original f C D hC hD hcY p q N hN θ hs ψ) = 0 := by
  subst N
  exact SupportedCapPullbackClass.original_closed f C D hC hD hcY p q θ hs hθ ψ hψ

variable (n : ℕ) (hn : p + q = n + 1)

def primitive : singularCochainGroup (ZMod 2) X n :=
  SupportedSmallCochainComparison.primitive (SupportedCap.cover X A B) n
    (localValue f A B C D hA hB hcX hfA hfB p q (n + 1) hn θ hs ψ -
      original f C D hC hD hcY p q (n + 1) hn θ hs ψ)

theorem boundary (hθ : cochainCoboundary (ZMod 2) Y p θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of D) q ψ = 0) :
    cochainCoboundary (ZMod 2) X n
      (primitive f A B C D hA hB hcX hC hD hcY hfA hfB p q θ hs ψ n hn) =
    localValue f A B C D hA hB hcX hfA hfB p q (n + 1) hn θ hs ψ -
      original f C D hC hD hcY p q (n + 1) hn θ hs ψ := by
  apply SupportedSmallCochainComparison.primitive_boundary _
    (SupportedCap.cover_open X A B hA hB) (SupportedCap.cover_univ X A B hcX)
  · change ((cochainCxZMod2 X).d _ _).hom (_ - _) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ((local_closed f A B C D hA hB hcX hfA hfB p q _ hn θ hs ψ hθ hψ).trans
      (original_closed f C D hC hD hcY p q _ hn θ hs ψ hθ hψ).symm)
  · rw [Preadditive.comp_sub, small_equality f A B C D hA hB hcX hC hD hcY hfA hfB p q _ hn θ hs ψ, sub_self]

theorem primitive_carrier_zero (S : Set X)
    (hl : cochainPullback (SupportedCap.subspaceMap X S) (n + 1)
      (localValue f A B C D hA hB hcX hfA hfB p q (n + 1) hn θ hs ψ) = 0)
    (hr : cochainPullback (SupportedCap.subspaceMap X S) (n + 1)
      (original f C D hC hD hcY p q (n + 1) hn θ hs ψ) = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) n
      (primitive f A B C D hA hB hcX hC hD hcY hfA hfB p q θ hs ψ n hn) = 0 := by
  apply SupportedSmallCochainComparison.primitive_support_zero
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (hl.trans hr.symm)

theorem cycle_values_eq (hθ : cochainCoboundary (ZMod 2) Y p θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of D) q ψ = 0)
    (c : coeff ⟶ (chains X).X (n + 1)) (hc : c ≫ (chains X).d (n + 1) n = 0) :
    c ≫ localValue f A B C D hA hB hcX hfA hfB p q (n + 1) hn θ hs ψ =
      c ≫ original f C D hC hD hcY p q (n + 1) hn θ hs ψ := by
  apply sub_eq_zero.mp
  rw [← Preadditive.comp_sub, ← boundary f A B C D hA hB hcX hC hD hcY hfA hfB p q θ hs ψ n hn hθ hψ]
  change c ≫ ((chains X).d (n + 1) n ≫ _) = 0
  rw [← Category.assoc, hc, zero_comp]

end
end Finsler.SupportedCapPullbackPrimitive
