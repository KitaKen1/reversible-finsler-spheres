module

public import Finsler.Loop.SupportedRightTestLocal
public import Finsler.Loop.SupportedCapTestOrder

/-! One actual subdivision prism moves a RIGHT scalar evaluation
through the supported cap. Its restriction is literally zero wherever
the actual Thom factor or the actual near-output test is zero. -/
@[expose] public section
namespace Finsler.SupportedRightTestOrder
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.SupportedRightTestLocal
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (a b q : ℕ)
  (α : singularCochainGroup (ZMod 2) X a) (θ : singularCochainGroup (ZMod 2) X (b + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (b + 1) θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q)

def primitive : singularCochainGroup (ZMod 2) X ((b + q) + a) :=
  SupportedSmallCochainComparison.primitive (SupportedCap.cover X A B) ((b + q) + a)
    (difference X A B hA hB hc a b q α θ hs ψ)

theorem before_closed (hα : cochainCoboundary (ZMod 2) X a α = 0)
    (hθ : cochainCoboundary (ZMod 2) X (b + 1) θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (before X A B hA hB hc a b q α θ hs ψ) = 0 :=
  CupCapOrder.closed X ((b + 1) + q) a _ (by omega) _ α
    (SupportedCapTestOrderCoupling.supported_closed X A B hA hB hc (b + 1) q _ rfl θ hs hθ ψ hψ) hα

theorem after_closed (hα : cochainCoboundary (ZMod 2) X a α = 0)
    (hθ : cochainCoboundary (ZMod 2) X (b + 1) θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (after X A B hA hB hc a b q α θ hs ψ) = 0 :=
  SupportedCapTestOrderCoupling.supported_closed X A B hA hB hc (b + 1) (q + a) _ (by omega) θ hs hθ _
    (CupCapOrder.closed (TopCat.of B) q a (q + a) rfl ψ _ hψ (pullback_closed _ a α hα))

theorem difference_closed (hα : cochainCoboundary (ZMod 2) X a α = 0)
    (hθ : cochainCoboundary (ZMod 2) X (b + 1) θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (difference X A B hA hB hc a b q α θ hs ψ) = 0 := by
  change ((cochainCxZMod2 X).d _ _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((before_closed X A B hA hB hc a b q α θ hs ψ hα hθ hψ).trans
    (after_closed X A B hA hB hc a b q α θ hs ψ hα hθ hψ).symm)

theorem boundary (hα : cochainCoboundary (ZMod 2) X a α = 0)
    (hθ : cochainCoboundary (ZMod 2) X (b + 1) θ = 0)
    (hψ : cochainCoboundary (ZMod 2) (TopCat.of B) q ψ = 0) :
    cochainCoboundary (ZMod 2) X _ (primitive X A B hA hB hc a b q α θ hs ψ) =
      before X A B hA hB hc a b q α θ hs ψ - after X A B hA hB hc a b q α θ hs ψ :=
  SupportedSmallCochainComparison.primitive_boundary (SupportedCap.cover X A B)
    (SupportedCap.cover_open X A B hA hB) (SupportedCap.cover_univ X A B hc) ((b + q) + a) _
    (difference_closed X A B hA hB hc a b q α θ hs ψ hα hθ hψ)
    (small_equal X A B hA hB hc a b q α θ hs ψ)

theorem primitive_thom_zero (S : Set X)
    (hS : cochainPullback (SupportedCap.subspaceMap X S) (b + 1) θ = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) _ (primitive X A B hA hB hc a b q α θ hs ψ) = 0 := by
  apply SupportedSmallCochainComparison.primitive_support_zero
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((before_thom_zero X A B hA hB hc a b q α θ hs ψ S hS).trans
    (after_thom_zero X A B hA hB hc a b q α θ hs ψ S hS).symm)

variable (S : Set X)
  (hS : cochainPullback (restriction (SupportedCap.subspaceMap X S)
    ((SupportedCap.subspaceMap X S) ⁻¹' B) B (fun _ h => h)) q ψ = 0)

include hS in
theorem before_test_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (before X A B hA hB hc a b q α θ hs ψ) = 0 :=
  CupCapOrder.restriction_zero (SupportedCap.subspaceMap X S) ((b + 1) + q) a _ (by omega) _ α
    (Or.inl (SupportedCapTestOrder.cut_carrier_zero_at_degree X A B S hA hB hc (b + 1) q _ rfl θ hs ψ hS))

include hS in
theorem after_test_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (after X A B hA hB hc a b q α θ hs ψ) = 0 :=
  SupportedCapTestOrder.cut_carrier_zero_at_degree X A B S hA hB hc (b + 1) (q + a) _ (by omega) θ hs _
    (CupCapOrder.restriction_zero (restriction (SupportedCap.subspaceMap X S)
      ((SupportedCap.subspaceMap X S) ⁻¹' B) B (fun _ h => h)) q a (q + a) rfl ψ _ (Or.inl hS))

include hS in
theorem primitive_test_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (primitive X A B hA hB hc a b q α θ hs ψ) = 0 := by
  apply SupportedSmallCochainComparison.primitive_support_zero
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((before_test_zero X A B hA hB hc a b q α θ hs ψ S hS).trans
    (after_test_zero X A B hA hB hc a b q α θ hs ψ S hS).symm)

end
end Finsler.SupportedRightTestOrder
