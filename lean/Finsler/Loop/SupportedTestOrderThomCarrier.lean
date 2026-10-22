module

public import Finsler.Loop.SupportedCapTestOrder
public import Finsler.Loop.SupportedThomCarrierZero

/-! The SAME test/Thom commutation primitive vanishes wherever the
actual Thom factor vanishes. Both the actual subdivision correction
and cup-one cap retain this carrier, without a near-test hypothesis. -/
@[expose] public section
namespace Finsler.SupportedTestOrderThomCarrier
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
  (hc : A ∪ B = Set.univ) (a b q : ℕ)
  (α : singularCochainGroup (ZMod 2) X a) (θ : singularCochainGroup (ZMod 2) X (b + 1))
  (hs : cochainPullback (SupportedCap.subspaceMap X A) (b + 1) θ = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of B) q) (S : Set X)
  (hS : cochainPullback (SupportedCap.subspaceMap X S) (b + 1) θ = 0)

include hS in
theorem before_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (SupportedCapTestOrderCoupling.before X A B hA hB hc a b q α θ hs ψ) = 0 := by
  have hz := congrArg (fun c => c ≫ ψ)
    (SupportedThomCarrierZero.cut_map_zero A B S hA hB hc (b + 1) q ((b + 1) + q) rfl
      θ hs hS (SupportedCap.subspaceMap X S) (fun z => z.property))
  simp only [Category.assoc, zero_comp] at hz
  exact SupportedCapTestOrder.absolute_pullback_zero X (SupportedCap.subspaceMap X S)
    a ((b + 1) + q) ((a + b) + q + 1) (by omega) α _ hz

include hS in
theorem coupled_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (SupportedCapTestOrderCoupling.beforeCoupled X A B hA hB hc a b q α θ hs ψ) = 0 := by
  have hz := congrArg (fun c => c ≫ ψ)
    (SupportedThomCarrierZero.cut_map_zero A B S hA hB hc (a + (b + 1)) q ((a + b) + q + 1) (by omega)
      (CupOne.cup X a (b + 1) (a + (b + 1)) rfl α θ)
      (SupportedCapTestOrderLocal.before_supported X A a (b + 1) α θ hs)
      (CupCapOrder.restriction_zero _ a (b + 1) _ rfl α θ (Or.inr hS))
      (SupportedCap.subspaceMap X S) (fun z => z.property))
  simp only [Category.assoc, zero_comp] at hz
  exact hz

include hS in
theorem difference_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (SupportedCapTestOrderCoupling.difference X A B hA hB hc a b q α θ hs ψ) = 0 := by
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((before_zero X A B hA hB hc a b q α θ hs ψ S hS).trans
    (coupled_zero X A B hA hB hc a b q α θ hs ψ S hS).symm)

include hS in
theorem correction_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (SupportedCupOneCapCorrection.correction X A B hA hB hc a b q α θ hs ψ) = 0 := by
  have hz := congrArg (fun c => c ≫ ψ)
    (SupportedThomCarrierZero.cut_map_zero A B S hA hB hc (a + b) q ((a + b) + q) rfl
      (SupportedCupOneCapCorrection.kappa X a b α θ)
      (SupportedCupOneCapCorrection.kappa_supported X A a b α θ hs)
      (CupOne.restriction_zero _ a (b + 1) _ (by omega) α θ (Or.inr hS))
      (SupportedCap.subspaceMap X S) (fun z => z.property))
  simp only [Category.assoc, zero_comp] at hz
  exact hz

include hS in
theorem primitive_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (SupportedCapTestOrder.primitive X A B hA hB hc a b q α θ hs ψ) = 0 := by
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f _).hom (_ + _) = 0
  rw [map_add]
  change cochainPullback (SupportedCap.subspaceMap X S) ((a + b) + q)
      (SupportedCapTestOrderCoupling.primitive X A B hA hB hc a b q α θ hs ψ) +
    cochainPullback (SupportedCap.subspaceMap X S) ((a + b) + q)
      (SupportedCupOneCapCorrection.correction X A B hA hB hc a b q α θ hs ψ) = 0
  rw [SupportedCapTestOrderCoupling.primitive_carrier_zero X A B hA hB hc a b q α θ hs ψ S
    (difference_zero X A B hA hB hc a b q α θ hs ψ S hS),
    correction_zero X A B hA hB hc a b q α θ hs ψ S hS, add_zero]

end
end Finsler.SupportedTestOrderThomCarrier
