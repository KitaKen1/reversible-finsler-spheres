module

public import Finsler.Loop.SupportedThomCarrierZero
public import Finsler.Loop.OriginalDoubleCapCommonComparison

/-! Either original Thom factor being zero on a carrier annihilates
the actual sequential cuts, common cup cap, cup-one correction and
subdivision comparison primitive. The original two covers are retained. -/
@[expose] public section
namespace Finsler.DoubleCapThomCarrier
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.OriginalDoubleSupportedCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

variable (X : TopCat.{0}) (A B C D : Set X)
  (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (hD : IsOpen D)
  (hAB : A ∪ B = Set.univ) (hCD : C ∪ D = Set.univ)
  (p r q : ℕ) (θ : singularCochainGroup (ZMod 2) X p)
  (η : singularCochainGroup (ZMod 2) X (r + 1))
  (hθ : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
  (hη : cochainPullback (SupportedCap.subspaceMap X C) (r + 1) η = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of (B ∩ D : Set X)) q) (S : Set X)

theorem sequential_first_zero
    (hS : cochainPullback (SupportedCap.subspaceMap X S) p θ = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) _
      (OriginalDoubleCapCommonComparison.sequential X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 := by
  have hz := congrArg (fun c => c ≫ inner X B C D hC hD hCD (r + 1) q η hη ψ)
    (SupportedThomCarrierZero.cut_map_zero A B S hA hB hAB p ((r + 1) + q) ((p + r) + q + 1) (by omega)
      θ hθ hS (SupportedCap.subspaceMap X S) (fun z => z.property))
  simp only [Category.assoc, zero_comp] at hz
  exact hz

theorem sequential_second_zero
    (hS : cochainPullback (SupportedCap.subspaceMap X S) (r + 1) η = 0) :
    cochainPullback (SupportedCap.subspaceMap X S) _
      (OriginalDoubleCapCommonComparison.sequential X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 := by
  apply SupportedCapTestOrder.cut_carrier_zero_at_degree X A B S hA hB hAB p ((r + 1) + q)
    ((p + r) + q + 1) (by omega) θ hθ (inner X B C D hC hD hCD (r + 1) q η hη ψ)
  let f := restriction (SupportedCap.subspaceMap X S) ((SupportedCap.subspaceMap X S) ⁻¹' B) B (fun _ h => h)
  have hηS := pullback_support (SupportedCap.subspaceMap X B) (secondFar X B S) S
    (fun _ h => h) (r + 1) η hS
  have hz := SupportedThomCarrierZero.cut_map_zero (secondFar X B C) (secondNear X B D) (secondFar X B S)
    (hC.preimage (SupportedCap.subspaceMap X B).hom.continuous)
    (hD.preimage (SupportedCap.subspaceMap X B).hom.continuous) (second_cover X B C D hCD)
    (r + 1) q ((r + 1) + q) rfl (cochainPullback (SupportedCap.subspaceMap X B) (r + 1) η)
    (pullback_support _ (secondFar X B C) C (fun _ h => h) (r + 1) η hη) hηS f (fun z => z.val.property)
  have he := congrArg (fun c => c ≫ cochainPullback (jointMap X B D) q ψ) hz
  simp only [Category.assoc, zero_comp] at he
  exact he

variable (hS : cochainPullback (SupportedCap.subspaceMap X S) p θ = 0 ∨
  cochainPullback (SupportedCap.subspaceMap X S) (r + 1) η = 0)

include hS in
theorem coupled_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (OriginalDoubleCapCommonComparison.coupled X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 :=
  SupportedThomCarrierZero.multi_scalar_zero X (DoubleFarCupOneCap.far X A C) (B ∩ D)
    (DoubleFarCupOneCap.far_open X A C hA hC) (hB.inter hD) (DoubleFarCupOneCap.common_cover X A B C D hAB hCD)
    S (p + r + 1) q ((p + r) + q + 1) (by omega) _
    (DoubleFarCupOneCap.left_supported X A C p r θ η hθ hη)
    (CupCapOrder.restriction_zero _ p (r + 1) _ (by omega) θ η hS) ψ

include hS in
theorem cup_one_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (DoubleFarCupOneCap.primitive X A C p r θ η hθ hη (B ∩ D)
      hA hC (hB.inter hD) (DoubleFarCupOneCap.common_cover X A B C D hAB hCD) q ψ) = 0 :=
  SupportedThomCarrierZero.multi_scalar_zero X (DoubleFarCupOneCap.far X A C) (B ∩ D)
    (DoubleFarCupOneCap.far_open X A C hA hC) (hB.inter hD) (DoubleFarCupOneCap.common_cover X A B C D hAB hCD)
    S (p + r) q ((p + r) + q) rfl _ (DoubleFarCupOneCap.kappa_supported X A C p r θ η hθ hη)
    (CupOne.restriction_zero _ p (r + 1) _ (by omega) θ η hS) ψ

include hS in
theorem primitive_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (OriginalDoubleCapCommonComparison.primitive X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 := by
  apply SupportedSmallCochainComparison.primitive_support_zero
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f _).hom (_ - _) = 0
  rw [map_sub]
  have hseq : cochainPullback (SupportedCap.subspaceMap X S) _
      (OriginalDoubleCapCommonComparison.sequential X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 := by
    rcases hS with hS | hS
    · exact sequential_first_zero X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ S hS
    · exact sequential_second_zero X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ S hS
  exact sub_eq_zero.mpr (hseq.trans (coupled_zero X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ S hS).symm)

end
end Finsler.DoubleCapThomCarrier
