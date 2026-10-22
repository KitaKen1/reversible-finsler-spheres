module

public import Finsler.Loop.OriginalDoubleCapCommonComparison

/-! Whole-parent carrier ZERO survives BOTH ORIGINAL supported cuts,
the common-cover cup cap, and their actual subdivision primitive.
Only the genuine common-near output is required to vanish there. -/
@[expose] public section
namespace Finsler.OriginalDoubleCapCarrier
open CategoryTheory CategoryTheory.Limits AlgebraicTopology SphereOddDegree
open Finsler.CochainComparison Finsler.SmallChainCarrier Finsler.SupportedCapNaturality
open Finsler.OriginalDoubleSupportedCap
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

variable (X : TopCat.{0}) (A B C D : Set X)
  (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (hD : IsOpen D)
  (hAB : A ∪ B = Set.univ) (hCD : C ∪ D = Set.univ)
  (p r q : ℕ) (θ : singularCochainGroup (ZMod 2) X p)
  (η : singularCochainGroup (ZMod 2) X (r + 1))
  (hθ : cochainPullback (SupportedCap.subspaceMap X A) p θ = 0)
  (hη : cochainPullback (SupportedCap.subspaceMap X C) (r + 1) η = 0)
  (ψ : singularCochainGroup (ZMod 2) (TopCat.of (B ∩ D : Set X)) q)
  (S : Set X)
  (hψ : cochainPullback (restriction (SupportedCap.subspaceMap X S)
    ((SupportedCap.subspaceMap X S) ⁻¹' (B ∩ D)) (B ∩ D) (fun _ h => h)) q ψ = 0)

include hψ in
theorem sequential_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (OriginalDoubleCapCommonComparison.sequential X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 := by
  let S₁ : Set (TopCat.of B) := (SupportedCap.subspaceMap X B) ⁻¹' S
  let f := restriction (SupportedCap.subspaceMap (TopCat.of B) S₁)
    ((SupportedCap.subspaceMap (TopCat.of B) S₁) ⁻¹' secondNear X B D) (secondNear X B D) (fun _ h => h)
  let g : TopCat.of ((SupportedCap.subspaceMap (TopCat.of B) S₁) ⁻¹' secondNear X B D) ⟶
      TopCat.of ((SupportedCap.subspaceMap X S) ⁻¹' (B ∩ D)) := TopCat.ofHom
    ⟨fun z => ⟨⟨z.val.val.val, z.val.property⟩, z.val.val.property, z.property⟩,
      (((continuous_subtype_val.comp continuous_subtype_val).comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩
  have he : f ≫ jointMap X B D = g ≫ restriction (SupportedCap.subspaceMap X S)
      ((SupportedCap.subspaceMap X S) ⁻¹' (B ∩ D)) (B ∩ D) (fun _ h => h) := rfl
  have hz : cochainPullback f q (cochainPullback (jointMap X B D) q ψ) = 0 := by
    rw [← pullback_comp, he, pullback_comp, hψ]
    change (push g).f q ≫ 0 = 0
    exact comp_zero
  have hi := SupportedCapTestOrder.cut_carrier_zero_at_degree (TopCat.of B)
    (secondFar X B C) (secondNear X B D) S₁
    (hC.preimage (SupportedCap.subspaceMap X B).hom.continuous)
    (hD.preimage (SupportedCap.subspaceMap X B).hom.continuous) (second_cover X B C D hCD)
    (r + 1) q ((r + 1) + q) rfl (cochainPullback (SupportedCap.subspaceMap X B) (r + 1) η)
    (pullback_support _ (secondFar X B C) C (fun _ h => h) (r + 1) η hη)
    (cochainPullback (jointMap X B D) q ψ) hz
  change cochainPullback (SupportedCap.subspaceMap (TopCat.of B) S₁) ((r + 1) + q)
    (inner X B C D hC hD hCD (r + 1) q η hη ψ) = 0 at hi
  apply SupportedCapTestOrder.cut_carrier_zero_at_degree X A B S hA hB hAB p ((r + 1) + q)
    ((p + r) + q + 1) (by omega) θ hθ (inner X B C D hC hD hCD (r + 1) q η hη ψ)
  let t : TopCat.of ((SupportedCap.subspaceMap X S) ⁻¹' B) ⟶ TopCat.of S₁ := TopCat.ofHom
    ⟨fun z => ⟨⟨z.val.val, z.property⟩, z.val.property⟩,
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _⟩
  have ht : restriction (SupportedCap.subspaceMap X S) ((SupportedCap.subspaceMap X S) ⁻¹' B) B (fun _ h => h) =
      t ≫ SupportedCap.subspaceMap (TopCat.of B) S₁ := rfl
  rw [ht, pullback_comp, hi]
  change (push t).f _ ≫ 0 = 0
  exact comp_zero

include hψ in
theorem coupled_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (OriginalDoubleCapCommonComparison.coupled X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 :=
  MultiFarSupportedCochain.subspace_zero X (DoubleFarCupOneCap.far X A C) (B ∩ D)
    (DoubleFarCupOneCap.far_open X A C hA hC) (hB.inter hD) (DoubleFarCupOneCap.common_cover X A B C D hAB hCD)
    S (p + r + 1) q ((p + r) + q + 1) (by omega) _
    (DoubleFarCupOneCap.left_supported X A C p r θ η hθ hη) ψ hψ

include hψ in
theorem primitive_zero : cochainPullback (SupportedCap.subspaceMap X S) _
    (OriginalDoubleCapCommonComparison.primitive X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ) = 0 := by
  apply SupportedSmallCochainComparison.primitive_support_zero
  change ((singularCochainComplexZMod2.map (SupportedCap.subspaceMap X S).op).f _).hom (_ - _) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr ((sequential_zero X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ S hψ).trans
    (coupled_zero X A B C D hA hB hC hD hAB hCD p r q θ η hθ hη ψ S hψ).symm)

end
end Finsler.OriginalDoubleCapCarrier
