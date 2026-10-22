module

public import Finsler.Topology.SubspacePairs

/-! The intrinsic restricted-flow lens is the actual ambient lens intersected with the subspace. -/

@[expose] public section

namespace Finsler.RestrictedLensPairs

open Set Finsler.FlowLens Finsler.LensFamily Finsler.LensContinuation
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {W : TopCat.{0}} {g : W → ℝ} (D : Descent W g) {Z : Set W}
    (hDZ : ∀ t (z : W), 0 ≤ t → z ∈ Z → D.flow t z ∈ Z)

theorem partY_preimage (U : Set W) (a b t : ℝ) (ht : 0 ≤ t) :
    partY (fun z : TopCat.of Z => g z) (Finsler.SubspaceK.subDescent D hDZ)
      (Subtype.val ⁻¹' U) a b t = Subtype.val ⁻¹' partY g D U a b t := by
  ext z
  change (g z < b ∧ g (D.flow (max t 0) z) < a ∧ (z : W) ∈ U) ↔
    (g z < b ∧ g (D.flow t z) < a ∧ (z : W) ∈ U)
  rw [max_eq_left ht]

def lensHEquiv (U : Set W) (a b t : ℝ) (ht : 0 ≤ t) (q : ℕ) :
    lensH (Finsler.SubspaceK.subDescent D hDZ) (Subtype.val ⁻¹' U) a b t q ≃ₗ[ZMod 2]
      H (triv (pairOf (inter_subset_inter_left Z (partY_sub_partU g D U a b t)))) q :=
  (Finsler.SubspacePairs.equalHEquiv (partY_preimage D hDZ U a b t ht) rfl _ _ q).trans
    (Finsler.SubspacePairs.insideHEquiv Z (partY_sub_partU g D U a b t) q)

theorem support_outside (U : Set W) (a b t : ℝ) (ht : 0 ≤ t) (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2)
      (lensH (Finsler.SubspaceK.subDescent D hDZ) (Subtype.val ⁻¹' U) a b t q))
    (hz : ∀ q, A ≤ q → ∀ x :
      lensH (Finsler.SubspaceK.subDescent D hDZ) (Subtype.val ⁻¹' U) a b t q, x = 0) :
    (∀ q, Module.Finite (ZMod 2)
      (H (triv (pairOf (inter_subset_inter_left Z (partY_sub_partU g D U a b t)))) q)) ∧
      ∀ q, A ≤ q → ∀ x :
        H (triv (pairOf (inter_subset_inter_left Z (partY_sub_partU g D U a b t)))) q, x = 0 := by
  constructor
  · intro q
    have := hf q
    exact Module.Finite.equiv (lensHEquiv D hDZ U a b t ht q)
  · intro q hq x
    obtain ⟨y, rfl⟩ := (lensHEquiv D hDZ U a b t ht q).surjective x
    rw [hz q hq y]
    exact (lensHEquiv D hDZ U a b t ht q).map_zero

end

end Finsler.RestrictedLensPairs

