module

public import Finsler.Topology.LensTransport

/-! Restrict a label homeomorphism and its lens correspondence to corresponding fixed subsets.
The lens correspondence can be supplied by the existing same-flow trapped transport. -/

@[expose] public section

namespace Finsler.FixedLensTransport

open CategoryTheory Set Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.LensContinuation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X₁ X₂ : TopCat.{0}} {g₁ : X₁ → ℝ} {g₂ : X₂ → ℝ}
variable (D₁ : Descent X₁ g₁) (D₂ : Descent X₂ g₂) {U₁ : Set X₁} {U₂ : Set X₂}
variable (ξ : U₁ ≃ₜ U₂) {Z₁ : Set X₁} {Z₂ : Set X₂}
variable (hg : ∀ w : U₁, g₂ (ξ w) = g₁ w)
variable (hZ : ∀ w : U₁, (w : X₁) ∈ Z₁ ↔ (ξ w : X₂) ∈ Z₂)

def partMap (hg : ∀ w : U₁, g₂ (ξ w) = g₁ w)
    (hZ : ∀ w : U₁, (w : X₁) ∈ Z₁ ↔ (ξ w : X₂) ∈ Z₂)
    (b : ℝ) : C(↥(partU g₁ U₁ b ∩ Z₁), ↥(partU g₂ U₂ b ∩ Z₂)) :=
  ⟨fun w => ⟨(ξ ⟨w, w.2.1.2⟩ : X₂),
      ⟨(hg ⟨w, w.2.1.2⟩).trans_lt w.2.1.1, (ξ ⟨w, w.2.1.2⟩).2⟩,
      (hZ ⟨w, w.2.1.2⟩).mp w.2.2⟩,
    (continuous_subtype_val.comp (ξ.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _⟩

def partInv (hg : ∀ w : U₁, g₂ (ξ w) = g₁ w)
    (hZ : ∀ w : U₁, (w : X₁) ∈ Z₁ ↔ (ξ w : X₂) ∈ Z₂)
    (b : ℝ) : C(↥(partU g₂ U₂ b ∩ Z₂), ↥(partU g₁ U₁ b ∩ Z₁)) :=
  partMap ξ.symm (fun w => by
    have h := hg (ξ.symm w)
    rw [ξ.apply_symm_apply] at h
    exact h.symm) (fun w => by
    have h := hZ (ξ.symm w)
    rw [ξ.apply_symm_apply] at h
    exact h.symm) b

include hg hZ in
theorem nonempty_equiv {a b T : ℝ}
    (hlens : ∀ w : U₁, g₁ w < b →
      (g₁ (D₁.flow T w) < a ↔ g₂ (D₂.flow T (ξ w)) < a)) (q : ℕ) :
    Nonempty (
      H (triv (pairOf (inter_subset_inter_left Z₁ (partY_sub_partU g₁ D₁ U₁ a b T)))) q ≃ₗ[ZMod 2]
      H (triv (pairOf (inter_subset_inter_left Z₂ (partY_sub_partU g₂ D₂ U₂ a b T)))) q) := by
  let h₁ := inter_subset_inter_left Z₁ (partY_sub_partU g₁ D₁ U₁ a b T)
  let h₂ := inter_subset_inter_left Z₂ (partY_sub_partU g₂ D₂ U₂ a b T)
  have hp : ∀ w : ↥(partU g₁ U₁ b ∩ Z₁), (w : X₁) ∈ partY g₁ D₁ U₁ a b T ∩ Z₁ →
      (partMap ξ hg hZ b w : X₂) ∈ partY g₂ D₂ U₂ a b T ∩ Z₂ := by
    intro w hw
    exact ⟨⟨(hg ⟨w, hw.1.2.2⟩).trans_lt hw.1.1,
      (hlens ⟨w, hw.1.2.2⟩ hw.1.1).mp hw.1.2.1, (ξ ⟨w, hw.1.2.2⟩).2⟩,
      (hZ ⟨w, hw.1.2.2⟩).mp hw.2⟩
  have hi : ∀ w : ↥(partU g₂ U₂ b ∩ Z₂), (w : X₂) ∈ partY g₂ D₂ U₂ a b T ∩ Z₂ →
      (partInv ξ hg hZ b w : X₁) ∈ partY g₁ D₁ U₁ a b T ∩ Z₁ := by
    intro w hw
    have h := hg (ξ.symm ⟨w, hw.1.2.2⟩)
    rw [ξ.apply_symm_apply] at h
    have hi := hlens (ξ.symm ⟨w, hw.1.2.2⟩) (h.symm.trans_lt hw.1.1)
    rw [ξ.apply_symm_apply] at hi
    refine ⟨⟨h.symm.trans_lt hw.1.1, hi.mpr hw.1.2.1, (ξ.symm ⟨w, hw.1.2.2⟩).2⟩, ?_⟩
    apply (hZ (ξ.symm ⟨w, hw.1.2.2⟩)).mpr
    simpa only [ξ.apply_symm_apply] using hw.2
  have hpi : (partMap ξ hg hZ b).comp (partInv ξ hg hZ b) = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro w
    apply Subtype.ext
    change (ξ (ξ.symm ⟨(w : X₂), w.2.1.2⟩) : X₂) = (w : X₂)
    exact congrArg (fun z : U₂ => (z : X₂)) (ξ.apply_symm_apply ⟨w, w.2.1.2⟩)
  have hbij := bijective_Hmap_of_section h₁ h₂ (partMap ξ hg hZ b) (partInv ξ hg hZ b)
    hp hi hpi
    { toFun := fun p => p.2
      continuous_toFun := continuous_snd
      map_zero_left := fun w =>
        Subtype.ext (congrArg (fun z : U₁ => (z : X₁)) (ξ.symm_apply_apply ⟨w, w.2.1.2⟩)).symm
      map_one_left := fun _ => rfl } (fun _ _ hw => hw) q
  exact ⟨(LinearEquiv.ofBijective _ hbij).symm⟩

end

end Finsler.FixedLensTransport

