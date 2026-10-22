module

public import Finsler.Topology.LensContinuation

/-! Lens pairs of two systems which agree on an open set. Let two descents, of functions g₁ on
X₁ and g₂ on X₂, be given with open sets 𝒲₁ and 𝒲₂ and a homeomorphism ξ of 𝒲₁ onto 𝒲₂ under
which the functions correspond. Suppose that in both systems a point of the open set below b
which is not taken below a in time T stays in the open set up to the time T, and that the
values of the functions after the time T correspond for the points whose orbit stays in the
open set up to the time T, in either system. Then the lens sets correspond under ξ, and the
lens pairs in 𝒲₁ and 𝒲₂ have isomorphic cohomology. The flows are not assumed to correspond
outside the open sets. -/

@[expose] public section

namespace Finsler.LensTransport

open CategoryTheory Set Topology Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.FlowLens Finsler.LensContinuation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X₁ X₂ : TopCat.{0}} {g₁ : X₁ → ℝ} {g₂ : X₂ → ℝ} (D₁ : Descent X₁ g₁)
  (D₂ : Descent X₂ g₂) {𝒲₁ : Set X₁} {𝒲₂ : Set X₂} (ξ : 𝒲₁ ≃ₜ 𝒲₂) {a b T : ℝ}
  (hg : ∀ w : 𝒲₁, g₂ (ξ w) = g₁ w)
  (hS₁ : ∀ w, w ∈ 𝒲₁ → g₁ w < b → a ≤ g₁ (D₁.flow T w) → ∀ s, 0 ≤ s → s ≤ T →
    D₁.flow s w ∈ 𝒲₁)
  (hS₂ : ∀ w, w ∈ 𝒲₂ → g₂ w < b → a ≤ g₂ (D₂.flow T w) → ∀ s, 0 ≤ s → s ≤ T →
    D₂.flow s w ∈ 𝒲₂)
  (hA₁ : ∀ w : 𝒲₁, (∀ s, 0 ≤ s → s ≤ T → D₁.flow s w ∈ 𝒲₁) →
    g₂ (D₂.flow T (ξ w)) = g₁ (D₁.flow T w))
  (hA₂ : ∀ w : 𝒲₁, (∀ s, 0 ≤ s → s ≤ T → D₂.flow s (ξ w) ∈ 𝒲₂) →
    g₂ (D₂.flow T (ξ w)) = g₁ (D₁.flow T w))

include hg hS₁ hS₂ hA₁ hA₂ in
/-- The lens sets correspond. -/
theorem lens_iff (w : 𝒲₁) (hw : g₁ w < b) :
    g₁ (D₁.flow T w) < a ↔ g₂ (D₂.flow T (ξ w)) < a := by
  constructor
  · intro h
    by_contra h'
    have h2 := hA₂ w (hS₂ (ξ w) (ξ w).2 ((hg w).trans_lt hw) (not_lt.mp h'))
    exact h' (h2.trans_lt h)
  · intro h
    by_contra h'
    have h1 := hA₁ w (hS₁ w w.2 hw (not_lt.mp h'))
    exact h' (h1.symm.trans_lt h)

/-- The map of the parts of the sublevels induced by the homeomorphism. -/
def partMap (hg : ∀ w : 𝒲₁, g₂ (ξ w) = g₁ w) (b : ℝ) :
    C(partU g₁ 𝒲₁ b, partU g₂ 𝒲₂ b) :=
  ⟨fun w => ⟨(ξ ⟨w, w.2.2⟩ : X₂), (hg ⟨w, w.2.2⟩).trans_lt w.2.1, (ξ ⟨w, w.2.2⟩).2⟩,
    (continuous_subtype_val.comp (ξ.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _⟩

/-- Its inverse. -/
def partInv (hg : ∀ w : 𝒲₁, g₂ (ξ w) = g₁ w) (b : ℝ) :
    C(partU g₂ 𝒲₂ b, partU g₁ 𝒲₁ b) :=
  ⟨fun w => ⟨(ξ.symm ⟨w, w.2.2⟩ : X₁), by
      have h := hg (ξ.symm ⟨w, w.2.2⟩)
      rw [ξ.apply_symm_apply] at h
      exact h.symm.trans_lt w.2.1, (ξ.symm ⟨w, w.2.2⟩).2⟩,
    (continuous_subtype_val.comp (ξ.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _))).subtype_mk _⟩

include hS₁ hS₂ hA₁ hA₂ in
/-- The lens pairs in the two open sets have isomorphic cohomology: the map induced by the
homeomorphism is bijective on cohomology. -/
theorem part_bijective (n : ℕ) :
    Function.Bijective (Hmap (trivHom (pairMapX (partY_sub_partU g₁ D₁ 𝒲₁ a b T)
      (partY_sub_partU g₂ D₂ 𝒲₂ a b T) (partMap ξ hg b)
      (fun w hw => ⟨(hg ⟨w, hw.2.2⟩).trans_lt hw.1,
        (lens_iff D₁ D₂ ξ hg hS₁ hS₂ hA₁ hA₂ ⟨w, hw.2.2⟩ hw.1).mp hw.2.1,
        (ξ ⟨w, hw.2.2⟩).2⟩))) n) := by
  refine bijective_Hmap_of_section _ _ (partMap ξ hg b) (partInv ξ hg b) _ ?_ ?_
    { toFun := fun q => q.2
      continuous_toFun := continuous_snd
      map_zero_left := fun w => ?_
      map_one_left := fun _ => rfl } (fun _ _ hw => hw) n
  · intro w hw
    have h := hg (ξ.symm ⟨w, hw.2.2⟩)
    rw [ξ.apply_symm_apply] at h
    refine ⟨h.symm.trans_lt hw.1, ?_, (ξ.symm ⟨w, hw.2.2⟩).2⟩
    have hi := lens_iff D₁ D₂ ξ hg hS₁ hS₂ hA₁ hA₂ (ξ.symm ⟨w, hw.2.2⟩) (h.symm.trans_lt hw.1)
    rw [ξ.apply_symm_apply] at hi
    exact hi.mpr hw.2.1
  · refine ContinuousMap.ext fun w => Subtype.ext ?_
    change ((ξ (ξ.symm ⟨(w : X₂), w.2.2⟩) : 𝒲₂) : X₂) = (w : X₂)
    rw [ξ.apply_symm_apply]
  · exact Subtype.ext (congrArg Subtype.val (ξ.symm_apply_apply ⟨w, w.2.2⟩)).symm

end

end Finsler.LensTransport
