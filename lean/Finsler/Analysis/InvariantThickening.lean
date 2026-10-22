module

public import Finsler.Analysis.InvariantCutoff

/-! Invariant sets and their metric thickenings under an isometric linear involution. -/

@[expose] public section

namespace Finsler.InvariantThickening

open Set Metric
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (τ : E →L[ℝ] E) (hτ : ∀ x, τ (τ x) = x)
  {Γ : Set E} (hΓτ : ∀ x ∈ Γ, τ x ∈ Γ)

include hτ hΓτ

theorem image_eq : τ '' Γ = Γ := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hΓτ x hx
  · intro x hx
    exact ⟨τ x, hΓτ x hx, hτ x⟩

omit hΓτ in
/-- An invariant set has invariant interior under a linear involution. -/
theorem interior_invariant {K : Set E} (hK : ∀ x, τ x ∈ K ↔ x ∈ K) (x : E) :
    τ x ∈ interior K ↔ x ∈ interior K := by
  have he : (Finsler.EquivariantField.invHomeo τ hτ) ⁻¹' K = K := Set.ext hK
  change x ∈ (Finsler.EquivariantField.invHomeo τ hτ) ⁻¹' interior K ↔ x ∈ interior K
  rw [(Finsler.EquivariantField.invHomeo τ hτ).preimage_interior, he]

variable (hiso : Isometry τ)

include hτ hΓτ hiso

theorem thickening_invariant (δ : ℝ) (x : E) :
    τ x ∈ thickening δ Γ ↔ x ∈ thickening δ Γ := by
  have he : infEDist (τ x) Γ = infEDist x Γ := by
    simpa only [image_eq τ hτ hΓτ] using (infEDist_image hiso (x := x) (t := Γ))
  rw [mem_thickening_iff_infEDist_lt, mem_thickening_iff_infEDist_lt, he]

theorem cthickening_invariant (δ : ℝ) (x : E) :
    τ x ∈ cthickening δ Γ ↔ x ∈ cthickening δ Γ := by
  have he : infEDist (τ x) Γ = infEDist x Γ := by
    simpa only [image_eq τ hτ hΓτ] using (infEDist_image hiso (x := x) (t := Γ))
  rw [mem_cthickening_iff, mem_cthickening_iff, he]

end

end Finsler.InvariantThickening
