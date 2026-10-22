module

public import Finsler.Analysis.LevelGlue
public import Finsler.Analysis.EquivariantApprox
public import Finsler.Analysis.EquivariantField

/-! Smooth invariant cutoffs obtained by averaging the ordinary cutoff over an involution. -/

@[expose] public section

namespace Finsler.InvariantCutoff

open Set Topology Finsler.EquivariantApprox Finsler.EquivariantField
open scoped ContDiff

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- An invariant compact set inside an invariant open set admits an invariant smooth cutoff,
equal to one on an invariant open neighbourhood and with compact support in the given set. -/
theorem exists_invariant_cutoff (τ : E →L[ℝ] E) (hτ : ∀ x, τ (τ x) = x)
    {T U : Set E} (hT : IsCompact T) (hU : IsOpen U) (hTU : T ⊆ U)
    (hTτ : ∀ x ∈ T, τ x ∈ T) (hUτ : ∀ x ∈ U, τ x ∈ U) :
    ∃ (χ : E → ℝ) (W : Set E), ContDiff ℝ ∞ χ ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ (∀ y, χ (τ y) = χ y) ∧
      IsOpen W ∧ T ⊆ W ∧ (∀ y, τ y ∈ W ↔ y ∈ W) ∧ ∀ y ∈ W, χ y = 1 := by
  obtain ⟨χ, W, hχ, hr, hc, hs, hW, hTW, hone⟩ := Finsler.LevelGlue.exists_cutoff hT hU hTU
  let χ' := average τ (ContinuousLinearMap.id ℝ ℝ) χ
  have hcomp : HasCompactSupport (χ ∘ τ) := hc.comp_homeomorph (invHomeo τ hτ)
  have hc' : HasCompactSupport χ' := (hc.add hcomp).smul_left (f := fun _ => (1 / 2 : ℝ))
  have hs' : tsupport χ' ⊆ U := by
    intro x hx
    have ha : x ∈ tsupport (fun y => χ y + χ (τ y)) :=
      tsupport_smul_subset_right (fun _ => (1 / 2 : ℝ)) _ hx
    rcases tsupport_add χ (χ ∘ τ) ha with h | h
    · exact hs h
    · have ht : τ x ∈ tsupport χ := tsupport_comp_subset_preimage χ τ.continuous h
      have hu := hUτ (τ x) (hs ht)
      rwa [hτ] at hu
  refine ⟨χ', W ∩ τ ⁻¹' W, average_contDiff τ _ hχ, ?_, hc', hs', ?_,
    hW.inter (hW.preimage τ.continuous), ?_, ?_, ?_⟩
  · intro y
    have h₁ := hr y
    have h₂ := hr (τ y)
    change 0 ≤ (1 / 2 : ℝ) * (χ y + χ (τ y)) ∧ (1 / 2 : ℝ) * (χ y + χ (τ y)) ≤ 1
    constructor <;> linarith
  · intro y
    exact average_equivariant τ (ContinuousLinearMap.id ℝ ℝ) hτ (fun _ => rfl) χ y
  · exact fun y hy => ⟨hTW hy, hTW (hTτ y hy)⟩
  · intro y
    change (τ y ∈ W ∧ τ (τ y) ∈ W) ↔ (y ∈ W ∧ τ y ∈ W)
    rw [hτ]
    exact and_comm
  · intro y hy
    change (1 / 2 : ℝ) * (χ y + χ (τ y)) = 1
    rw [hone y hy.1, hone (τ y) hy.2]
    norm_num

end

end Finsler.InvariantCutoff
