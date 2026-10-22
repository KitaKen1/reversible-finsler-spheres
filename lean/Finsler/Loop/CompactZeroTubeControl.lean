module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-! A continuous error vanishing on the zero set of a nonnegative
continuous gap is uniformly small on a sufficiently thin gap tube in
a compact parameter space. The minimum is taken only on the bad set. -/

@[expose] public section
namespace Finsler.CompactZeroTubeControl

noncomputable section
set_option autoImplicit false

theorem exists_radius {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (gap error : X → ℝ) (hgap : Continuous gap) (herror : Continuous error)
    (hnonneg : ∀ x, 0 ≤ gap x) (hzero : ∀ x, gap x = 0 → error x = 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ ρ > 0, ∀ x, gap x < ρ → |error x| < ε := by
  have hbad : IsCompact {x | ε ≤ |error x|} :=
    (isClosed_le continuous_const herror.abs).isCompact
  have hpos : ∀ x ∈ {x | ε ≤ |error x|}, 0 < gap x := by
    intro x hx
    by_contra hn
    have hz : gap x = 0 := le_antisymm (le_of_not_gt hn) (hnonneg x)
    have he := hzero x hz
    change ε ≤ |error x| at hx
    rw [he, abs_zero] at hx
    exact (not_le_of_gt hε) hx
  obtain ⟨ρ, hρ, hbound⟩ := hbad.exists_forall_le' hgap.continuousOn hpos
  refine ⟨ρ, hρ, ?_⟩
  intro x hx
  by_contra hn
  exact (not_lt_of_ge (hbound x (le_of_not_gt hn))) hx

end
end Finsler.CompactZeroTubeControl
