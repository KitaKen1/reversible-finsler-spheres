module

public import Finsler.Topology.ActualWindowPieces

/-! the actual event budget, without an EventBounds input.
This connects the constructed local data to the original global linear-budget obligation. -/

@[expose] public section

namespace Finsler.ActualEventBudget

open Finsler.Geometry Finsler.Geodesics Finsler.CriticalLevels
open Finsler.EventSum Finsler.LevelCount

noncomputable section

theorem exists_count_budget {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ M N : ℕ, ∀ a : ℝ, 0 < a → 2 * a ∉ crit F → ∀ K : ℕ,
      ∑ k ∈ Finset.range K, pot F (2 * a) k ≤
        6 * (M : ℤ) * (N : ℤ) * (levelCount F (2 * a) : ℤ) := by
  obtain ⟨E⟩ := Finsler.ActualWindowPieces.nonempty_eventBounds F hn hfin
  exact ⟨E.M, E.N, fun a ha hreg K => sum_pot_le E hn hfin ha hreg K⟩

theorem exists_linear_budget {n : ℕ} (F : ReversibleMetric n) (hn : 1 ≤ n)
    (hfin : (primeImages F).Finite) :
    ∃ C : ℕ, ∀ a : ℝ, 0 < a → 2 * a ∉ crit F → ∀ K : ℕ,
      ((∑ k ∈ Finset.range K, pot F (2 * a) k : ℤ) : ℝ) ≤ C * (1 + a) := by
  obtain ⟨E⟩ := Finsler.ActualWindowPieces.nonempty_eventBounds F hn hfin
  exact exists_sum_pot_le E hn hfin

end

end Finsler.ActualEventBudget
