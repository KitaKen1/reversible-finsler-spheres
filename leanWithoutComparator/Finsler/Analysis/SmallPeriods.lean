module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Functions with arbitrarily small periods. A function from the real line to the natural
numbers whose sublevel sets are open (an upper semicontinuous function) and which has
arbitrarily small positive periods is constant: near a point its values are at most the value
at the point, and every other point can be moved into that neighbourhood by a multiple of a
small period. -/

@[expose] public section

namespace Finsler.SmallPeriods

open Function

/-- An upper semicontinuous function with natural values and arbitrarily small positive periods
takes at every point at most its value at any other point. -/
theorem le_of_small_periods {f : ℝ → ℕ} (hopen : ∀ k, IsOpen {θ : ℝ | f θ ≤ k})
    (hper : ∀ ε > 0, ∃ τ, 0 < τ ∧ τ < ε ∧ Periodic f τ) (θ₀ θ₁ : ℝ) : f θ₁ ≤ f θ₀ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hopen (f θ₀)) θ₀ (le_refl (f θ₀))
  obtain ⟨τ, hτ, hτε, hp⟩ := hper ε hε
  have h1 : ((⌊(θ₀ - θ₁) / τ⌋ : ℤ) : ℝ) ≤ (θ₀ - θ₁) / τ := Int.floor_le _
  have h2 : (θ₀ - θ₁) / τ < (⌊(θ₀ - θ₁) / τ⌋ : ℤ) + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hτ] at h1
  rw [div_lt_iff₀ hτ] at h2
  have hmem : θ₁ + (⌊(θ₀ - θ₁) / τ⌋ : ℤ) * τ ∈ Metric.ball θ₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> nlinarith
  have h5 : f (θ₁ + (⌊(θ₀ - θ₁) / τ⌋ : ℤ) * τ) ≤ f θ₀ := hball hmem
  rwa [(hp.int_mul ⌊(θ₀ - θ₁) / τ⌋) θ₁] at h5

/-- An upper semicontinuous function with natural values and arbitrarily small positive periods
is constant. -/
theorem eq_of_small_periods {f : ℝ → ℕ} (hopen : ∀ k, IsOpen {θ : ℝ | f θ ≤ k})
    (hper : ∀ ε > 0, ∃ τ, 0 < τ ∧ τ < ε ∧ Periodic f τ) (θ₀ θ₁ : ℝ) : f θ₁ = f θ₀ :=
  le_antisymm (le_of_small_periods hopen hper θ₀ θ₁) (le_of_small_periods hopen hper θ₁ θ₀)

end Finsler.SmallPeriods
