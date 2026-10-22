module

public import Finsler.Geometry.PolygonDescent
public import Finsler.Topology.LensLabels
public import Finsler.Topology.LensTrap

/-! The crossing pairs of the polygon energy split into lens pairs near the stationary
polygons. Let the polygons of energy at most b₀ be short, and let 𝒲₁, 𝒲₂ be disjoint open sets of
the polygon space whose union contains the polygons of energy in [a₀, b₀] which are stationary
along all curves of sphere polygons. Then there are a descending semiflow of the polygon energy
and d > 0 such that for cuts a₀ ≤ a' < a ≤ b ≤ b₀ with b − a' < d and every time T ≥ 1 the
cohomology of the polygons below b relative to those below a is the product of the cohomologies
of the lens pairs in 𝒲₁ and 𝒲₂. The semiflow is the one constructed from a pseudo-gradient; the
band is compact because the polygon space is, so the trapping follows from the strict decrease
of the time-one map outside 𝒲₁ ∪ 𝒲₂. -/

@[expose] public section

namespace Finsler.PolygonCrossing

open CategoryTheory Finsler.SphereGeometry Finsler.Geometry Finsler.EnergySphereSmooth
open Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonDescent Finsler.FlowLens
open Finsler.LensContinuation Finsler.LensLabels Finsler.LensTrap Finsler.BorelCochain
open Finsler.BorelLoop Finsler.PairTriple
open Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ}

/-- A band of the polygon energy is compact. -/
theorem band_isCompact (F : ReversibleMetric n) (hn : 1 ≤ n) (N : ℕ) (a₀ b₀ : ℝ) :
    IsCompact {q : Poly n N | a₀ ≤ energy F N q ∧ energy F N q ≤ b₀} :=
  ((isClosed_le continuous_const (energy_continuous F hn N)).inter
    (isClosed_le (energy_continuous F hn N) continuous_const)).isCompact

/-- The crossing pairs of the polygon energy for tight cuts are products of the lens pairs in
two disjoint open sets containing the stationary polygons. -/
theorem exists_crossing_decomposition (F : ReversibleMetric n) (hn : 1 ≤ n) {N : ℕ} [NeZero N]
    {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ} (hshort : ∀ q : ZMod N → Sphere n, energy F N q ≤ b₀ → ShortPolygon δ q)
    {𝒲₁ 𝒲₂ : Set (Poly n N)} (h₁ : IsOpen 𝒲₁) (h₂ : IsOpen 𝒲₂) (hdis : Disjoint 𝒲₁ 𝒲₂)
    (hcrit : ∀ q : ZMod N → Sphere n, a₀ ≤ energy F N q → energy F N q ≤ b₀ →
      PolyCritical F N q → q ∈ 𝒲₁ ∪ 𝒲₂) :
    ∃ D : Descent (Poly n N) (energy F N), ∃ d : ℝ, 0 < d ∧
      ∀ (a' a b T : ℝ) (hab : a ≤ b) (hT : 0 ≤ T), a₀ ≤ a' → a' < a → b ≤ b₀ → b - a' < d →
        1 ≤ T → ∀ k : ℕ,
        Nonempty (H (triv (pairOf ((sub_subset_lensY D hab hT).trans
            (lensY_subset D a b T)))) k ≃ₗ[ZMod 2]
          (H (triv (pairOf (partY_sub_partU (energy F N) D 𝒲₁ a b T))) k ×
            H (triv (pairOf (partY_sub_partU (energy F N) D 𝒲₂ a b T))) k)) := by
  obtain ⟨D, hD⟩ := exists_descent F hn hδ hshort (h₁.union h₂) hcrit
  obtain ⟨d, hd, htr⟩ := exists_trap D (energy_continuous F hn N) (h₁.union h₂)
    (band_isCompact F hn N a₀ b₀) (fun w ha hb hw => hD w ha hb hw)
  refine ⟨D, d, hd, ?_⟩
  intro a' a b T hab hT ha0 ha hb0 hwidth hT1 k
  exact ⟨labelEquiv D (energy_continuous F hn N) hab ha hT h₁ h₂ hdis
    (htr a' b T ha0 hb0 hwidth hT1) k⟩

end

end Finsler.PolygonCrossing
