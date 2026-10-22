module

public import Finsler.Geometry.RootField

/-! Root fields and the rest of a root band. Let the stationary sphere polygons of a compact band
of the penalized energy lie in a compact subset S of the regular set. Then for every κ > 0 there
is a smooth compactly supported field supported in the regular set, bounded by κ, along which the
penalized energy does not increase on the regular set and decreases strictly at every polygon of
the band at which its derivative does not vanish (the global root field for the closed
thickenings of S). If a compact set Γ has an open neighbourhood in which every critical point of
a band lies in Γ, then for some δ₁ > 0 the points at distance more than δ₁ from Γ form an open set
which contains every critical point of the band outside Γ and avoids the δ₁-thickening of Γ. -/

@[expose] public section

namespace Finsler.RootBand

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.EnergySphereSmooth Finsler.PolygonCritical Finsler.PolygonLoop Finsler.PolygonSmooth
open Finsler.PolygonEnergyGlobal Finsler.EnergyDiagonal Finsler.PolygonDescent
open Finsler.PseudoGradient Finsler.SphereFlow Finsler.FlowLens Finsler.AmbientPenalty
open Finsler.AmbientDescent Finsler.LevelField Finsler.RootField
open Set Filter Metric
open scoped Topology ContDiff NNReal

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-- **Root fields of every bound.** -/
theorem exists_root_fields (F : ReversibleMetric n) (hn : 1 ≤ n) {lam : ℝ} (hlam : 0 < lam)
    {δ : ℝ}
    (hδ : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
      ContDiffAt ℝ 1 (ambientMinEnergy F) ((P : Ambient n), (Q : Ambient n)))
    {a₀ b₀ : ℝ}
    (hshort : ∀ q : ZMod N → Sphere n, PolygonDescent.energy F N q ≤ b₀ → ShortPolygon δ q)
    {S : Set (ZMod N → Ambient n)} (hS : IsCompact S) (hSreg : S ⊆ regSet F N lam)
    (hcrit : ∀ q : ZMod N → Sphere n, a₀ ≤ PolygonDescent.energy F N q →
      PolygonDescent.energy F N q ≤ b₀ → PolyCritical F N q → (incl q : Om n N).1 ∈ S)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n, ContDiff ℝ ∞ V₀ ∧ HasCompactSupport V₀ ∧
      tsupport V₀ ⊆ regSet F N lam ∧ (∀ z, ‖V₀ z‖ ≤ κ) ∧
      (∀ z ∈ regSet F N lam, fderiv ℝ (pen F N lam) z (V₀ z) ≤ 0) ∧
      ∀ Q : Om n N, a₀ ≤ penW F N lam Q → penW F N lam Q ≤ b₀ →
        fderiv ℝ (pen F N lam) Q.1 ≠ 0 → fderiv ℝ (pen F N lam) Q.1 (V₀ Q.1) < 0 := by
  obtain ⟨ε, hε, hεsub⟩ := hS.exists_cthickening_subset_open (regSet_isOpen F lam) hSreg
  have hε2 : 0 < ε / 2 := half_pos hε
  have hK₁ : IsCompact (cthickening (ε / 2) S) := hS.cthickening
  have hK₀ : IsCompact (cthickening ε S) := hS.cthickening
  have hK₁₀ : cthickening (ε / 2) S ⊆ interior (cthickening ε S) :=
    (cthickening_subset_thickening' hε (half_lt_self hε) S).trans
      (interior_maximal (thickening_subset_cthickening ε S) isOpen_thickening)
  have hS₁ : S ⊆ interior (cthickening (ε / 2) S) :=
    (self_subset_thickening hε2 S).trans
      (interior_maximal (thickening_subset_cthickening _ S) isOpen_thickening)
  obtain ⟨V₀, h1, h2, h3, h4, h5, h6⟩ := exists_root_field F hn hlam hδ hshort hK₀ hK₁ hK₁₀
    hεsub (Wrest := ∅) isOpen_empty
    (fun q ha hb hc => Or.inl (hS₁ (hcrit q ha hb hc))) hκ
  exact ⟨V₀, h1, h2, h3, h4, h5, fun Q ha hb hne => h6 Q ha hb (notMem_empty Q) hne⟩

/-- **The rest of a root band.** -/
theorem exists_rest {Γ 𝒱 : Set (ZMod N → Ambient n)} (hΓ : IsCompact Γ) (hne : Γ.Nonempty)
    (h𝒱 : IsOpen 𝒱) (hΓ𝒱 : Γ ⊆ 𝒱) (P : Om n N → Prop)
    (hiso : ∀ Q : Om n N, P Q → Q.1 ∈ 𝒱 → Q.1 ∈ Γ) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∃ Wrest : Set (Om n N), IsOpen Wrest ∧
      (∀ Q ∈ Wrest, Q.1 ∉ thickening δ₁ Γ) ∧ ∀ Q : Om n N, P Q → Q.1 ∈ Γ ∨ Q ∈ Wrest := by
  obtain ⟨δ₂, hδ₂, hsub⟩ := hΓ.exists_thickening_subset_open h𝒱 hΓ𝒱
  refine ⟨δ₂ / 2, half_pos hδ₂, {Q : Om n N | δ₂ / 2 < infDist Q.1 Γ}, ?_, ?_, ?_⟩
  · exact isOpen_lt continuous_const
      ((continuous_infDist_pt Γ).comp continuous_subtype_val)
  · intro Q hQ hth
    rw [mem_thickening_iff_infDist_lt hne] at hth
    exact absurd hQ (not_lt.mpr hth.le)
  · intro Q hP
    by_cases h : Q.1 ∈ thickening δ₂ Γ
    · exact Or.inl (hiso Q hP (hsub h))
    · right
      rw [mem_thickening_iff_infDist_lt hne, not_lt] at h
      change δ₂ / 2 < infDist Q.1 Γ
      linarith

end

end Finsler.RootBand
