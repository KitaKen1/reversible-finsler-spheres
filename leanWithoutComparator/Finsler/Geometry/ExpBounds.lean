module

public import Finsler.Geometry.CoordinateExp
public import Finsler.Analysis.Taylor2

/-! Quadratic position estimate for the coordinate geodesic flow. On jets over a closed chart
ball with velocity norm in [a,b], 0 < a, the uniform-time flow has bounded acceleration on a
compact time interval, so the position deviates from the straight line y + s·u by at most M s². -/

@[expose] public section

namespace Finsler.ExpBounds

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.UniformFlow Finsler.CoordinateExp Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ}

/-- Jets over a closed chart ball with velocity norm in [a,b]. -/
def annulusJets (y₀ : Coordinates n) (r a b : ℝ) : Set (Coordinates n × Coordinates n) :=
  closedBall y₀ r ×ˢ {u | a ≤ ‖u‖ ∧ ‖u‖ ≤ b}

theorem annulusJets_isCompact (y₀ : Coordinates n) (r a b : ℝ) :
    IsCompact (annulusJets y₀ r a b) := by
  apply (isCompact_closedBall y₀ r).prod
  apply (isCompact_closedBall (0 : Coordinates n) b).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro u hu
    simpa using hu.2

theorem annulusJets_subset (p : Sphere n) {y₀ : Coordinates n} {r a b : ℝ} (ha : 0 < a)
    (hr : closedBall y₀ r ⊆ (extChartAt (𝓡 n) p).target) : annulusJets y₀ r a b ⊆ slitJets p := by
  rintro z ⟨hz1, hz2, -⟩
  refine ⟨hr hz1, ?_⟩
  intro h0
  rw [h0, norm_zero] at hz2
  linarith

section Taylor

variable (F : ReversibleMetric n) (p : Sphere n)
  {Φ : Coordinates n × Coordinates n → ℝ → Coordinates n × Coordinates n} {τ : ℝ}
  {z : Coordinates n × Coordinates n} (h0 : Φ z 0 = z)
  (hode : ∀ t : ℝ, |t| < τ → Φ z t ∈ slitJets p ∧ HasDerivAt (Φ z) (geodesicField F p (Φ z t)) t)

include hode in
theorem position_hasDerivAt {t : ℝ} (ht : |t| < τ) :
    HasDerivAt (fun σ => (Φ z σ).1) (Φ z t).2 t :=
  (hasFDerivAt_fst (𝕜 := ℝ) (p := Φ z t)).comp_hasDerivAt t (hode t ht).2

include hode in
theorem velocity_hasDerivAt {t : ℝ} (ht : |t| < τ) :
    HasDerivAt (fun σ => (Φ z σ).2) (spray (coordinateLagrangian F p) (Φ z t)) t :=
  (hasFDerivAt_snd (𝕜 := ℝ) (p := Φ z t)).comp_hasDerivAt t (hode t ht).2

include h0 hode in
/-- Quadratic deviation of the position from the straight line. -/
theorem position_taylor {M s : ℝ} (hM0 : 0 ≤ M) (hs : 0 ≤ s) (hsτ : s < τ)
    (hM : ∀ σ ∈ Icc (0 : ℝ) s, ‖spray (coordinateLagrangian F p) (Φ z σ)‖ ≤ M) :
    ‖(Φ z s).1 - z.1 - s • z.2‖ ≤ M * s ^ 2 := by
  have habs : ∀ σ ∈ Icc (0 : ℝ) s, |σ| < τ := fun σ hσ => by
    rw [abs_of_nonneg hσ.1]
    exact lt_of_le_of_lt hσ.2 hsτ
  have h := Finsler.Taylor2.taylor_sub_le (f := fun σ => (Φ z σ).1) (f' := fun σ => (Φ z σ).2)
    (f'' := fun σ => spray (coordinateLagrangian F p) (Φ z σ)) hs hM0
    (fun σ hσ => position_hasDerivAt F p hode (habs σ hσ))
    (fun σ hσ => velocity_hasDerivAt F p hode (habs σ hσ)) hM
  simpa [h0] using h

end Taylor

/-- The spray is bounded along the uniform-time flow from a compact set of jets. -/
theorem exists_spray_bound (F : ReversibleMetric n) (p : Sphere n)
    {Φ : Coordinates n × Coordinates n → ℝ → Coordinates n × Coordinates n}
    (hΦc : Continuous (fun q : (Coordinates n × Coordinates n) × ℝ => Φ q.1 q.2))
    {K : Set (Coordinates n × Coordinates n)} (hK : IsCompact K) {τ : ℝ}
    (hode : ∀ z ∈ K, ∀ t : ℝ, |t| < τ →
      Φ z t ∈ slitJets p ∧ HasDerivAt (Φ z) (geodesicField F p (Φ z t)) t)
    {T : ℝ} (hTτ : T < τ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ∀ t ∈ Icc (-T) T,
      ‖spray (coordinateLagrangian F p) (Φ z t)‖ ≤ M := by
  set S := (fun q : (Coordinates n × Coordinates n) × ℝ => Φ q.1 q.2) '' (K ×ˢ Icc (-T) T)
  have hS : IsCompact S := (hK.prod isCompact_Icc).image hΦc
  have hsub : S ⊆ slitJets p := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    have hlt : |q.2| < τ := lt_of_le_of_lt (abs_le.mpr hq2) hTτ
    exact (hode q.1 hq1 q.2 hlt).1
  have hcont : ContinuousOn (spray (coordinateLagrangian F p)) S := fun x hx =>
    (coordinate_spray_contDiffAt F p (hsub hx).1 (hsub hx).2 0).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hcont
  refine ⟨max C 0, le_max_right _ _, fun z hz t ht => ?_⟩
  exact (hC _ ⟨(z, t), ⟨hz, ht⟩, rfl⟩).trans (le_max_left _ _)

end

end Finsler.ExpBounds
