module

public import Finsler.Geometry.ExpBounds
public import Finsler.Analysis.UniformFlowGlobal
public import Finsler.Analysis.ParamTaylor
public import Finsler.Analysis.RadialRemainder

/-! The coordinate exponential map near the zero section and its local inverse. The global flow
of the cut-off geodesic field is C³; Taylor's formula with a C¹ integral remainder R writes its
position as y + s·u + s²R((y,u),s) on unit jets, so the exponential map is
exp(y,v) = y + v + ‖v‖²R((y,v/‖v‖),‖v‖). Bounds for R and DR on a compact set make the remainder
1/2-Lipschitz on a small ball, so the contraction principle inverts exp(y,·) there; for v ≠ 0 the
value is the endpoint of the coordinate geodesic with initial jet (y,v). -/

@[expose] public section

namespace Finsler.CoordinateExpInverse

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.ExpBounds Finsler.RadialRemainder Finsler.ParamTaylor
open Finsler.ChartPath Finsler.SobolevSpherePath Finsler.SphereDistance Finsler.IntervalSobolev
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ}

/-- Data of the coordinate exponential map over a closed chart ball. -/
structure ExpData (F : ReversibleMetric n) (p : Sphere n) (y₀ : Coordinates n) (r : ℝ) where
  Φ : Coordinates n × Coordinates n → ℝ → Coordinates n × Coordinates n
  R : (Coordinates n × Coordinates n) × ℝ → Coordinates n
  τ : ℝ
  ρ : ℝ
  τ_pos : 0 < τ
  ρ_pos : 0 < ρ
  ρ_le_one : ρ ≤ 1
  ρ_lt_τ : ρ < τ
  smooth : ContDiff ℝ 3 (fun q : (Coordinates n × Coordinates n) × ℝ => Φ q.1 q.2)
  init : ∀ z, Φ z 0 = z
  ode : ∀ z ∈ unitJets y₀ r, ∀ t : ℝ, |t| < τ →
    Φ z t ∈ slitJets p ∧ HasDerivAt (Φ z) (geodesicField F p (Φ z t)) t
  R_smooth : ContDiff ℝ 1 R
  exp_eq : ∀ y ∈ closedBall y₀ r, ∀ v : Coordinates n, v ≠ 0 →
    y + v + rad R y v = (Φ (y, ‖v‖⁻¹ • v) ‖v‖).1
  lip : ∀ y ∈ closedBall y₀ r, ∀ v ∈ closedBall (0 : Coordinates n) ρ,
    ∀ w ∈ closedBall (0 : Coordinates n) ρ, ‖rad R y v - rad R y w‖ ≤ ‖v - w‖ / 2

theorem unitJets_subset_annulus (y₀ : Coordinates n) (r : ℝ) :
    unitJets y₀ r ⊆ annulusJets y₀ r (1 / 2) 2 := by
  rintro z ⟨hz1, hz2⟩
  have h : ‖z.2‖ = 1 := by simpa using hz2
  exact ⟨hz1, by rw [h]; norm_num, by rw [h]; norm_num⟩

theorem normalize_mem_unitJets {y₀ y v : Coordinates n} {r : ℝ} (hy : y ∈ closedBall y₀ r)
    (hv : v ≠ 0) : (y, ‖v‖⁻¹ • v) ∈ unitJets y₀ r := by
  refine ⟨hy, ?_⟩
  rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- The exponential data exist over every closed chart ball. -/
theorem exists_expData (F : ReversibleMetric n) (p : Sphere n) {y₀ : Coordinates n} {r : ℝ}
    (hball : closedBall y₀ r ⊆ (extChartAt (𝓡 n) p).target) :
    Nonempty (ExpData F p y₀ r) := by
  set K := annulusJets y₀ r (1 / 2) 2 with hKdef
  have hK : IsCompact K := annulusJets_isCompact y₀ r (1 / 2) 2
  have hKO : K ⊆ slitJets p := annulusJets_subset p (by norm_num) hball
  have hX : ContDiffOn ℝ ((2 : ℕ) + 1) (geodesicField F p) (slitJets p) := by
    have h := geodesicField_contDiffOn F p 3
    exact_mod_cast h
  obtain ⟨g, Φ, δ, τ, hδ, hτ, hg, hΦ, h0, hodeg, hδO, hgX, hstay⟩ :=
    Finsler.UniformFlowGlobal.exists_global_flow (slitJets_isOpen p) 2 hX hK hKO
  have hΦ3 : ContDiff ℝ 3 (fun q : (Coordinates n × Coordinates n) × ℝ => Φ q.1 q.2) := by
    exact_mod_cast hΦ
  set P : (Coordinates n × Coordinates n) × ℝ → Coordinates n := fun q => (Φ q.1 q.2).1 with hPdef
  have hP : ContDiff ℝ ((1 : ℕ) + 2) P := by
    have h : ContDiff ℝ 3 P := contDiff_fst.comp hΦ3
    exact_mod_cast h
  obtain ⟨R, hR, hRid⟩ := exists_smooth_remainder hP
  -- the time derivative at s = 0 is the velocity on the region where g is the geodesic field
  have htime : ∀ z ∈ K, timeDeriv P (z, 0) = z.2 := by
    intro z hz
    have hdP : DifferentiableAt ℝ P (z, 0) := (hP.differentiable (by norm_num)) _
    have h1 := hasDerivAt_time z hdP
    have h2 : HasDerivAt (fun s => P (z, s)) (g (Φ z 0)).1 0 :=
      (hasFDerivAt_fst (𝕜 := ℝ) (p := Φ z 0)).comp_hasDerivAt 0 (hodeg z 0)
    rw [h1.unique h2, h0, hgX z (self_subset_cthickening K hz)]
    rfl
  -- uniform bounds for R and DR on a compact set
  set Q : Set ((Coordinates n × Coordinates n) × ℝ) :=
    (closedBall y₀ r ×ˢ closedBall (0 : Coordinates n) 1) ×ˢ Icc (0 : ℝ) 1 with hQ
  have hQc : IsCompact Q :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod isCompact_Icc
  obtain ⟨A, hA⟩ := hQc.exists_bound_of_continuousOn hR.continuous.continuousOn
  obtain ⟨B, hB⟩ := hQc.exists_bound_of_continuousOn
    (hR.continuous_fderiv (by norm_num)).continuousOn
  set A' := max A 0
  set B' := max B 0
  have hpolar : ∀ y ∈ closedBall y₀ r, ∀ v : Coordinates n, ‖v‖ ≤ 1 → polar y v ∈ Q := by
    intro y hy v hv
    refine ⟨⟨hy, ?_⟩, ⟨norm_nonneg v, hv⟩⟩
    simpa using norm_polar_snd_le y v
  set c := 2 * A' + 3 * B' with hc
  have hc0 : 0 ≤ c := by positivity
  set ρ := min (min 1 τ / 2) (1 / (2 * c + 2)) with hρdef
  have hρpos : 0 < ρ := lt_min (by positivity) (by positivity)
  have hρ1 : ρ ≤ 1 := (min_le_left _ _).trans (by
    have := min_le_left (1 : ℝ) τ
    linarith)
  have hρτ : ρ < τ := lt_of_le_of_lt (min_le_left _ _) (by
    have := min_le_right (1 : ℝ) τ
    linarith)
  have hρc : c * ρ ≤ 1 / 2 := by
    have h1 : ρ ≤ 1 / (2 * c + 2) := min_le_right _ _
    have h2 : c * ρ ≤ c * (1 / (2 * c + 2)) := mul_le_mul_of_nonneg_left h1 hc0
    have h3 : c * (1 / (2 * c + 2)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  refine ⟨{
    Φ := Φ
    R := R
    τ := τ
    ρ := ρ
    τ_pos := hτ
    ρ_pos := hρpos
    ρ_le_one := hρ1
    ρ_lt_τ := hρτ
    smooth := hΦ3
    init := h0
    ode := ?_
    R_smooth := hR
    exp_eq := ?_
    lip := ?_ }⟩
  · intro z hz t ht
    have hzK : z ∈ K := unitJets_subset_annulus y₀ r hz
    have hin := hstay z hzK t ht
    refine ⟨hδO hin, ?_⟩
    have hd := hodeg z t
    rwa [hgX _ hin] at hd
  · intro y hy v hv
    have hz : (y, ‖v‖⁻¹ • v) ∈ K := unitJets_subset_annulus y₀ r (normalize_mem_unitJets hy hv)
    have h := hRid (y, ‖v‖⁻¹ • v) ‖v‖
    rw [htime _ hz] at h
    have hP0 : P ((y, ‖v‖⁻¹ • v), 0) = y := by
      simp only [hPdef, h0]
    rw [hP0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul] at h
    change _ = P ((y, ‖v‖⁻¹ • v), ‖v‖)
    rw [h]
    rfl
  · intro y hy
    exact rad_lipschitz hR
      (fun v hv => ((hA _ (hpolar y hy v hv)).trans (le_max_left _ _)))
      (fun v hv => ((hB _ (hpolar y hy v hv)).trans (le_max_left _ _))) hρ1 hρc

section ExpDataLemmas

variable {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

/-- Existence of an inverse image under the coordinate exponential map near y. -/
theorem exists_exp_inverse {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {z : Coordinates n}
    (hz : ‖z - y‖ ≤ D.ρ / 2) :
    ∃ v ∈ closedBall (0 : Coordinates n) D.ρ, y + v + rad D.R y v = z := by
  obtain ⟨v, hv, hve⟩ := Finsler.ContractionInverse.exists_preimage D.ρ_pos.le (rad_zero D.R y)
    (D.lip y hy) hz
  refine ⟨v, hv, ?_⟩
  rw [add_assoc, hve]
  abel

open Classical in
/-- The local inverse of the coordinate exponential map. -/
def expInv (y z : Coordinates n) : Coordinates n :=
  if h : ∃ v ∈ closedBall (0 : Coordinates n) D.ρ, y + v + rad D.R y v = z then h.choose else 0

theorem expInv_spec {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {z : Coordinates n}
    (hz : ‖z - y‖ ≤ D.ρ / 2) :
    expInv D y z ∈ closedBall (0 : Coordinates n) D.ρ ∧
      y + expInv D y z + rad D.R y (expInv D y z) = z := by
  have h := exists_exp_inverse D hy hz
  unfold expInv
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- Uniqueness of inverse images in the ball. -/
theorem eq_of_exp_eq {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {v w : Coordinates n}
    (hv : v ∈ closedBall (0 : Coordinates n) D.ρ) (hw : w ∈ closedBall (0 : Coordinates n) D.ρ)
    (h : y + v + rad D.R y v = y + w + rad D.R y w) : v = w := by
  have h2 := Finsler.ContractionInverse.norm_sub_le_two (D.lip y hy) hv hw
  have h3 : (v + rad D.R y v) - (w + rad D.R y w) = 0 := by
    have : y + (v + rad D.R y v) = y + (w + rad D.R y w) := by
      simpa only [add_assoc] using h
    rw [add_left_cancel this, sub_self]
  rw [h3, norm_zero, mul_zero] at h2
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)

theorem expInv_self {y : Coordinates n} (hy : y ∈ closedBall y₀ r) : expInv D y y = 0 := by
  have hz : ‖y - y‖ ≤ D.ρ / 2 := by
    rw [sub_self, norm_zero]
    exact (div_pos D.ρ_pos two_pos).le
  obtain ⟨hmem, hspec⟩ := expInv_spec D hy hz
  apply eq_of_exp_eq D hy hmem (mem_closedBall_self D.ρ_pos.le)
  rw [hspec, rad_zero, add_zero, add_zero]

/-- The inverse is at most twice the coordinate displacement. -/
theorem norm_expInv_le {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {z : Coordinates n}
    (hz : ‖z - y‖ ≤ D.ρ / 2) : ‖expInv D y z‖ ≤ 2 * ‖z - y‖ := by
  obtain ⟨hmem, hspec⟩ := expInv_spec D hy hz
  set v := expInv D y z with hvdef
  have h := Finsler.ContractionInverse.norm_sub_le_two (D.lip y hy) hmem
    (mem_closedBall_self D.ρ_pos.le)
  rw [sub_zero, rad_zero, add_zero, sub_zero] at h
  have hzv : v + rad D.R y v = z - y := by
    rw [← hspec]
    abel
  rwa [hzv] at h

theorem expInv_ne_zero {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {z : Coordinates n}
    (hz : ‖z - y‖ ≤ D.ρ / 2) (hne : z ≠ y) : expInv D y z ≠ 0 := by
  intro h0
  have hspec := (expInv_spec D hy hz).2
  rw [h0, rad_zero, add_zero, add_zero] at hspec
  exact hne hspec.symm

/-- Endpoint of the coordinate geodesic with initial jet (y, V(y,z)). -/
theorem geodesic_endpoint {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {z : Coordinates n}
    (hz : ‖z - y‖ ≤ D.ρ / 2) (hne : z ≠ y) :
    scaledGeodesic D.Φ (y, ‖expInv D y z‖⁻¹ • expInv D y z) ‖expInv D y z‖ 1 = z := by
  have hv := expInv_ne_zero D hy hz hne
  have h := D.exp_eq y hy (expInv D y z) hv
  rw [(expInv_spec D hy hz).2] at h
  simp only [scaledGeodesic, mul_one]
  exact h.symm

/-- A sphere path from the chart point y to the chart point z with energy F²(y, V(y,z)). -/
theorem exists_geodesic_path {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {z : Coordinates n}
    (hz : ‖z - y‖ ≤ D.ρ / 2) (hne : z ≠ y) :
    ∃ w : Space n, w ∈ pathsBetween n (inverseAmbient p y) (inverseAmbient p z) ∧
      pathEnergy F w = coordinateLagrangian F p (y, expInv D y z) := by
  set v := expInv D y z with hvdef
  have hv0 : v ≠ 0 := expInv_ne_zero D hy hz hne
  have hvρ : ‖v‖ ≤ D.ρ := by simpa using (expInv_spec D hy hz).1
  have hsτ : |‖v‖| < D.τ := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact lt_of_le_of_lt hvρ D.ρ_lt_τ
  have hs : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  set u : Coordinates n × Coordinates n := (y, ‖v‖⁻¹ • v) with hu
  have hmem : u ∈ unitJets y₀ r := normalize_mem_unitJets hy hv0
  have hΦ : ContDiff ℝ ((2 : ℕ) + 1) (fun q : (Coordinates n × Coordinates n) × ℝ => D.Φ q.1 q.2) := by
    exact_mod_cast D.smooth
  have hode := D.ode u hmem
  refine ⟨chartPath p (fun _ ht => scaledGeodesic_mem F p hode (abs_mul_lt hsτ ht))
      (continuousOn_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
      (hasDerivAt_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
      (deriv_continuousOn_of_C2 fun _ _ =>
        (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt), ?_, ?_⟩
  · have h := chartPath_mem p (fun _ ht => scaledGeodesic_mem F p hode (abs_mul_lt hsτ ht))
      (continuousOn_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
      (hasDerivAt_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
      (deriv_continuousOn_of_C2 fun _ _ =>
        (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt)
    rwa [scaledGeodesic_zero (D.init u), geodesic_endpoint D hy hz hne] at h
  · rw [pathEnergy_scaledGeodesic_eq F p hΦ (by norm_num) (D.init u) D.τ_pos hode hs hsτ]
    simp only [hu, smul_smul, mul_inv_cancel₀ hs, one_smul]

end ExpDataLemmas

end

end Finsler.CoordinateExpInverse
