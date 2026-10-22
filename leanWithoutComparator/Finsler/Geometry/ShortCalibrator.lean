module

public import Finsler.Geometry.EikonalChart
public import Finsler.Geometry.SprayEnergy

/-! The chart energy function is C¹ through the diagonal. For the fixed initial point y the
energy f(z) = F²(y, V(y,z)) vanishes to second order at z = y (F² is quadratic and ‖V‖ ≤ 2‖z − y‖),
so f is differentiable there with derivative 0; off the diagonal its derivative is the endpoint
momentum, which is bounded by C‖endpoint velocity‖ ≤ CM‖V‖ and hence tends to 0 at y. So f is C¹
on the ball of radius ρ/2 around y and satisfies the eikonal inequality there. -/

@[expose] public section

namespace Finsler.ShortCalibrator

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.ExpInverseRegularity
open Finsler.RadialRemainder Finsler.EikonalChart
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

/-- A local quadratic criterion for Fréchet differentiability. -/
theorem hasFDerivAt_of_eventually_quadratic {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → G} {L : E →L[ℝ] G} {x : E} {K : ℝ}
    (h : ∀ᶠ d in 𝓝 (0 : E), ‖f (x + d) - f x - L d‖ ≤ K * ‖d‖ ^ 2) : HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun d => f (x + d) - f x - L d) =O[𝓝 0] fun d => ‖d‖ ^ 2 := by
    apply Asymptotics.IsBigO.of_bound K
    filter_upwards [h] with d hd
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hd
  exact hO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num))

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

theorem energyFn_self {y : Coordinates n} (hy : y ∈ closedBall y₀ r) : energyFn D y y = 0 := by
  unfold energyFn
  rw [expInv_self D hy]
  have h := coordinateLagrangian_velocity_smul F p y 0 0
  simpa using h

/-- The endpoint velocity is bounded by a multiple of the initial velocity. -/
theorem exists_endVel_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ closedBall y₀ r, ∀ z : Coordinates n, ‖z - y‖ ≤ D.ρ / 2 →
      ‖endVel D y z‖ ≤ M * ‖expInv D y z‖ := by
  set Kc : Set ((Coordinates n × Coordinates n) × ℝ) := unitJets y₀ r ×ˢ Icc (0 : ℝ) D.ρ
  have hKc : IsCompact Kc := (unitJets_isCompact y₀ r).prod isCompact_Icc
  have hcont : Continuous fun q : (Coordinates n × Coordinates n) × ℝ => ‖(D.Φ q.1 q.2).2‖ :=
    (continuous_snd.comp D.smooth.continuous).norm
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y hy z hz => ?_⟩
  set V := expInv D y z
  rcases eq_or_ne V 0 with h0 | h0
  · have h0' : expInv D y z = 0 := h0
    simp only [endVel, h0', norm_zero, zero_smul]
    exact mul_nonneg (le_max_right _ _) (norm_nonneg _)
  · have hu := normalize_mem_unitJets hy h0
    have hVρ : ‖V‖ ≤ D.ρ := by simpa using (expInv_spec D hy hz).1
    have hb := hM ((y, ‖V‖⁻¹ • V), ‖V‖) ⟨hu, ⟨norm_nonneg _, hVρ⟩⟩
    rw [Real.norm_of_nonneg (norm_nonneg _)] at hb
    unfold endVel
    rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hb.trans (le_max_left _ _)) (norm_nonneg _)

section Diagonal

variable {y : Coordinates n} (hy : y ∈ closedBall y₀ r)
  (hyt : y ∈ (extChartAt (𝓡 n) p).target)

include hyt in
/-- A local quadratic bound for the coordinate Lagrangian near y. -/
theorem exists_lagrangian_quadratic :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ closedBall y ε ⊆ (extChartAt (𝓡 n) p).target ∧
      ∀ x ∈ closedBall y ε, ∀ w : Coordinates n,
        ‖velocityTerm (coordinateLagrangian F p) (x, w)‖ ≤ C * ‖w‖ ∧
        coordinateLagrangian F p (x, w) ≤ C / 2 * ‖w‖ ^ 2 := by
  obtain ⟨ε, C, hε, hC, hsub, hb⟩ := exists_coordinate_partial_bounds F p hyt
  refine ⟨ε, C, hε, hC, hsub, fun x hx w => ⟨(hb x hx w).2, ?_⟩⟩
  have hd : DifferentiableAt ℝ (coordinateLagrangian F p) (x, w) :=
    (coordinateLagrangian_contDiffAt_one F p (z := (x, w)) (hsub hx)).differentiableAt
      (by norm_num)
  have he := Finsler.SprayEnergy.velocityTerm_self (coordinateLagrangian F p)
    (fun y' w' r => coordinateLagrangian_velocity_smul F p y' r w') hd
  have h1 : velocityTerm (coordinateLagrangian F p) (x, w) w ≤ C * ‖w‖ * ‖w‖ :=
    (le_abs_self _).trans ((ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hb x hx w).2 (norm_nonneg _)))
  change velocityTerm (coordinateLagrangian F p) (x, w) w = 2 * coordinateLagrangian F p (x, w)
    at he
  nlinarith

include hy hyt in
/-- At the diagonal the energy function is differentiable with derivative zero. -/
theorem energyFn_hasFDerivAt_self : HasFDerivAt (energyFn D y) (0 : Coordinates n →L[ℝ] ℝ) y := by
  obtain ⟨ε, C, hε, hC, hsub, hb⟩ := exists_lagrangian_quadratic (F := F) hyt
  apply hasFDerivAt_of_eventually_quadratic (K := 2 * C)
  have hρ : (0 : ℝ) < D.ρ / 2 := by have := D.ρ_pos; positivity
  filter_upwards [Metric.ball_mem_nhds (0 : Coordinates n) hρ] with d hd
  have hd' : ‖(y + d) - y‖ ≤ D.ρ / 2 := by
    rw [add_sub_cancel_left]
    exact (mem_ball_zero_iff.mp hd).le
  have hV := norm_expInv_le D hy hd'
  rw [add_sub_cancel_left] at hV
  rw [energyFn_self D hy, sub_zero, zero_apply, sub_zero]
  unfold energyFn
  have hL0 : 0 ≤ coordinateLagrangian F p (y, expInv D y (y + d)) := by
    change 0 ≤ Finsler.AmbientLagrangian.lagrangian F _
    exact sq_nonneg _
  rw [Real.norm_of_nonneg hL0]
  have h1 := (hb y (mem_closedBall_self hε.le) (expInv D y (y + d))).2
  have h2 : ‖expInv D y (y + d)‖ ^ 2 ≤ (2 * ‖d‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hV 2
  nlinarith

end Diagonal

section Derivative

open Classical in
/-- The derivative of the energy function: zero on the diagonal, the endpoint momentum off it. -/
def energyDeriv (y z : Coordinates n) : Coordinates n →L[ℝ] ℝ :=
  if z = y then 0 else velocityTerm (coordinateLagrangian F p) (z, endVel D y z)

variable {y : Coordinates n} (hy : y ∈ closedBall y₀ r)
  (hyt : y ∈ (extChartAt (𝓡 n) p).target)

theorem norm_sub_lt_of_mem_ball {z : Coordinates n} (hz : z ∈ ball y (D.ρ / 2)) :
    ‖z - y‖ < D.ρ / 2 := by
  rwa [mem_ball, dist_eq_norm] at hz

include hy hyt in
theorem energyFn_hasFDerivAt_ball {z : Coordinates n} (hz : z ∈ ball y (D.ρ / 2)) :
    HasFDerivAt (energyFn D y) (energyDeriv D y z) z := by
  unfold energyDeriv
  by_cases h : z = y
  · subst h
    simp only [ite_true]
    exact energyFn_hasFDerivAt_self D hy hyt
  · simp only [h, ite_false]
    exact energyFn_hasFDerivAt D hy (norm_sub_lt_of_mem_ball D hz) h

include hy in
theorem endpoint_mem_target {z : Coordinates n} (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) :
    z ∈ (extChartAt (𝓡 n) p).target := by
  have hV := expInv_ne_zero D hy hz.le hne
  have hVρ : ‖expInv D y z‖ < D.ρ := by
    have h := norm_expInv_le D hy hz.le
    linarith
  obtain ⟨-, hmem, -, -, -, -⟩ := geodesic_facts D hy hV hVρ
  have h := hmem 1 (right_mem_Icc.mpr zero_le_one)
  rwa [geodesic_endpoint D hy hz.le hne] at h

include hy in
/-- Off the diagonal the derivative is continuous. -/
theorem energyDeriv_continuousAt_of_ne {z : Coordinates n} (hz : ‖z - y‖ < D.ρ / 2)
    (hne : z ≠ y) : ContinuousAt (energyDeriv D y) z := by
  have hev : (fun z' => velocityTerm (coordinateLagrangian F p) (z', endVel D y z')) =ᶠ[𝓝 z]
      energyDeriv D y := by
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds (show z ∈ ({y} : Set _)ᶜ from hne)]
      with z' hz'
    have hz'' : z' ≠ y := hz'
    unfold energyDeriv
    simp only [hz'', ite_false]
  apply ContinuousAt.congr _ hev
  -- continuity of the endpoint velocity
  have hV : ContinuousAt (fun z' => expInv D y z') z :=
    (expInv_contDiffAt D hy hz hne).continuousAt
  have hV0 : expInv D y z ≠ 0 := expInv_ne_zero D hy hz.le hne
  have hn : ContinuousAt (fun z' => ‖expInv D y z'‖) z := hV.norm
  have hinv : ContinuousAt (fun z' => ‖expInv D y z'‖⁻¹) z :=
    hn.inv₀ (norm_ne_zero_iff.mpr hV0)
  have hΦc : Continuous fun q : (Coordinates n × Coordinates n) × ℝ => D.Φ q.1 q.2 :=
    D.smooth.continuous
  have harg : ContinuousAt (fun z' =>
      ((y, ‖expInv D y z'‖⁻¹ • expInv D y z'), ‖expInv D y z'‖)) z :=
    (continuousAt_const.prodMk (hinv.smul hV)).prodMk hn
  have hend : ContinuousAt (endVel D y) z := by
    unfold endVel
    exact hn.smul (continuous_snd.continuousAt.comp (hΦc.continuousAt.comp harg))
  -- continuity of the velocity term
  have hzt := endpoint_mem_target D hy hz hne
  have hL1 : ContDiffAt ℝ 1 (coordinateLagrangian F p) (z, endVel D y z) :=
    coordinateLagrangian_contDiffAt_one F p (z := (z, endVel D y z)) hzt
  have hfd : ContinuousAt (fderiv ℝ (coordinateLagrangian F p)) (z, endVel D y z) :=
    hL1.continuousAt_fderiv (by norm_num)
  have hvt : ContinuousAt (velocityTerm (coordinateLagrangian F p)) (z, endVel D y z) := by
    rw [Finsler.LagrangianSpray.velocityTerm_eq]
    exact Finsler.LagrangianSpray.restrictVel.continuous.continuousAt.comp hfd
  exact ContinuousAt.comp (f := fun z' : Coordinates n => (z', endVel D y z')) hvt
    (continuousAt_id.prodMk hend)

end Derivative

section C1

variable {y : Coordinates n} (hy : y ∈ closedBall y₀ r)
  (hyt : y ∈ (extChartAt (𝓡 n) p).target)

include hy hyt in
/-- At the diagonal the derivative tends to zero. -/
theorem energyDeriv_continuousAt_self : ContinuousAt (energyDeriv D y) y := by
  obtain ⟨ε, C, hε, hC, hsub, hb⟩ := exists_lagrangian_quadratic (F := F) hyt
  obtain ⟨M, hM0, hM⟩ := exists_endVel_bound D
  have hy0 : energyDeriv D y y = 0 := by
    unfold energyDeriv
    simp
  rw [ContinuousAt, hy0, tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have hρ : (0 : ℝ) < min (D.ρ / 2) ε := lt_min (by have := D.ρ_pos; positivity) hε
  have hlim : Tendsto (fun z : Coordinates n => 2 * C * M * ‖z - y‖) (𝓝 y) (𝓝 0) := by
    have h : Tendsto (fun z : Coordinates n => ‖z - y‖) (𝓝 y) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp (tendsto_id (x := 𝓝 y))
    simpa using h.const_mul (2 * C * M)
  apply squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) _ hlim
  filter_upwards [Metric.ball_mem_nhds y hρ] with z hz
  have hz1 : ‖z - y‖ < D.ρ / 2 := by
    rw [mem_ball, dist_eq_norm] at hz
    exact lt_of_lt_of_le hz (min_le_left _ _)
  have hz2 : z ∈ closedBall y ε := by
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_closedBall, dist_eq_norm]
    exact (lt_of_lt_of_le hz (min_le_right _ _)).le
  unfold energyDeriv
  by_cases h : z = y
  · subst h
    simp only [ite_true, norm_zero, sub_self]
    positivity
  · simp only [h, ite_false]
    have h1 := (hb z hz2 (endVel D y z)).1
    have h2 := hM y hy z hz1.le
    have h3 := norm_expInv_le D hy hz1.le
    calc ‖velocityTerm (coordinateLagrangian F p) (z, endVel D y z)‖
        ≤ C * ‖endVel D y z‖ := h1
      _ ≤ C * (M * ‖expInv D y z‖) := mul_le_mul_of_nonneg_left h2 hC.le
      _ ≤ C * (M * (2 * ‖z - y‖)) := by gcongr
      _ = 2 * C * M * ‖z - y‖ := by ring

include hy hyt in
theorem energyDeriv_continuousOn : ContinuousOn (energyDeriv D y) (ball y (D.ρ / 2)) := by
  intro z hz
  by_cases h : z = y
  · subst h
    exact (energyDeriv_continuousAt_self D hy hyt).continuousWithinAt
  · exact (energyDeriv_continuousAt_of_ne D hy (norm_sub_lt_of_mem_ball D hz) h).continuousWithinAt

include hy hyt in
/-- The energy function is C¹ on the ball of radius ρ/2 around y. -/
theorem energyFn_contDiffOn : ContDiffOn ℝ 1 (energyFn D y) (ball y (D.ρ / 2)) := by
  have h1 : ((1 : ℕ) : WithTop ℕ∞) = (0 : ℕ) + 1 := by norm_num
  rw [show (1 : WithTop ℕ∞) = ((0 : ℕ) : WithTop ℕ∞) + 1 by norm_num,
    contDiffOn_succ_iff_fderiv_of_isOpen isOpen_ball]
  refine ⟨fun z hz => (energyFn_hasFDerivAt_ball D hy hyt hz).differentiableAt.differentiableWithinAt,
    by simp, ?_⟩
  rw [show ((0 : ℕ) : WithTop ℕ∞) = 0 by norm_num, contDiffOn_zero]
  exact (energyDeriv_continuousOn D hy hyt).congr fun z hz =>
    (energyFn_hasFDerivAt_ball D hy hyt hz).fderiv

include hy hyt in
/-- The eikonal inequality on the whole ball, including the diagonal. -/
theorem energyFn_eikonal_ball {z : Coordinates n} (hz : z ∈ ball y (D.ρ / 2)) (ζ : Coordinates n) :
    fderiv ℝ (energyFn D y) z ζ ≤
      2 * Real.sqrt (energyFn D y z) * Real.sqrt (coordinateLagrangian F p (z, ζ)) := by
  by_cases h : z = y
  · subst h
    rw [(energyFn_hasFDerivAt_self D hy hyt).fderiv, zero_apply]
    positivity
  · exact energyFn_eikonal D hy (norm_sub_lt_of_mem_ball D hz) h ζ

end C1

end

end Finsler.ShortCalibrator
