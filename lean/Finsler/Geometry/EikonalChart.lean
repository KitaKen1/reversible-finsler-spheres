module

public import Finsler.Geometry.ExpInverseRegularity
public import Finsler.Analysis.GaussMomentumLocal
public import Finsler.Analysis.ChartPath
public import Finsler.Geometry.FundamentalInequality

/-! The eikonal identity in a sphere chart. Fix y and an endpoint z ≠ y close to it. Along the line
z + εζ, the inverse V(y, z + εζ) is C³ in ε, the coordinate geodesics c(ε,t) with initial jets
(y, V(y, z + εζ)) form a C³ family with fixed initial point, constant energy density and endpoints
z + εζ. The local momentum Gauss lemma gives
d/dε F²(y, V(y, z + εζ)) at 0 = (endpoint momentum)(ζ). With energy conservation and the fundamental
inequality pulled back to the chart, f(z) = F²(y, V(y,z)) is differentiable off the diagonal with
df(z)ζ ≤ 2√f(z)·√F²(z,ζ): the eikonal inequality in the chart. -/

@[expose] public section

namespace Finsler.EikonalChart

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.ExpInverseRegularity
open Finsler.RadialRemainder Finsler.GaussMomentum Finsler.GaussMomentumLocal Finsler.ChartPath
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r) {y : Coordinates n} (hy : y ∈ closedBall y₀ r) {z : Coordinates n}
  (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) (ζ : Coordinates n)

/-- The inverse along the line z + εζ. -/
def lineInv (y z ζ : Coordinates n) (ε : ℝ) : Coordinates n := expInv D y (z + ε • ζ)

/-- The family of coordinate geodesics with initial jets (y, V(y, z + εζ)). -/
def family (y z ζ : Coordinates n) (q : ℝ × ℝ) : Coordinates n :=
  (D.Φ (y, ‖lineInv D y z ζ q.1‖⁻¹ • lineInv D y z ζ q.1) (‖lineInv D y z ζ q.1‖ * q.2)).1

include hy hz hne in
theorem lineInv_contDiffAt : ContDiffAt ℝ 3 (lineInv D y z ζ) 0 := by
  have h := expInv_contDiffAt D hy hz hne
  have hl : ContDiffAt ℝ 3 (fun ε : ℝ => z + ε • ζ) 0 :=
    contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
  have h0 : z + (0 : ℝ) • ζ = z := by simp
  have h' : ContDiffAt ℝ 3 (fun z' => expInv D y z') (z + (0 : ℝ) • ζ) := by rwa [h0]
  exact h'.comp 0 hl

include hy hz hne in
theorem lineInv_zero_ne : lineInv D y z ζ 0 ≠ 0 := by
  unfold lineInv
  rw [zero_smul, add_zero]
  exact expInv_ne_zero D hy hz.le hne

include hy hz hne in
/-- Near ε = 0 the inverse is nonzero, inside the ball, and the endpoint stays in the domain. -/
theorem eventually_good :
    ∀ᶠ ε in 𝓝 (0 : ℝ), lineInv D y z ζ ε ≠ 0 ∧ ‖lineInv D y z ζ ε‖ < D.ρ ∧
      ‖z + ε • ζ - y‖ < D.ρ / 2 := by
  have hc : ContinuousAt (lineInv D y z ζ) 0 :=
    (lineInv_contDiffAt D hy hz hne ζ).continuousAt
  have h1 : ∀ᶠ ε in 𝓝 (0 : ℝ), lineInv D y z ζ ε ≠ 0 :=
    hc.eventually_ne (lineInv_zero_ne D hy hz hne ζ)
  have hρ0 : ‖lineInv D y z ζ 0‖ < D.ρ := by
    have h := norm_expInv_le D hy hz.le
    unfold lineInv
    rw [zero_smul, add_zero]
    linarith
  have h2 : ∀ᶠ ε in 𝓝 (0 : ℝ), ‖lineInv D y z ζ ε‖ < D.ρ :=
    (continuous_norm.continuousAt.comp hc).eventually (isOpen_Iio.mem_nhds hρ0)
  have hcl : ContinuousAt (fun ε : ℝ => ‖z + ε • ζ - y‖) 0 :=
    ((continuous_const.add (continuous_id.smul continuous_const)).sub continuous_const).norm.continuousAt
  have hz0 : ‖z + (0 : ℝ) • ζ - y‖ < D.ρ / 2 := by simpa using hz
  have h3 : ∀ᶠ ε in 𝓝 (0 : ℝ), ‖z + ε • ζ - y‖ < D.ρ / 2 :=
    hcl.eventually (isOpen_Iio.mem_nhds hz0)
  filter_upwards [h1, h2, h3] with ε a b c
  exact ⟨a, b, c⟩

include hy hz hne in
/-- The family is C³ near ε = 0, for every time. -/
theorem family_contDiffAt (t : ℝ) : ContDiffAt ℝ 3 (family D y z ζ) (0, t) := by
  have hw : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => lineInv D y z ζ q.1) (0, t) := by
    have h1 : ContDiffAt ℝ 3 (lineInv D y z ζ) ((0 : ℝ), t).1 := lineInv_contDiffAt D hy hz hne ζ
    have h2 : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => q.1) ((0 : ℝ), t) := contDiffAt_fst
    exact h1.comp ((0 : ℝ), t) h2
  have hw0 : lineInv D y z ζ (0, t).1 ≠ 0 := lineInv_zero_ne D hy hz hne ζ
  have hn : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => ‖lineInv D y z ζ q.1‖) (0, t) :=
    (contDiffAt_norm ℝ hw0).comp (0, t) hw
  have hinv : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => ‖lineInv D y z ζ q.1‖⁻¹) (0, t) :=
    hn.inv (norm_ne_zero_iff.mpr hw0)
  have harg : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
      ((y, ‖lineInv D y z ζ q.1‖⁻¹ • lineInv D y z ζ q.1), ‖lineInv D y z ζ q.1‖ * q.2)) (0, t) :=
    (contDiffAt_const.prodMk (hinv.smul hw)).prodMk (hn.mul contDiffAt_snd)
  have h := D.smooth.contDiffAt.comp (0, t) harg
  exact contDiffAt_fst.comp (0, t) h

/-- The endpoint velocity of the coordinate geodesic from y to z. -/
def endVel (y z : Coordinates n) : Coordinates n :=
  ‖expInv D y z‖ • (D.Φ (y, ‖expInv D y z‖⁻¹ • expInv D y z) ‖expInv D y z‖).2

theorem family_eq (ε t : ℝ) :
    family D y z ζ (ε, t) =
      scaledGeodesic D.Φ (y, ‖lineInv D y z ζ ε‖⁻¹ • lineInv D y z ζ ε) ‖lineInv D y z ζ ε‖ t :=
  rfl

include hy in
/-- The family is C³ at every (ε,t) whose endpoint lies in the open domain off the diagonal. -/
theorem family_contDiffAt_of {ε : ℝ} (hε : ‖z + ε • ζ - y‖ < D.ρ / 2) (hεne : z + ε • ζ ≠ y)
    (t : ℝ) : ContDiffAt ℝ 3 (family D y z ζ) (ε, t) := by
  have hwε : ContDiffAt ℝ 3 (lineInv D y z ζ) ε := by
    have h := expInv_contDiffAt D hy hε hεne
    have hl : ContDiffAt ℝ 3 (fun e : ℝ => z + e • ζ) ε :=
      contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    exact h.comp ε hl
  have hw0 : lineInv D y z ζ ε ≠ 0 := expInv_ne_zero D hy hε.le hεne
  have hw : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => lineInv D y z ζ q.1) (ε, t) := by
    have h1 : ContDiffAt ℝ 3 (lineInv D y z ζ) ((ε, t) : ℝ × ℝ).1 := hwε
    have h2 : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => q.1) (ε, t) := contDiffAt_fst
    exact h1.comp (ε, t) h2
  have hn : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => ‖lineInv D y z ζ q.1‖) (ε, t) :=
    (contDiffAt_norm ℝ hw0).comp (ε, t) hw
  have hinv : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => ‖lineInv D y z ζ q.1‖⁻¹) (ε, t) :=
    hn.inv (norm_ne_zero_iff.mpr hw0)
  have harg : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
      ((y, ‖lineInv D y z ζ q.1‖⁻¹ • lineInv D y z ζ q.1), ‖lineInv D y z ζ q.1‖ * q.2)) (ε, t) :=
    (contDiffAt_const.prodMk (hinv.smul hw)).prodMk (hn.mul contDiffAt_snd)
  have h := D.smooth.contDiffAt.comp (ε, t) harg
  exact contDiffAt_fst.comp (ε, t) h

include hy in
/-- The geodesic facts for an initial velocity v ≠ 0 inside the ball. -/
theorem geodesic_facts {v : Coordinates n} (hv : v ≠ 0) (hvρ : ‖v‖ < D.ρ) :
    let γ := scaledGeodesic D.Φ (y, ‖v‖⁻¹ • v) ‖v‖
    (∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 γ t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (extChartAt (𝓡 n) p).target) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv γ) t =
      spray (coordinateLagrangian F p) (curveJet γ t)) ∧
    γ 0 = y ∧ deriv γ 0 = v := by
  intro γ
  have hu := normalize_mem_unitJets hy hv
  have hode := D.ode _ hu
  have hs : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hsτ : |‖v‖| < D.τ := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact lt_trans hvρ D.ρ_lt_τ
  have hΦ : ContDiff ℝ ((2 : ℕ) + 1)
      (fun q : (Coordinates n × Coordinates n) × ℝ => D.Φ q.1 q.2) := by
    exact_mod_cast D.smooth
  refine ⟨fun t _ => (scaledGeodesic_contDiff hΦ (by norm_num) ‖v‖).contDiffAt,
    fun t ht => scaledGeodesic_mem F p hode (abs_mul_lt hsτ ht),
    fun t ht => deriv_scaledGeodesic_ne_zero F p hode hs (abs_mul_lt hsτ ht),
    fun t ht => scaledGeodesic_acc F p hode hs (abs_mul_lt hsτ ht), ?_, ?_⟩
  · exact scaledGeodesic_zero (D.init _) ‖v‖
  · rw [deriv_scaledGeodesic_zero F p hode (D.init _) D.τ_pos, smul_smul,
      mul_inv_cancel₀ hs, one_smul]

include hy hz hne in
/-- The eikonal identity along a line: the derivative of F²(y, V(y, z + εζ)) at ε = 0 is the
endpoint momentum applied to ζ. -/
theorem eikonal_line :
    HasDerivAt (fun ε => coordinateLagrangian F p (y, lineInv D y z ζ ε))
      (velocityTerm (coordinateLagrangian F p) (z, endVel D y z) ζ) 0 := by
  set c := family D y z ζ with hcdef
  set w := lineInv D y z ζ with hwdef
  have hgood := eventually_good D hy hz hne ζ
  have hne_ev : ∀ᶠ ε in 𝓝 (0 : ℝ), z + ε • ζ ≠ y := by
    have hcz : ContinuousAt (fun ε : ℝ => z + ε • ζ) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    have h0 : z + (0 : ℝ) • ζ ≠ y := by simpa using hne
    exact hcz.eventually_ne h0
  have hw0 : w 0 = expInv D y z := by simp [hwdef, lineInv]
  have hw0ne : w 0 ≠ 0 := lineInv_zero_ne D hy hz hne ζ
  have hw0ρ : ‖w 0‖ < D.ρ := by
    have h := norm_expInv_le D hy hz.le
    rw [hw0]
    linarith
  -- the curve at ε = 0
  obtain ⟨hC2, hmem, hvne, hacc, hγ0, hdγ0⟩ := geodesic_facts D hy hw0ne hw0ρ
  have hc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 3 c (0, t) :=
    fun t _ => family_contDiffAt D hy hz hne ζ t
  have hvel0 : ∀ t ∈ Icc (0 : ℝ) 1,
      vel c (0, t) = deriv (scaledGeodesic D.Φ (y, ‖w 0‖⁻¹ • w 0) ‖w 0‖) t := by
    intro t ht
    exact ((hasDerivAt_t ((hc t ht).differentiableAt (by norm_num))).deriv).symm
  have hL : ∀ t ∈ Icc (0 : ℝ) 1,
      ContDiffAt ℝ 2 (coordinateLagrangian F p) (c (0, t), vel c (0, t)) := by
    intro t ht
    rw [hvel0 t ht]
    have h := coordinateLagrangian_smoothAt_nonzero F p
      (z := (scaledGeodesic D.Φ (y, ‖w 0‖⁻¹ • w 0) ‖w 0‖ t,
        deriv (scaledGeodesic D.Φ (y, ‖w 0‖⁻¹ • w 0) ‖w 0‖) t)) (hmem t ht) (hvne t ht)
    exact h.of_le (by simp)
  have hres : ∀ t ∈ Icc (0 : ℝ) 1,
      residual (coordinateLagrangian F p) (fun s => c (0, s)) t = 0 := by
    intro t ht
    exact coordinate_residual_eq_zero F p (hC2 t ht) (hmem t ht) (hvne t ht) (hacc t ht)
  have hfix : ∀ᶠ ε in 𝓝 (0 : ℝ), c (ε, 0) = c (0, 0) := by
    refine Eventually.of_forall fun ε => ?_
    simp [hcdef, family, D.init]
  have hconst : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ ε in 𝓝 (0 : ℝ),
      coordinateLagrangian F p (c (ε, t), vel c (ε, t)) =
        coordinateLagrangian F p (c (ε, 0), vel c (ε, 0)) := by
    intro t ht
    filter_upwards [hgood, hne_ev] with ε hε hεne
    obtain ⟨hwε, hwρ, hεz⟩ := hε
    obtain ⟨hC2ε, hmemε, hvneε, haccε, -, -⟩ := geodesic_facts D hy hwε hwρ
    have hd : ∀ t' : ℝ, vel c (ε, t') =
        deriv (scaledGeodesic D.Φ (y, ‖w ε‖⁻¹ • w ε) ‖w ε‖) t' := fun t' =>
      ((hasDerivAt_t ((family_contDiffAt_of D hy ζ hεz hεne t').differentiableAt
        (by norm_num))).deriv).symm
    rw [hd t, hd 0]
    exact Finsler.ChartPath.density_const F p hC2ε hmemε hvneε haccε ht
  -- the derivative of the energy of the initial jets
  have hy_t : y ∈ (extChartAt (𝓡 n) p).target := by
    have h := hmem 0 (left_mem_Icc.mpr zero_le_one)
    rwa [hγ0] at h
  have hwd : HasDerivAt w (deriv w 0) 0 :=
    ((lineInv_contDiffAt D hy hz hne ζ).differentiableAt (by norm_num)).hasDerivAt
  have hLd : DifferentiableAt ℝ (coordinateLagrangian F p) (y, w 0) :=
    (coordinateLagrangian_contDiffAt_one F p (z := (y, w 0)) hy_t).differentiableAt (by norm_num)
  have hE : HasDerivAt (fun ε => coordinateLagrangian F p (y, w ε))
      (fderiv ℝ (coordinateLagrangian F p) (y, w 0) (0, deriv w 0)) 0 :=
    hLd.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const 0 y).prodMk hwd)
  have hD : HasDerivAt (fun ε => coordinateLagrangian F p (c (ε, 0), vel c (ε, 0)))
      (fderiv ℝ (coordinateLagrangian F p) (y, w 0) (0, deriv w 0)) 0 := by
    apply hE.congr_of_eventuallyEq
    filter_upwards [hgood, hne_ev] with ε hε hεne
    obtain ⟨hwε, hwρ, hεz⟩ := hε
    obtain ⟨-, -, -, -, hγε0, hdγε0⟩ := geodesic_facts D hy hwε hwρ
    have hvel : vel c (ε, 0) = deriv (scaledGeodesic D.Φ (y, ‖w ε‖⁻¹ • w ε) ‖w ε‖) 0 :=
      ((hasDerivAt_t ((family_contDiffAt_of D hy ζ hεz hεne 0).differentiableAt
        (by norm_num))).deriv).symm
    rw [hvel, hdγε0]
    change coordinateLagrangian F p (scaledGeodesic D.Φ (y, ‖w ε‖⁻¹ • w ε) ‖w ε‖ 0, w ε) = _
    rw [hγε0]
  have hgauss := endpoint_momentum_local hc hL hres hfix hconst hD
  -- identify the endpoint data
  have hc01 : c (0, 1) = z := by
    have h := geodesic_endpoint D hy hz.le hne
    rw [← hw0] at h
    exact h
  have hvel01 : vel c (0, 1) = endVel D y z := by
    rw [hvel0 1 (right_mem_Icc.mpr zero_le_one)]
    have hode := D.ode _ (normalize_mem_unitJets hy hw0ne)
    have hsτ : |‖w 0‖| < D.τ := by
      rw [abs_of_nonneg (norm_nonneg _)]
      exact lt_trans hw0ρ D.ρ_lt_τ
    rw [(scaledGeodesic_hasDerivAt F p hode (abs_mul_lt hsτ (right_mem_Icc.mpr zero_le_one))).deriv,
      mul_one, endVel, hw0]
  have hjac : jacobi c (0, 1) = ζ := by
    have h := hasDerivAt_ε ((hc 1 (right_mem_Icc.mpr zero_le_one)).differentiableAt (by norm_num))
    have hline : HasDerivAt (fun e : ℝ => z + e • ζ) ζ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add z
    have hev : (fun e => c (e, 1)) =ᶠ[𝓝 (0 : ℝ)] fun e => z + e • ζ := by
      filter_upwards [hgood, hne_ev] with ε hε hεne
      obtain ⟨hwε, hwρ, hεz⟩ := hε
      have hspec := (expInv_spec D hy hεz.le).2
      have hexp := D.exp_eq y hy (w ε) hwε
      change (D.Φ (y, ‖w ε‖⁻¹ • w ε) (‖w ε‖ * 1)).1 = _
      rw [mul_one, ← hexp]
      exact hspec
    exact h.unique (hline.congr_of_eventuallyEq hev)
  rw [hc01, hvel01, hjac] at hgauss
  rw [hgauss]
  exact hE

/-- The fundamental inequality for the coordinate Lagrangian. -/
theorem coordinate_velocityTerm_le (F : ReversibleMetric n) (p : Sphere n) {x η ζ : Coordinates n}
    (hx : x ∈ (extChartAt (𝓡 n) p).target) :
    velocityTerm (coordinateLagrangian F p) (x, η) ζ ≤
      2 * Real.sqrt (coordinateLagrangian F p (x, η)) *
        Real.sqrt (coordinateLagrangian F p (x, ζ)) := by
  have hφ : ContDiffAt ℝ 2 (inverseAmbient p) x := (inverseAmbient_smoothAt p hx).of_le (by simp)
  have hL : ContDiffAt ℝ 1 (Finsler.AmbientLagrangian.lagrangian F)
      (jetMap (inverseAmbient p) (x, η)) :=
    Finsler.AmbientEnergyRegularity.lagrangian_contDiffAt_one F
      (ne_zero_of_mem_unit_sphere (inverseSphere p x))
  have hpv := pullback_velocity hφ hL
  change velocityTerm (pullback (Finsler.AmbientLagrangian.lagrangian F) (inverseAmbient p))
      (x, η) ζ ≤ _
  rw [hpv]
  have hq : ‖inverseAmbient p x‖ = 1 := by simp [inverseAmbient]
  exact Finsler.FundamentalInequality.velocityDifferential_le F hq
    (inverseAmbient_fderiv_tangent p hx η) (inverseAmbient_fderiv_tangent p hx ζ)

include hy hz hne in
/-- Energy conservation along the geodesic from y to z. -/
theorem lagrangian_endVel :
    coordinateLagrangian F p (z, endVel D y z) = coordinateLagrangian F p (y, expInv D y z) := by
  have hV := expInv_ne_zero D hy hz.le hne
  have hVρ : ‖expInv D y z‖ < D.ρ := by
    have h := norm_expInv_le D hy hz.le
    linarith
  obtain ⟨hC2, hmem, hvne, hacc, hγ0, hdγ0⟩ := geodesic_facts D hy hV hVρ
  have h := Finsler.ChartPath.density_const F p hC2 hmem hvne hacc (right_mem_Icc.mpr zero_le_one)
  have hode := D.ode _ (normalize_mem_unitJets hy hV)
  have hsτ : |‖expInv D y z‖| < D.τ := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact lt_trans hVρ D.ρ_lt_τ
  have hd1 := (scaledGeodesic_hasDerivAt F p hode
    (abs_mul_lt hsτ (right_mem_Icc.mpr zero_le_one))).deriv
  have he1 := geodesic_endpoint D hy hz.le hne
  change coordinateLagrangian F p (curveJet _ 1) = coordinateLagrangian F p (curveJet _ 0) at h
  simp only [curveJet] at h
  rw [hd1, he1, mul_one, hγ0, hdγ0] at h
  exact h

/-- The energy function of the chart point z, for the fixed initial point y. -/
def energyFn (y z : Coordinates n) : ℝ := coordinateLagrangian F p (y, expInv D y z)

include hy hz hne in
/-- Off the diagonal, the energy function is differentiable with derivative the endpoint
momentum. -/
theorem energyFn_hasFDerivAt :
    HasFDerivAt (energyFn D y) (velocityTerm (coordinateLagrangian F p) (z, endVel D y z)) z := by
  have hV := expInv_contDiffAt D hy hz hne
  have hy_t : y ∈ (extChartAt (𝓡 n) p).target := by
    have h := (D.ode _ (normalize_mem_unitJets hy (expInv_ne_zero D hy hz.le hne)) 0
      (by simpa using D.τ_pos)).1.1
    simpa [D.init] using h
  have hLd : DifferentiableAt ℝ (coordinateLagrangian F p) (y, expInv D y z) :=
    (coordinateLagrangian_contDiffAt_one F p (z := (y, expInv D y z)) hy_t).differentiableAt
      (by norm_num)
  have hVd : HasFDerivAt (fun z' => expInv D y z') (fderiv ℝ (fun z' => expInv D y z') z) z :=
    (hV.differentiableAt (by norm_num)).hasFDerivAt
  have hpair : HasFDerivAt (fun z' => (y, expInv D y z'))
      ((0 : Coordinates n →L[ℝ] Coordinates n).prod (fderiv ℝ (fun z' => expInv D y z') z)) z :=
    (hasFDerivAt_const y z).prodMk hVd
  have hf : HasFDerivAt (energyFn D y)
      ((fderiv ℝ (coordinateLagrangian F p) (y, expInv D y z)).comp
        ((0 : Coordinates n →L[ℝ] Coordinates n).prod (fderiv ℝ (fun z' => expInv D y z') z))) z :=
    hLd.hasFDerivAt.comp z hpair
  have heq : (fderiv ℝ (coordinateLagrangian F p) (y, expInv D y z)).comp
      ((0 : Coordinates n →L[ℝ] Coordinates n).prod (fderiv ℝ (fun z' => expInv D y z') z)) =
      velocityTerm (coordinateLagrangian F p) (z, endVel D y z) := by
    refine ContinuousLinearMap.ext fun ζ => ?_
    have hline := eikonal_line D hy hz hne ζ
    have hl : HasDerivAt (fun ε : ℝ => z + ε • ζ) ζ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add z
    have hcomp := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hf hl (by simp)
    exact (hline.unique hcomp).symm
  rw [← heq]
  exact hf

include hy hz hne in
/-- The eikonal inequality in the chart, off the diagonal. -/
theorem energyFn_eikonal (ζ : Coordinates n) :
    fderiv ℝ (energyFn D y) z ζ ≤
      2 * Real.sqrt (energyFn D y z) * Real.sqrt (coordinateLagrangian F p (z, ζ)) := by
  rw [(energyFn_hasFDerivAt D hy hz hne).fderiv]
  have hV := expInv_ne_zero D hy hz.le hne
  have hVρ : ‖expInv D y z‖ < D.ρ := by
    have h := norm_expInv_le D hy hz.le
    linarith
  obtain ⟨-, hmem, -, -, -, -⟩ := geodesic_facts D hy hV hVρ
  have hz_t : z ∈ (extChartAt (𝓡 n) p).target := by
    have h := hmem 1 (right_mem_Icc.mpr zero_le_one)
    rwa [geodesic_endpoint D hy hz.le hne] at h
  have h := coordinate_velocityTerm_le F p (η := endVel D y z) (ζ := ζ) hz_t
  rwa [lagrangian_endVel D hy hz hne] at h

end

end Finsler.EikonalChart
