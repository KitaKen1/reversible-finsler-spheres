module

public import Finsler.Analysis.BoundaryMomentum
public import Finsler.Geometry.EnergyJointSmooth
public import Finsler.Geometry.SegmentContinuity

/-! The two-endpoint first variation of the actual short-segment energy. A joint family of
coordinate geodesics realizes arbitrary endpoint directions. The Euler equation and constant
energy density give final momentum minus initial momentum, with no assumed first-variation
formula or reversal identification. These are local formulas off the diagonal. -/

@[expose] public section

namespace Finsler.SegmentMomentum

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.CoordinateExp Finsler.CoordinateExpInverse Finsler.ExpInverseRegularity
open Finsler.EikonalChart Finsler.EnergyJointSmooth Finsler.ChartTransfer
open Finsler.GaussMomentum Finsler.BoundaryMomentum
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ} {F : ReversibleMetric n} {p : Sphere n} {y₀ : Coordinates n} {r : ℝ}
  (D : ExpData F p y₀ r)

/-- The joint chart energy of the segment from the first point to the second. -/
def jointEnergy (q : Coordinates n × Coordinates n) : ℝ := energyFn D q.1 q.2

/-- The boundary covector: terminal momentum on the second direction minus initial momentum on
the first direction. The Lagrangian is F², so no extra factor 1/2 is inserted. -/
def boundaryCovector (y z : Coordinates n) : (Coordinates n × Coordinates n) →L[ℝ] ℝ :=
  (velocityTerm (coordinateLagrangian F p) (z, endVel D y z)).comp
      (ContinuousLinearMap.snd ℝ (Coordinates n) (Coordinates n)) -
    (velocityTerm (coordinateLagrangian F p) (y, expInv D y z)).comp
      (ContinuousLinearMap.fst ℝ (Coordinates n) (Coordinates n))

/-- Vary both endpoints linearly and join them by the actual coordinate geodesic. -/
def endpointFamily (y z η ζ : Coordinates n) (q : ℝ × ℝ) : Coordinates n :=
  geo F D (y + q.1 • η) (z + q.1 • ζ) q.2

/-- Joint smoothness of the endpoint family wherever its endpoints are in the inverse domain. -/
theorem endpointFamily_contDiffAt {y z η ζ : Coordinates n} {ε : ℝ}
    (hy : y + ε • η ∈ ball y₀ r) (hz : ‖(z + ε • ζ) - (y + ε • η)‖ < D.ρ / 2)
    (hne : z + ε • ζ ≠ y + ε • η) (t : ℝ) :
    ContDiffAt ℝ 3 (endpointFamily D y z η ζ) (ε, t) := by
  have harg : ContDiffAt ℝ 3 (fun q : ℝ × ℝ => (y + q.1 • η, z + q.1 • ζ)) (ε, t) :=
    (contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const)).prodMk
      (contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const))
  have hV : ContDiffAt ℝ 3
      (fun q : ℝ × ℝ => expInv D (y + q.1 • η) (z + q.1 • ζ)) (ε, t) :=
    ContDiffAt.comp (g := fun w : Coordinates n × Coordinates n => expInv D w.1 w.2)
      (f := fun q : ℝ × ℝ => (y + q.1 • η, z + q.1 • ζ))
      (x := (ε, t)) (expInv_contDiffAt_joint D hy hz hne) harg
  have hV0 : expInv D (y + ε • η) (z + ε • ζ) ≠ 0 :=
    expInv_ne_zero D (ball_subset_closedBall hy) hz.le hne
  have hn : ContDiffAt ℝ 3
      (fun q : ℝ × ℝ => ‖expInv D (y + q.1 • η) (z + q.1 • ζ)‖) (ε, t) :=
    (contDiffAt_norm ℝ hV0).comp (ε, t) hV
  have hi := hn.inv (norm_ne_zero_iff.mpr hV0)
  have hflowarg : ContDiffAt ℝ 3 (fun q : ℝ × ℝ =>
      ((y + q.1 • η,
          ‖expInv D (y + q.1 • η) (z + q.1 • ζ)‖⁻¹ •
            expInv D (y + q.1 • η) (z + q.1 • ζ)),
        ‖expInv D (y + q.1 • η) (z + q.1 • ζ)‖ * q.2)) (ε, t) :=
    ((contDiffAt_const.add (contDiffAt_fst.smul contDiffAt_const)).prodMk
      (hi.smul hV)).prodMk (hn.mul contDiffAt_snd)
  exact contDiffAt_fst.comp (ε, t) (D.smooth.contDiffAt.comp (ε, t) hflowarg)

/-- The endpoint line stays in the inverse domain near its central off-diagonal pair. -/
theorem eventually_endpoints_good {y z : Coordinates n} (hy : y ∈ ball y₀ r)
    (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) (η ζ : Coordinates n) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), y + ε • η ∈ ball y₀ r ∧
      ‖(z + ε • ζ) - (y + ε • η)‖ < D.ρ / 2 ∧ z + ε • ζ ≠ y + ε • η := by
  have hyc : ContinuousAt (fun ε : ℝ => y + ε • η) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hzc : ContinuousAt (fun ε : ℝ => z + ε • ζ) 0 :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hy0 : y + (0 : ℝ) • η ∈ ball y₀ r := by simpa using hy
  have hz0 : ‖(z + (0 : ℝ) • ζ) - (y + (0 : ℝ) • η)‖ < D.ρ / 2 := by simpa using hz
  have hn0 : (z + (0 : ℝ) • ζ) - (y + (0 : ℝ) • η) ≠ 0 := by
    simpa only [zero_smul, add_zero, sub_ne_zero] using hne
  have h1 := hyc.eventually (isOpen_ball.mem_nhds hy0)
  have h2 := (hzc.sub hyc).norm.eventually (isOpen_Iio.mem_nhds hz0)
  have h3 := (hzc.sub hyc).eventually_ne hn0
  filter_upwards [h1, h2, h3] with ε hε1 hε2 hε3
  exact ⟨hε1, hε2, sub_ne_zero.mp hε3⟩

/-- The actual time derivative at the terminal point equals the endpoint velocity used in the
eikonal formula. -/
theorem geo_deriv_one {y z : Coordinates n} (hy : y ∈ closedBall y₀ r)
    (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) :
    deriv (geo F D y z) 1 = endVel D y z := by
  have hV := expInv_ne_zero D hy hz.le hne
  have hVρ : ‖expInv D y z‖ < D.ρ := by
    have h := norm_expInv_le D hy hz.le
    linarith
  have hode := D.ode _ (normalize_mem_unitJets hy hV)
  have hsτ : |‖expInv D y z‖| < D.τ := by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact lt_trans hVρ D.ρ_lt_τ
  simpa only [geo, endVel, mul_one] using (scaledGeodesic_hasDerivAt F p hode
    (abs_mul_lt hsτ (right_mem_Icc.mpr zero_le_one))).deriv

/-- The genuine Fréchet derivative of the two-endpoint chart energy is the boundary covector. -/
theorem jointEnergy_hasFDerivAt {y z : Coordinates n} (hy : y ∈ ball y₀ r)
    (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) :
    HasFDerivAt (jointEnergy D) (boundaryCovector D y z) (y, z) := by
  have hy' := ball_subset_closedBall hy
  have hV := expInv_ne_zero D hy' hz.le hne
  have hVρ : ‖expInv D y z‖ < D.ρ := by
    have h := norm_expInv_le D hy' hz.le
    linarith
  obtain ⟨hC2, hmem, hvne, hacc, hγ0, hdγ0⟩ := geodesic_facts D hy' hV hVρ
  have hyt : y ∈ (extChartAt (𝓡 n) p).target := by
    have h := hmem 0 (left_mem_Icc.mpr zero_le_one)
    rwa [hγ0] at h
  change geo F D y z 0 = y at hγ0
  change deriv (geo F D y z) 0 = expInv D y z at hdγ0
  have hs : ContDiffAt ℝ 3 (jointEnergy D) (y, z) :=
    energy_contDiffAt_joint D hy hz hne hyt
  have hf := (hs.differentiableAt (by norm_num)).hasFDerivAt
  have heq : fderiv ℝ (jointEnergy D) (y, z) = boundaryCovector D y z := by
    apply ContinuousLinearMap.ext
    rintro ⟨η, ζ⟩
    let c := endpointFamily D y z η ζ
    have hgood := eventually_endpoints_good D hy hz hne η ζ
    have hc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 3 c (0, t) := by
      intro t _
      apply endpointFamily_contDiffAt D
      · simpa using hy
      · simpa using hz
      · simpa using hne
    have hd : ∀ ε : ℝ, y + ε • η ∈ ball y₀ r →
        ‖(z + ε • ζ) - (y + ε • η)‖ < D.ρ / 2 → z + ε • ζ ≠ y + ε • η →
        ∀ t : ℝ, vel c (ε, t) = deriv (geo F D (y + ε • η) (z + ε • ζ)) t := by
      intro ε hεy hεz hεne t
      exact (hasDerivAt_t ((endpointFamily_contDiffAt D hεy hεz hεne t).differentiableAt
        (by norm_num))).deriv.symm
    have hd0 : ∀ t : ℝ, vel c (0, t) = deriv (geo F D y z) t := by
      intro t
      simpa using hd 0 (by simpa using hy) (by simpa using hz) (by simpa using hne) t
    have hc0 : ∀ t : ℝ, c (0, t) = geo F D y z t := by
      intro t
      simp [c, endpointFamily]
    have hL : ∀ t ∈ Icc (0 : ℝ) 1,
        ContDiffAt ℝ 2 (coordinateLagrangian F p) (c (0, t), vel c (0, t)) := by
      intro t ht
      rw [hc0 t, hd0 t]
      exact (coordinateLagrangian_smoothAt_nonzero F p
        (z := (geo F D y z t, deriv (geo F D y z) t)) (hmem t ht) (hvne t ht)).of_le
        (by simp)
    have hres : ∀ t ∈ Icc (0 : ℝ) 1,
        residual (coordinateLagrangian F p) (fun s => c (0, s)) t = 0 := by
      intro t ht
      have he : (fun s => c (0, s)) = geo F D y z := funext hc0
      rw [he]
      exact coordinate_residual_eq_zero F p (hC2 t ht) (hmem t ht) (hvne t ht) (hacc t ht)
    have hconst : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᶠ ε in 𝓝 (0 : ℝ),
        coordinateLagrangian F p (c (ε, t), vel c (ε, t)) =
          coordinateLagrangian F p (c (ε, 0), vel c (ε, 0)) := by
      intro t ht
      filter_upwards [hgood] with ε hε
      have hεy := ball_subset_closedBall hε.1
      have hv := expInv_ne_zero D hεy hε.2.1.le hε.2.2
      have hvρ : ‖expInv D (y + ε • η) (z + ε • ζ)‖ < D.ρ := by
        have h := norm_expInv_le D hεy hε.2.1.le
        linarith [hε.2.1]
      obtain ⟨hC, hT, hVn, hA, -, -⟩ := geodesic_facts D hεy hv hvρ
      rw [hd ε hε.1 hε.2.1 hε.2.2 t, hd ε hε.1 hε.2.1 hε.2.2 0]
      exact Finsler.ChartPath.density_const F p hC hT hVn hA ht
    have hinit : (fun ε => coordinateLagrangian F p (c (ε, 0), vel c (ε, 0))) =ᶠ[𝓝 (0 : ℝ)]
        fun ε => jointEnergy D (y + ε • η, z + ε • ζ) := by
      filter_upwards [hgood] with ε hε
      have hεy := ball_subset_closedBall hε.1
      have hv := expInv_ne_zero D hεy hε.2.1.le hε.2.2
      have hvρ : ‖expInv D (y + ε • η) (z + ε • ζ)‖ < D.ρ := by
        have h := norm_expInv_le D hεy hε.2.1.le
        linarith [hε.2.1]
      obtain ⟨-, -, -, -, h0, hv0⟩ := geodesic_facts D hεy hv hvρ
      change geo F D (y + ε • η) (z + ε • ζ) 0 = y + ε • η at h0
      change deriv (geo F D (y + ε • η) (z + ε • ζ)) 0 =
        expInv D (y + ε • η) (z + ε • ζ) at hv0
      rw [hd ε hε.1 hε.2.1 hε.2.2 0]
      change coordinateLagrangian F p
        (geo F D (y + ε • η) (z + ε • ζ) 0,
          deriv (geo F D (y + ε • η) (z + ε • ζ)) 0) = _
      rw [h0, hv0]
      rfl
    have hline : HasDerivAt (fun ε : ℝ => (y + ε • η, z + ε • ζ)) (η, ζ) 0 := by
      have h1 : HasDerivAt (fun ε : ℝ => y + ε • η) η 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add y
      have h2 : HasDerivAt (fun ε : ℝ => z + ε • ζ) ζ 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add z
      exact h1.prodMk h2
    have hE : HasDerivAt (fun ε : ℝ => jointEnergy D (y + ε • η, z + ε • ζ))
        (fderiv ℝ (jointEnergy D) (y, z) (η, ζ)) (0 : ℝ) :=
      hf.comp_hasDerivAt_of_eq 0 hline (by simp)
    have hb := boundary_momentum_local hc hL hres hconst (hE.congr_of_eventuallyEq hinit)
    have hJ0 : jacobi c (0, 0) = η := by
      have h := hasDerivAt_ε ((hc 0 (left_mem_Icc.mpr zero_le_one)).differentiableAt (by norm_num))
      have he : (fun ε => c (ε, 0)) = fun ε => y + ε • η := by
        funext ε
        simp [c, endpointFamily, geo, scaledGeodesic, D.init]
      rw [he] at h
      exact h.unique (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const η).const_add y)
    have hJ1 : jacobi c (0, 1) = ζ := by
      have h := hasDerivAt_ε ((hc 1 (right_mem_Icc.mpr zero_le_one)).differentiableAt (by norm_num))
      have he : (fun ε => c (ε, 1)) =ᶠ[𝓝 (0 : ℝ)] fun ε => z + ε • ζ := by
        filter_upwards [hgood] with ε hε
        exact geodesic_endpoint D (ball_subset_closedBall hε.1) hε.2.1.le hε.2.2
      have hzline : HasDerivAt (fun ε : ℝ => z + ε • ζ) ζ 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ζ).const_add z
      exact h.unique (hzline.congr_of_eventuallyEq he)
    have hγ1 : geo F D y z 1 = z := geodesic_endpoint D hy' hz.le hne
    rw [hc0 0, hc0 1, hd0 0, hd0 1, hγ0, hdγ0,
      hγ1, geo_deriv_one D hy' hz hne, hJ0, hJ1] at hb
    simpa [boundaryCovector] using hb.symm
  rw [← heq]
  exact hf

/-- The starting endpoint derivative is minus the actual initial momentum. -/
theorem energyFn_start_hasFDerivAt {y z : Coordinates n} (hy : y ∈ ball y₀ r)
    (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) :
    HasFDerivAt (fun y' => energyFn D y' z)
      (-velocityTerm (coordinateLagrangian F p) (y, expInv D y z)) y := by
  have hi : HasFDerivAt (fun y' : Coordinates n => (y', z))
      (ContinuousLinearMap.inl ℝ (Coordinates n) (Coordinates n)) y :=
    hasFDerivAt_prodMk_left y z
  have h := (jointEnergy_hasFDerivAt D hy hz hne).comp y hi
  change HasFDerivAt (fun y' => energyFn D y' z)
    ((boundaryCovector D y z).comp (ContinuousLinearMap.inl ℝ (Coordinates n) (Coordinates n))) y at h
  have he : (boundaryCovector D y z).comp
      (ContinuousLinearMap.inl ℝ (Coordinates n) (Coordinates n)) =
      -velocityTerm (coordinateLagrangian F p) (y, expInv D y z) := by
    ext η
    simp [boundaryCovector]
  rw [he] at h
  exact h

/-- Along arbitrary differentiable endpoint curves, the first variation is the boundary momentum
difference. Only the central pair must lie in the short-segment domain. -/
theorem energyFn_hasDerivAt_endpoints {y z : Coordinates n} (hy : y ∈ ball y₀ r)
    (hz : ‖z - y‖ < D.ρ / 2) (hne : z ≠ y) {a b : ℝ → Coordinates n} {η ζ : Coordinates n}
    {s : ℝ} (ha : HasDerivAt a η s) (hb : HasDerivAt b ζ s) (hay : a s = y) (hbz : b s = z) :
    HasDerivAt (fun ε => energyFn D (a ε) (b ε))
      (velocityTerm (coordinateLagrangian F p) (z, endVel D y z) ζ -
        velocityTerm (coordinateLagrangian F p) (y, expInv D y z) η) s := by
  have hpair : HasFDerivAt (jointEnergy D) (boundaryCovector D y z) (a s, b s) := by
    rw [hay, hbz]
    exact jointEnergy_hasFDerivAt D hy hz hne
  have h : HasDerivAt (jointEnergy D ∘ fun ε => (a ε, b ε))
      (boundaryCovector D y z (η, ζ)) s := hpair.comp_hasDerivAt s (ha.prodMk hb)
  simpa [Function.comp_def, jointEnergy, boundaryCovector] using h

end

end Finsler.SegmentMomentum
