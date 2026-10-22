module

public import Finsler.Geometry.CoordinateSpray
public import Finsler.Analysis.UniformFlow
public import Finsler.Analysis.ChartPath

/-! Uniformly defined coordinate geodesics. The coordinate geodesic field is smooth on jets with
nonzero velocity, so on the compact set of unit jets over a closed chart ball it has a uniform-time
flow. Its position component is a C² coordinate geodesic for |t| < τ. Rescaling by s = |v| and
the quadratic homogeneity of the spray give, for every small nonzero v, a coordinate geodesic
with initial jet (y, v) on a neighborhood of [0,1]; its actual H¹ sphere path has energy F²(y,v). -/

@[expose] public section

namespace Finsler.CoordinateExp

open Finsler.SphereGeometry Finsler.Geometry Finsler.EulerCovariance Finsler.LagrangianSpray
open Finsler.SphereCoordinateEuler Finsler.CoordinateEnergyRegularity Finsler.CoordinateSpray
open Finsler.UniformFlow Finsler.ChartPath Finsler.SobolevSpherePath Finsler.SphereDistance
open Set Filter Metric
open scoped Topology ContDiff Manifold

noncomputable section

variable {n : ℕ}

/-- Unit jets over a closed chart ball. -/
def unitJets (y₀ : Coordinates n) (r : ℝ) : Set (Coordinates n × Coordinates n) :=
  closedBall y₀ r ×ˢ sphere (0 : Coordinates n) 1

theorem unitJets_isCompact (y₀ : Coordinates n) (r : ℝ) : IsCompact (unitJets y₀ r) :=
  (isCompact_closedBall _ _).prod (isCompact_sphere _ _)

theorem unitJets_subset (p : Sphere n) {y₀ : Coordinates n} {r : ℝ}
    (hr : closedBall y₀ r ⊆ (extChartAt (𝓡 n) p).target) : unitJets y₀ r ⊆ slitJets p := by
  rintro z ⟨hz1, hz2⟩
  refine ⟨hr hz1, ?_⟩
  intro h0
  rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hz2
  exact zero_ne_one hz2

/-- A uniform-time geodesic flow on unit jets over a chart ball. -/
theorem exists_uniform_geodesic_flow (F : ReversibleMetric n) (p : Sphere n)
    {y₀ : Coordinates n} {r : ℝ} (hr : closedBall y₀ r ⊆ (extChartAt (𝓡 n) p).target) (k : ℕ) :
    ∃ Φ : Coordinates n × Coordinates n → ℝ → Coordinates n × Coordinates n, ∃ τ : ℝ, 0 < τ ∧
      ContDiff ℝ (k + 1) (fun q : (Coordinates n × Coordinates n) × ℝ => Φ q.1 q.2) ∧
      (∀ z, Φ z 0 = z) ∧
      ∀ z ∈ unitJets y₀ r, ∀ t : ℝ, |t| < τ →
        Φ z t ∈ slitJets p ∧ HasDerivAt (Φ z) (geodesicField F p (Φ z t)) t :=
  exists_uniform_flow (slitJets_isOpen p) k (geodesicField_contDiffOn F p (k + 1))
    (unitJets_isCompact y₀ r) (unitJets_subset p hr)

section Geodesic

variable (F : ReversibleMetric n) (p : Sphere n)
  {Φ : Coordinates n × Coordinates n → ℝ → Coordinates n × Coordinates n} {τ : ℝ} {k : ℕ}
  (hΦ : ContDiff ℝ (k + 1) (fun q : (Coordinates n × Coordinates n) × ℝ => Φ q.1 q.2))
  {z : Coordinates n × Coordinates n}
  (hode : ∀ t : ℝ, |t| < τ → Φ z t ∈ slitJets p ∧ HasDerivAt (Φ z) (geodesicField F p (Φ z t)) t)

/-- The geodesic through the jet z, rescaled to initial velocity s · z.2. -/
def scaledGeodesic (Φ : Coordinates n × Coordinates n → ℝ → Coordinates n × Coordinates n)
    (z : Coordinates n × Coordinates n) (s t : ℝ) : Coordinates n :=
  (Φ z (s * t)).1

include hode in
theorem scaledGeodesic_hasDerivAt {s t : ℝ} (hst : |s * t| < τ) :
    HasDerivAt (scaledGeodesic Φ z s) (s • (Φ z (s * t)).2) t := by
  have h1 := (hode (s * t) hst).2
  have h2 : HasDerivAt (fun u : ℝ => s * u) s t := by
    simpa using (hasDerivAt_id t).const_mul s
  have h3 := h1.scomp t h2
  have h4 := (hasFDerivAt_fst (𝕜 := ℝ) (p := Φ z (s * t))).comp_hasDerivAt t h3
  exact h4

include hode in
theorem scaledVelocity_hasDerivAt {s t : ℝ} (hst : |s * t| < τ) :
    HasDerivAt (fun u => s • (Φ z (s * u)).2)
      (s • s • spray (coordinateLagrangian F p) (Φ z (s * t))) t := by
  have h1 := (hode (s * t) hst).2
  have h2 : HasDerivAt (fun u : ℝ => s * u) s t := by
    simpa using (hasDerivAt_id t).const_mul s
  have h3 := h1.scomp t h2
  have h4 := (hasFDerivAt_snd (𝕜 := ℝ) (p := Φ z (s * t))).comp_hasDerivAt t h3
  have h5 := h4.const_smul s
  exact h5

include hode in
theorem deriv_scaledGeodesic_eventually {s t : ℝ} (hst : |s * t| < τ) :
    deriv (scaledGeodesic Φ z s) =ᶠ[𝓝 t] fun u => s • (Φ z (s * u)).2 := by
  have hopen : IsOpen {u : ℝ | |s * u| < τ} :=
    isOpen_lt ((continuous_const.mul continuous_id).abs) continuous_const
  filter_upwards [hopen.mem_nhds hst] with u hu
  exact (scaledGeodesic_hasDerivAt F p hode hu).deriv

include hode in
theorem scaledGeodesic_mem {s t : ℝ} (hst : |s * t| < τ) :
    scaledGeodesic Φ z s t ∈ (extChartAt (𝓡 n) p).target :=
  (hode (s * t) hst).1.1

include hode in
theorem deriv_scaledGeodesic_ne_zero {s t : ℝ} (hs : s ≠ 0) (hst : |s * t| < τ) :
    deriv (scaledGeodesic Φ z s) t ≠ 0 := by
  rw [(scaledGeodesic_hasDerivAt F p hode hst).deriv]
  exact smul_ne_zero hs (hode (s * t) hst).1.2

include hode in
/-- The rescaled curve is a coordinate geodesic: its acceleration is the spray of its jet. -/
theorem scaledGeodesic_acc {s t : ℝ} (hs : s ≠ 0) (hst : |s * t| < τ) :
    deriv (deriv (scaledGeodesic Φ z s)) t =
      spray (coordinateLagrangian F p) (curveJet (scaledGeodesic Φ z s) t) := by
  rw [(deriv_scaledGeodesic_eventually F p hode hst).deriv_eq,
    (scaledVelocity_hasDerivAt F p hode hst).deriv]
  have hjet : curveJet (scaledGeodesic Φ z s) t = ((Φ z (s * t)).1, s • (Φ z (s * t)).2) := by
    unfold curveJet
    rw [(scaledGeodesic_hasDerivAt F p hode hst).deriv]
    rfl
  rw [hjet, coordinate_spray_smul F p (hode (s * t) hst).1.1 (hode (s * t) hst).1.2 hs, smul_smul,
    sq]

include hΦ in
theorem scaledGeodesic_contDiff (hk : 1 ≤ k) (s : ℝ) : ContDiff ℝ 2 (scaledGeodesic Φ z s) := by
  have h1 : ContDiff ℝ (k + 1) (fun t : ℝ => Φ z (s * t)) :=
    hΦ.comp (contDiff_const.prodMk (contDiff_const.mul contDiff_id))
  have h2 : ContDiff ℝ (k + 1) (fun t : ℝ => (Φ z (s * t)).1) := contDiff_fst.comp h1
  exact h2.of_le (by exact_mod_cast (by omega : 2 ≤ k + 1))

theorem scaledGeodesic_zero (h0 : Φ z 0 = z) (s : ℝ) : scaledGeodesic Φ z s 0 = z.1 := by
  simp [scaledGeodesic, h0]

include hode in
theorem deriv_scaledGeodesic_zero (h0 : Φ z 0 = z) {s : ℝ} (hτ : 0 < τ) :
    deriv (scaledGeodesic Φ z s) 0 = s • z.2 := by
  rw [(scaledGeodesic_hasDerivAt F p hode (by simpa using hτ)).deriv, mul_zero, h0]

end Geodesic

section Energy

variable (F : ReversibleMetric n) (p : Sphere n)
  {Φ : Coordinates n × Coordinates n → ℝ → Coordinates n × Coordinates n} {τ : ℝ} {k : ℕ}
  (hΦ : ContDiff ℝ (k + 1) (fun q : (Coordinates n × Coordinates n) × ℝ => Φ q.1 q.2))
  (hk : 1 ≤ k) {z : Coordinates n × Coordinates n} (h0 : Φ z 0 = z) (hτ : 0 < τ)
  (hode : ∀ t : ℝ, |t| < τ → Φ z t ∈ slitJets p ∧ HasDerivAt (Φ z) (geodesicField F p (Φ z t)) t)
  {s : ℝ} (hs : s ≠ 0) (hsτ : |s| < τ)

include hsτ in
theorem abs_mul_lt {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : |s * t| < τ := by
  rw [abs_mul, abs_of_nonneg ht.1]
  calc |s| * t ≤ |s| * 1 := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg s)
    _ = |s| := mul_one _
    _ < τ := hsτ

include hΦ hk hode hs hsτ in
/-- The sphere path of the coordinate geodesic with initial jet (z.1, s • z.2) has energy
F²(z.1, s • z.2). -/
theorem pathEnergy_scaledGeodesic :
    pathEnergy F (chartPath p (fun _ ht => scaledGeodesic_mem F p hode (abs_mul_lt hsτ ht))
      (continuousOn_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ hk s).contDiffAt)
      (hasDerivAt_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ hk s).contDiffAt)
      (deriv_continuousOn_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ hk s).contDiffAt)) =
      coordinateLagrangian F p (scaledGeodesic Φ z s 0, deriv (scaledGeodesic Φ z s) 0) :=
  pathEnergy_geodesic F p (fun _ _ => (scaledGeodesic_contDiff hΦ hk s).contDiffAt)
    (fun _ ht => scaledGeodesic_mem F p hode (abs_mul_lt hsτ ht))
    (fun _ ht => deriv_scaledGeodesic_ne_zero F p hode hs (abs_mul_lt hsτ ht))
    (fun _ ht => scaledGeodesic_acc F p hode hs (abs_mul_lt hsτ ht))

include hode hτ h0 in
theorem initial_jet :
    (scaledGeodesic Φ z s 0, deriv (scaledGeodesic Φ z s) 0) = (z.1, s • z.2) := by
  rw [scaledGeodesic_zero h0, deriv_scaledGeodesic_zero F p hode h0 hτ]

include hΦ hk hode hs hsτ h0 hτ in
/-- Energy of the geodesic sphere path in terms of the initial jet. -/
theorem pathEnergy_scaledGeodesic_eq :
    pathEnergy F (chartPath p (fun _ ht => scaledGeodesic_mem F p hode (abs_mul_lt hsτ ht))
      (continuousOn_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ hk s).contDiffAt)
      (hasDerivAt_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ hk s).contDiffAt)
      (deriv_continuousOn_of_C2 fun _ _ => (scaledGeodesic_contDiff hΦ hk s).contDiffAt)) =
      coordinateLagrangian F p (z.1, s • z.2) := by
  rw [pathEnergy_scaledGeodesic F p hΦ hk hode hs hsτ, initial_jet F p h0 hτ hode]

end Energy

end

end Finsler.CoordinateExp
