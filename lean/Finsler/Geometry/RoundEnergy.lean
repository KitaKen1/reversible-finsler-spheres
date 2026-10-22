module

public import Finsler.Analysis.EnergyCalibration
public import Finsler.Analysis.IntervalH1AffineRestrict
public import Finsler.Geometry.MetricComparison
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! The minimal energy of the round metric. For unit vectors p, q the minimal energy of sphere
paths from p to q is arccos(⟪p, q⟫)², the square of the angle, when q ≠ −p.

The upper bound is the great-circle arc t ↦ cos(θt) p + sin(θt) u with θ = arccos⟪p, q⟫ and
u the unit vector of q − ⟪p, q⟫ p, whose speed is θ. The lower bound is a calibration. The
function φ_ε(c) = (1 + ε) arccos(c / (1 + ε)) is smooth for |c| < 1 + ε, and since
(1 + ε)²(1 − c²) ≤ (1 + ε)² − c², the function x ↦ φ_ε(⟪p, x⟫)² satisfies the eikonal inequality
of the round metric at every point of the sphere; cut off outside |c| < 1 + ε/2 it is a global
C¹ calibrator. Hence φ_ε(⟪p, q⟫) ≤ φ_ε(1) + √E along every path from p to q, and ε → 0 gives
arccos⟪p, q⟫ ≤ √E. No sub-path or exit-time argument is needed. -/

@[expose] public section

namespace Finsler.RoundEnergy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevSpherePath Finsler.SobolevOfPrimitive Finsler.SphereDistance
open Finsler.EnergyCalibration Finsler.SphereRetraction
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace Real

noncomputable section

variable {n : ℕ}

/-! ### The round Lagrangian on tangent pairs -/

/-- On a tangent pair of the unit sphere the round Lagrangian is the squared norm. -/
theorem lagrangian_round {x ξ : Ambient n} (hx : ‖x‖ = 1) (hξ : ⟪x, ξ⟫ = 0) :
    lagrangian (roundMetric n) (x, ξ) = ‖ξ‖ ^ 2 := by
  let xs : Sphere n := ⟨x, by simpa using hx⟩
  have hr : ξ ∈ (ambientMap xs).range := by
    rw [ambientMap_range]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hξ
  obtain ⟨v, hv⟩ := hr
  have hp : ambientPair (⟨xs, v⟩ : Total n) = (x, ξ) := by
    apply Prod.ext
    · rfl
    · exact hv
  rw [← hp, lagrangian_ambientPair]
  change ‖ambientVector n ⟨xs, v⟩‖ ^ 2 = _
  rw [show ambientVector n ⟨xs, v⟩ = ξ from hv]

/-! ### Elementary inner product facts -/

theorem norm_sq_comb {p u : Ambient n} (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0)
    (a b : ℝ) : ‖a • p + b • u‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hpu,
    hp, hu, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

theorem inner_comb {p u : Ambient n} (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0)
    (a b c d : ℝ) : ⟪a • p + b • u, c • p + d • u⟫ = a * c + b * d := by
  have hpp : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hup : ⟪u, p⟫ = 0 := by rw [real_inner_comm, hpu]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hpp,
    huu, hpu, hup]
  ring

/-- For a tangent vector ξ at a unit x, |⟪p, ξ⟫| ≤ √(1 − ⟪p, x⟫²) ‖ξ‖. -/
theorem abs_inner_le {p x ξ : Ambient n} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) (hξ : ⟪x, ξ⟫ = 0) :
    |⟪p, ξ⟫| ≤ Real.sqrt (1 - ⟪p, x⟫ ^ 2) * ‖ξ‖ := by
  set c := ⟪p, x⟫ with hc
  have h1 : ⟪p, ξ⟫ = ⟪p - c • x, ξ⟫ := by
    rw [inner_sub_left, real_inner_smul_left, hξ, mul_zero, sub_zero]
  have h2 : ‖p - c • x‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, hp, hx, Real.norm_eq_abs, mul_pow,
      sq_abs, ← hc]
    ring
  have h3 : ‖p - c • x‖ = Real.sqrt (1 - c ^ 2) := by
    rw [← h2, Real.sqrt_sq (norm_nonneg _)]
  rw [h1, ← h3]
  exact abs_real_inner_le_norm _ _

/-! ### The great-circle arc -/

/-- The great-circle arc t ↦ cos(θt) p + sin(θt) u. -/
def arcCurve (p u : Ambient n) (θ t : ℝ) : Ambient n :=
  Real.cos (θ * t) • p + Real.sin (θ * t) • u

/-- Its velocity. -/
def arcVel (p u : Ambient n) (θ t : ℝ) : Ambient n :=
  (-(θ * Real.sin (θ * t))) • p + (θ * Real.cos (θ * t)) • u

theorem arcCurve_continuous (p u : Ambient n) (θ : ℝ) : Continuous (arcCurve p u θ) := by
  unfold arcCurve
  fun_prop

theorem arcVel_continuous (p u : Ambient n) (θ : ℝ) : Continuous (arcVel p u θ) := by
  unfold arcVel
  fun_prop

theorem arcCurve_hasDerivAt (p u : Ambient n) (θ t : ℝ) :
    HasDerivAt (arcCurve p u θ) (arcVel p u θ t) t := by
  have h1 : HasDerivAt (fun t => θ * t) θ t := by
    simpa using (hasDerivAt_id t).const_mul θ
  have hc := (Real.hasDerivAt_cos (θ * t)).comp t h1
  have hs := (Real.hasDerivAt_sin (θ * t)).comp t h1
  have h := (hc.smul_const p).add (hs.smul_const u)
  convert h using 1
  all_goals first
    | exact funext fun y => rfl
    | (simp only [arcVel]; congr 1 <;> congr 1 <;> ring)

theorem arcCurve_eq_add_integral (p u : Ambient n) (θ t : ℝ) :
    arcCurve p u θ t = arcCurve p u θ 0 + ∫ s in (0 : ℝ)..t, arcVel p u θ s := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => arcCurve_hasDerivAt p u θ x)
    ((arcVel_continuous p u θ).intervalIntegrable 0 t)]
  abel

/-- The great-circle arc as an actual graph element. -/
def arcPath (p u : Ambient n) (θ : ℝ) : Space n :=
  ofPrimitive (arcCurve_continuous p u θ).continuousOn
    (memLp_of_continuousOn (arcVel_continuous p u θ).continuousOn)
    (fun t _ => arcCurve_eq_add_integral p u θ t)

theorem representative_arcPath (p u : Ambient n) (θ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (arcPath p u θ) t = arcCurve p u θ t :=
  representative_ofPrimitive _ _ _ ht

theorem velocity_arcPath_ae (p u : Ambient n) (θ : ℝ) :
    velocity (arcPath p u θ) =ᵐ[intervalMeasure] arcVel p u θ :=
  velocity_ofPrimitive_ae _ _ _

section Arc

variable {p u : Ambient n} (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0)
include hp hu hpu

theorem norm_arcCurve (θ t : ℝ) : ‖arcCurve p u θ t‖ = 1 := by
  have h := norm_sq_comb hp hu hpu (Real.cos (θ * t)) (Real.sin (θ * t))
  rw [Real.cos_sq_add_sin_sq] at h
  have h0 := norm_nonneg (arcCurve p u θ t)
  unfold arcCurve
  nlinarith [sq_nonneg (‖Real.cos (θ * t) • p + Real.sin (θ * t) • u‖ - 1),
    norm_nonneg (Real.cos (θ * t) • p + Real.sin (θ * t) • u)]

theorem inner_arcCurve_arcVel (θ t : ℝ) : ⟪arcCurve p u θ t, arcVel p u θ t⟫ = 0 := by
  rw [arcCurve, arcVel, inner_comb hp hu hpu]
  ring

theorem norm_sq_arcVel (θ t : ℝ) : ‖arcVel p u θ t‖ ^ 2 = θ ^ 2 := by
  rw [arcVel, norm_sq_comb hp hu hpu]
  have h := Real.cos_sq_add_sin_sq (θ * t)
  nlinarith [h]

theorem arcPath_mem (θ : ℝ) : arcPath p u θ ∈ SpherePath n := by
  intro t ht
  rw [representative_arcPath p u θ ht]
  exact norm_arcCurve hp hu hpu θ t

theorem pathEnergy_arcPath (θ : ℝ) : pathEnergy (roundMetric n) (arcPath p u θ) = θ ^ 2 := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hae : (fun t => lagrangian (roundMetric n) (continuousRepresentative (arcPath p u θ) t,
      velocity (arcPath p u θ) t)) =ᵐ[intervalMeasure] fun _ => θ ^ 2 := by
    filter_upwards [velocity_arcPath_ae p u θ, ae_restrict_mem measurableSet_Ioo] with t hv ht
    rw [show velocity (arcPath p u θ) t = arcVel p u θ t from hv,
      representative_arcPath p u θ (Ioo_subset_Icc_self ht),
      lagrangian_round (norm_arcCurve hp hu hpu θ t) (inner_arcCurve_arcVel hp hu hpu θ t),
      norm_sq_arcVel hp hu hpu θ t]
  rw [pathEnergy, integral_congr_ae hae, integral_const, probReal_univ, one_smul]

end Arc

/-! ### The constant path -/

/-- The constant path at p. -/
def constPath (p : Ambient n) : Space n :=
  ofPrimitive (continuousOn_const (c := p)) (memLp_of_continuousOn
    (continuousOn_const (c := (0 : Ambient n)))) (fun t _ => by simp)

theorem constPath_mem {p : Ambient n} (hp : ‖p‖ = 1) : constPath p ∈ pathsBetween n p p := by
  refine ⟨fun t ht => ?_, ?_, ?_⟩
  · rw [constPath, representative_ofPrimitive _ _ _ ht]
    exact hp
  · rw [constPath, representative_ofPrimitive _ _ _ (left_mem_Icc.mpr zero_le_one)]
  · rw [constPath, representative_ofPrimitive _ _ _ (right_mem_Icc.mpr zero_le_one)]

theorem pathEnergy_constPath {p : Ambient n} (hp : ‖p‖ = 1) :
    pathEnergy (roundMetric n) (constPath p) = 0 := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hae : (fun t => lagrangian (roundMetric n) (continuousRepresentative (constPath p) t,
      velocity (constPath p) t)) =ᵐ[intervalMeasure] fun _ => (0 : ℝ) := by
    filter_upwards [velocity_ofPrimitive_ae (continuousOn_const (c := p))
      (memLp_of_continuousOn (continuousOn_const (c := (0 : Ambient n))))
      (fun t _ => by simp), ae_restrict_mem measurableSet_Ioo] with t hv ht
    have hv' : velocity (constPath p) t = 0 := hv
    have hr : continuousRepresentative (constPath p) t = p := by
      rw [constPath, representative_ofPrimitive _ _ _ (Ioo_subset_Icc_self ht)]
    rw [hv', hr, lagrangian_round hp (inner_zero_right p), norm_zero]
    norm_num
  rw [pathEnergy, integral_congr_ae hae, integral_zero]

/-! ### The upper bound -/

theorem inner_le_one {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : ⟪p, q⟫ ≤ 1 := by
  have h := real_inner_le_norm p q
  rw [hp, hq, one_mul] at h
  exact h

theorem neg_one_le_inner {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : -1 ≤ ⟪p, q⟫ := by
  have h := abs_real_inner_le_norm p q
  rw [hp, hq, one_mul] at h
  exact (abs_le.mp h).1

theorem eq_of_inner_eq_one {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (h : ⟪p, q⟫ = 1) :
    q = p := by
  have h2 : ‖q - p‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real, hp, hq, real_inner_comm, h]
    ring
  have h3 : ‖q - p‖ = 0 := (pow_eq_zero_iff two_ne_zero).mp h2
  exact sub_eq_zero.mp (norm_eq_zero.mp h3)

/-- Non-antipodal unit vectors are joined by the great-circle arc of energy arccos⟪p, q⟫². -/
theorem exists_arc {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫ ≠ -1) :
    ∃ w ∈ pathsBetween n p q, pathEnergy (roundMetric n) w = Real.arccos ⟪p, q⟫ ^ 2 := by
  set c := ⟪p, q⟫ with hc
  have hc1 : c ≤ 1 := inner_le_one hp hq
  have hc0 : -1 < c := lt_of_le_of_ne (neg_one_le_inner hp hq) (Ne.symm hpq)
  rcases eq_or_lt_of_le hc1 with h1 | h1
  · have hqp := eq_of_inner_eq_one hp hq h1
    refine ⟨constPath p, ?_, ?_⟩
    · rw [hqp]
      exact constPath_mem hp
    · rw [pathEnergy_constPath hp, h1, Real.arccos_one]
      norm_num
  · set θ := Real.arccos c with hθ
    set s := Real.sqrt (1 - c ^ 2) with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
    have hss : s ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by nlinarith)
    set u := s⁻¹ • (q - c • p) with hu
    have hpp : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
    have hpu : ⟪p, u⟫ = 0 := by
      rw [hu, real_inner_smul_right, inner_sub_right, real_inner_smul_right, hpp, ← hc]
      ring
    have hqcp : ‖q - c • p‖ ^ 2 = s ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, hp, hq, Real.norm_eq_abs, mul_pow,
        sq_abs, real_inner_comm, ← hc, hss]
      ring
    have hu1 : ‖u‖ = 1 := by
      have h2 : ‖q - c • p‖ = s := by
        rw [← Real.sqrt_sq (norm_nonneg _), hqcp, Real.sqrt_sq hs0.le]
      rw [hu, norm_smul, h2, norm_inv, Real.norm_eq_abs, abs_of_pos hs0, inv_mul_cancel₀ hs0.ne']
    have hcos : Real.cos θ = c := Real.cos_arccos hc0.le hc1
    have hsin : Real.sin θ = s := Real.sin_arccos c
    refine ⟨arcPath p u θ, ⟨arcPath_mem hp hu1 hpu θ, ?_, ?_⟩, pathEnergy_arcPath hp hu1 hpu θ⟩
    · rw [representative_arcPath p u θ (left_mem_Icc.mpr zero_le_one), arcCurve, mul_zero,
        Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero]
    · rw [representative_arcPath p u θ (right_mem_Icc.mpr zero_le_one), arcCurve, mul_one, hcos,
        hsin, hu, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]
      abel

/-! ### The calibrator -/

/-- φ_ε(c) = (1 + ε) arccos(c / (1 + ε)). -/
def phi (ε c : ℝ) : ℝ := (1 + ε) * Real.arccos (c / (1 + ε))

theorem phi_nonneg {ε : ℝ} (hε : 0 < ε) (c : ℝ) : 0 ≤ phi ε c :=
  mul_nonneg (by linarith) (Real.arccos_nonneg _)

theorem phi_hasDerivAt {ε c : ℝ} (hε : 0 < ε) (hc : |c| < 1 + ε) :
    HasDerivAt (phi ε) (-((1 + ε) / Real.sqrt ((1 + ε) ^ 2 - c ^ 2))) c := by
  have hε1 : 0 < 1 + ε := by linarith
  have hlt : |c / (1 + ε)| < 1 := by
    rw [abs_div, abs_of_pos hε1, div_lt_one hε1]
    exact hc
  have h1 : c / (1 + ε) ≠ -1 := by
    intro h
    rw [h, abs_neg, abs_one] at hlt
    exact lt_irrefl _ hlt
  have h2 : c / (1 + ε) ≠ 1 := by
    intro h
    rw [h, abs_one] at hlt
    exact lt_irrefl _ hlt
  have hd : HasDerivAt (fun x => x / (1 + ε)) (1 / (1 + ε)) c := by
    simpa using (hasDerivAt_id c).div_const (1 + ε)
  have ha := (Real.hasDerivAt_arccos h1 h2).comp c hd
  have h := ha.const_mul (1 + ε)
  convert h using 1
  · exact funext fun y => rfl
  have hq : 0 < (1 + ε) ^ 2 - c ^ 2 := by
    have := sq_lt_sq' (abs_lt.mp hc).1 (abs_lt.mp hc).2
    linarith
  have hsq : Real.sqrt (1 - (c / (1 + ε)) ^ 2) = Real.sqrt ((1 + ε) ^ 2 - c ^ 2) / (1 + ε) := by
    rw [div_pow, one_sub_div (by positivity), Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ _),
      Real.sqrt_sq hε1.le]
  rw [hsq]
  have hr : 0 < Real.sqrt ((1 + ε) ^ 2 - c ^ 2) := Real.sqrt_pos.mpr hq
  field_simp

theorem phi_contDiffAt {ε c : ℝ} (hε : 0 < ε) (hc : |c| < 1 + ε) :
    ContDiffAt ℝ 1 (phi ε) c := by
  have hε1 : 0 < 1 + ε := by linarith
  have hlt : |c / (1 + ε)| < 1 := by
    rw [abs_div, abs_of_pos hε1, div_lt_one hε1]
    exact hc
  have h1 : c / (1 + ε) ≠ -1 := by
    intro h
    rw [h, abs_neg, abs_one] at hlt
    exact lt_irrefl _ hlt
  have h2 : c / (1 + ε) ≠ 1 := by
    intro h
    rw [h, abs_one] at hlt
    exact lt_irrefl _ hlt
  have hf : ContDiffAt ℝ 1 (fun x : ℝ => x / (1 + ε)) c := contDiffAt_id.div_const (1 + ε)
  have hg : ContDiffAt ℝ 1 (Real.arccos ∘ fun x : ℝ => x / (1 + ε)) c :=
    ContDiffAt.comp (g := Real.arccos) c (Real.contDiffAt_arccos h1 h2) hf
  exact contDiffAt_const.mul hg

/-- The key estimate: |φ_ε'(c)| √(1 − c²) ≤ 1 on [−1, 1]. -/
theorem phi_deriv_bound {ε c : ℝ} (hε : 0 < ε) (hc : |c| ≤ 1) :
    (1 + ε) / Real.sqrt ((1 + ε) ^ 2 - c ^ 2) * Real.sqrt (1 - c ^ 2) ≤ 1 := by
  have hε1 : 0 < 1 + ε := by linarith
  have hc2 : c ^ 2 ≤ 1 := by
    have := sq_le_sq' (abs_le.mp hc).1 (abs_le.mp hc).2
    simpa using this
  have hq : 0 < (1 + ε) ^ 2 - c ^ 2 := by nlinarith
  have hr : 0 < Real.sqrt ((1 + ε) ^ 2 - c ^ 2) := Real.sqrt_pos.mpr hq
  rw [div_mul_eq_mul_div, div_le_one hr]
  have h1 : (1 + ε) * Real.sqrt (1 - c ^ 2) = Real.sqrt ((1 + ε) ^ 2 * (1 - c ^ 2)) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hε1.le]
  rw [h1]
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (sq_nonneg c) (by nlinarith : (0 : ℝ) ≤ (1 + ε) ^ 2 - 1)]

/-- The bump of the calibrator: one on |c| ≤ 1 + ε/4, zero outside |c| < 1 + ε/2. -/
def bump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : ℝ) where
  rIn := 1 + ε / 4
  rOut := 1 + ε / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- The one-variable calibrator ψ_ε = bump · φ_ε². -/
def psi (ε : ℝ) (hε : 0 < ε) (c : ℝ) : ℝ := bump ε hε c * phi ε c ^ 2

theorem psi_nonneg {ε : ℝ} (hε : 0 < ε) (c : ℝ) : 0 ≤ psi ε hε c :=
  mul_nonneg (bump ε hε).nonneg (sq_nonneg _)

theorem psi_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (psi ε hε) := by
  rw [contDiff_iff_contDiffAt]
  intro c
  by_cases hc : |c| < 1 + ε
  · exact (((bump ε hε).contDiff (n := 1)).contDiffAt).mul
      ((phi_contDiffAt hε hc).pow 2)
  · have hev : psi ε hε =ᶠ[𝓝 c] fun _ => 0 := by
      have hopen : IsOpen {x : ℝ | 1 + ε / 2 < |x|} := isOpen_lt continuous_const continuous_abs
      have hmem : c ∈ {x : ℝ | 1 + ε / 2 < |x|} := by
        change 1 + ε / 2 < |c|
        linarith [not_lt.mp hc]
      filter_upwards [hopen.mem_nhds hmem] with x hx
      have hx' : (bump ε hε).rOut ≤ dist x 0 := by
        rw [Real.dist_eq, sub_zero]
        exact le_of_lt hx
      rw [psi, (bump ε hε).zero_of_le_dist hx', zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

theorem psi_eventuallyEq {ε c : ℝ} (hε : 0 < ε) (hc : |c| ≤ 1) :
    psi ε hε =ᶠ[𝓝 c] fun x => phi ε x ^ 2 := by
  have hopen : IsOpen {x : ℝ | |x| < 1 + ε / 4} := isOpen_lt continuous_abs continuous_const
  have hmem : c ∈ {x : ℝ | |x| < 1 + ε / 4} := by
    change |c| < 1 + ε / 4
    linarith
  filter_upwards [hopen.mem_nhds hmem] with x hx
  have hx' : x ∈ Metric.closedBall (0 : ℝ) (bump ε hε).rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact le_of_lt hx
  rw [psi, (bump ε hε).one_of_mem_closedBall hx', one_mul]

theorem psi_hasDerivAt {ε c : ℝ} (hε : 0 < ε) (hc : |c| ≤ 1) :
    HasDerivAt (psi ε hε)
      (2 * phi ε c * (-((1 + ε) / Real.sqrt ((1 + ε) ^ 2 - c ^ 2)))) c := by
  have hc' : |c| < 1 + ε := by linarith
  have h := (phi_hasDerivAt hε hc').pow 2
  have h' : HasDerivAt (fun x => phi ε x ^ 2)
      (2 * phi ε c * (-((1 + ε) / Real.sqrt ((1 + ε) ^ 2 - c ^ 2)))) c := by
    convert h using 1
    push_cast
    ring
  exact h'.congr_of_eventuallyEq (psi_eventuallyEq hε hc)

theorem psi_eq {ε c : ℝ} (hε : 0 < ε) (hc : |c| ≤ 1) : psi ε hε c = phi ε c ^ 2 :=
  (psi_eventuallyEq hε hc).eq_of_nhds

/-- The ambient calibrator x ↦ ψ_ε(⟪p, x⟫). -/
def calib (p : Ambient n) (ε : ℝ) (hε : 0 < ε) (x : Ambient n) : ℝ := psi ε hε ⟪p, x⟫

theorem calib_contDiff (p : Ambient n) {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (calib p ε hε) :=
  (psi_contDiff hε).comp (innerSL ℝ p).contDiff

theorem calib_nonneg (p : Ambient n) {ε : ℝ} (hε : 0 < ε) (x : Ambient n) :
    0 ≤ calib p ε hε x :=
  psi_nonneg hε _

theorem abs_inner_le_one {p x : Ambient n} (hp : ‖p‖ = 1) (hx : ‖x‖ = 1) : |⟪p, x⟫| ≤ 1 := by
  have h := abs_real_inner_le_norm p x
  rwa [hp, hx, one_mul] at h

/-- The eikonal inequality of the round metric holds at every point of the sphere. -/
theorem calib_eikonal {p : Ambient n} (hp : ‖p‖ = 1) {ε : ℝ} (hε : 0 < ε) {x : Ambient n}
    (hx : ‖x‖ = 1) (ξ : Ambient n) (hξ : ⟪x, ξ⟫ = 0) :
    fderiv ℝ (calib p ε hε) x ξ ≤
      2 * Real.sqrt (calib p ε hε x) * Real.sqrt (lagrangian (roundMetric n) (x, ξ)) := by
  set c := ⟪p, x⟫ with hcdef
  have hc : |c| ≤ 1 := abs_inner_le_one hp hx
  have hd : HasFDerivAt (calib p ε hε)
      ((2 * phi ε c * (-((1 + ε) / Real.sqrt ((1 + ε) ^ 2 - c ^ 2)))) • innerSL ℝ p) x :=
    (psi_hasDerivAt hε hc).comp_hasFDerivAt x (innerSL ℝ p).hasFDerivAt
  rw [hd.fderiv]
  change (2 * phi ε c * (-((1 + ε) / Real.sqrt ((1 + ε) ^ 2 - c ^ 2)))) * ⟪p, ξ⟫ ≤ _
  rw [lagrangian_round hx hξ, Real.sqrt_sq (norm_nonneg ξ)]
  have hcal : calib p ε hε x = phi ε c ^ 2 := psi_eq hε hc
  rw [hcal, Real.sqrt_sq (phi_nonneg hε c)]
  have hb := phi_deriv_bound hε hc
  have hi := abs_inner_le hp hx hξ
  rw [← hcdef] at hi
  have hφ := phi_nonneg hε c
  set A := (1 + ε) / Real.sqrt ((1 + ε) ^ 2 - c ^ 2) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (by linarith) (Real.sqrt_nonneg _)
  have h1 : -(A * ⟪p, ξ⟫) ≤ A * |⟪p, ξ⟫| := by
    have := neg_abs_le ⟪p, ξ⟫
    nlinarith [abs_nonneg ⟪p, ξ⟫]
  have h2 : A * |⟪p, ξ⟫| ≤ A * (Real.sqrt (1 - c ^ 2) * ‖ξ‖) :=
    mul_le_mul_of_nonneg_left hi hA0
  have h3 : A * (Real.sqrt (1 - c ^ 2) * ‖ξ‖) ≤ ‖ξ‖ := by
    have := mul_le_mul_of_nonneg_right hb (norm_nonneg ξ)
    nlinarith
  have h4 : -(A * ⟪p, ξ⟫) ≤ ‖ξ‖ := le_trans h1 (le_trans h2 h3)
  nlinarith

/-! ### The lower bound -/

/-- Along every sphere path from p, the angle to p at the end is at most √E. -/
theorem arccos_le_sqrt_pathEnergy {p : Ambient n} (hp : ‖p‖ = 1) {w : Space n}
    (hw : w ∈ SpherePath n) (h0 : continuousRepresentative w 0 = p) :
    Real.arccos ⟪p, continuousRepresentative w 1⟫ ≤
      Real.sqrt (pathEnergy (roundMetric n) w) := by
  set c := ⟪p, continuousRepresentative w 1⟫ with hcdef
  have hq : ‖continuousRepresentative w 1‖ = 1 := hw 1 (right_mem_Icc.mpr zero_le_one)
  have hc : |c| ≤ 1 := abs_inner_le_one hp hq
  have hpp : ⟪p, p⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hp, one_pow]
  -- the calibration inequality for every ε > 0
  have hcal : ∀ ε : ℝ, 0 < ε → phi ε c ≤ phi ε 1 + Real.sqrt (pathEnergy (roundMetric n) w) := by
    intro ε hε
    have heik : ∀ x ∈ (univ : Set (Ambient n)), ‖x‖ = 1 → ∀ ξ : Ambient n, ⟪x, ξ⟫ = 0 →
        fderiv ℝ (calib p ε hε) x ξ ≤
          2 * Real.sqrt (calib p ε hε x) * Real.sqrt (lagrangian (roundMetric n) (x, ξ)) :=
      fun x _ hx ξ hξ => calib_eikonal hp hε hx ξ hξ
    have h := sqrt_le_add_sqrt_energy (roundMetric n) (calib_contDiff p hε) (calib_nonneg p hε)
      heik hw (fun _ _ => mem_univ _)
    have e1 : calib p ε hε (continuousRepresentative w 1) = phi ε c ^ 2 := psi_eq hε hc
    have e0 : calib p ε hε (continuousRepresentative w 0) = phi ε 1 ^ 2 := by
      rw [h0]
      change psi ε hε ⟪p, p⟫ = _
      rw [hpp]
      exact psi_eq hε (by norm_num)
    rw [e1, e0, Real.sqrt_sq (phi_nonneg hε c), Real.sqrt_sq (phi_nonneg hε 1)] at h
    exact h
  -- let ε → 0
  have hlim : ∀ c' : ℝ, Tendsto (fun ε => phi ε c') (𝓝[>] 0) (𝓝 (Real.arccos c')) := by
    intro c'
    have hcont : ContinuousAt (fun ε : ℝ => (1 + ε) * Real.arccos (c' / (1 + ε))) 0 := by
      apply ContinuousAt.mul (continuousAt_const.add continuousAt_id)
      apply Real.continuous_arccos.continuousAt.comp
      exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)
    have h := hcont.tendsto
    simp only [add_zero, one_mul, div_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hL := hlim c
  have hR := (hlim 1).add_const (Real.sqrt (pathEnergy (roundMetric n) w))
  rw [Real.arccos_one, zero_add] at hR
  exact le_of_tendsto_of_tendsto hL hR
    (eventually_nhdsWithin_of_forall fun ε hε => hcal ε hε)

/-- The energy of every sphere path from p to q is at least arccos⟪p, q⟫². -/
theorem arccos_sq_le_pathEnergy {p q : Ambient n} (hp : ‖p‖ = 1) {w : Space n}
    (hw : w ∈ pathsBetween n p q) :
    Real.arccos ⟪p, q⟫ ^ 2 ≤ pathEnergy (roundMetric n) w := by
  have h := arccos_le_sqrt_pathEnergy hp hw.1 hw.2.1
  rw [hw.2.2] at h
  calc Real.arccos ⟪p, q⟫ ^ 2 ≤ Real.sqrt (pathEnergy (roundMetric n) w) ^ 2 :=
        pow_le_pow_left₀ (Real.arccos_nonneg _) h 2
    _ = pathEnergy (roundMetric n) w := Real.sq_sqrt (pathEnergy_nonneg _ _)

/-! ### The minimal energy -/

/-- The round minimal energy between non-antipodal unit vectors is the squared angle. -/
theorem minEnergy_round {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫ ≠ -1) :
    minEnergy (roundMetric n) p q = Real.arccos ⟪p, q⟫ ^ 2 := by
  obtain ⟨w, hw, hE⟩ := exists_arc hp hq hpq
  apply le_antisymm
  · rw [← hE]
    exact minEnergy_le _ hw
  · show _ ≤ sInf _
    exact le_csInf ⟨_, ⟨w, hw, rfl⟩⟩ (by
      rintro _ ⟨v, hv, rfl⟩
      exact arccos_sq_le_pathEnergy hp hv)

/-- The round distance between non-antipodal unit vectors is the angle. -/
theorem dist_round {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ⟪p, q⟫ ≠ -1) :
    Finsler.SphereDistance.dist (roundMetric n) p q = Real.arccos ⟪p, q⟫ := by
  rw [Finsler.SphereDistance.dist, minEnergy_round hp hq hpq, Real.sqrt_sq (Real.arccos_nonneg _)]

end

end Finsler.RoundEnergy
