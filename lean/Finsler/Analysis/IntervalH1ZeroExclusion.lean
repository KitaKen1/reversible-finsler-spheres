module

public import Finsler.Analysis.IntervalH1RotationalBounds
public import Mathlib.Analysis.ODE.Gronwall

/-! One-point zero propagation for the actual rotational momenta.
Under TangentCritical the finite continuous momentum size obeys an integral
Riccati bound. Mathlib's Gronwall uniqueness, applied to the primitive of the
size, propagates a single zero forward; the periodic trace carries it around
the circle. Positive energy therefore excludes zero momentum at every time,
with a uniform positive lower bound, and excludes zero weak velocity almost
everywhere. Legendre inversion and smooth regularity are separate. -/

@[expose] public section

namespace Finsler.SobolevZeroExclusion

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevRotationalVariation Finsler.SobolevRotationalRecovery
open Finsler.SobolevRotationalBounds Finsler.SobolevCurveVariation
open Finsler.SobolevEnergyDifferential Finsler.SobolevEnergy Finsler.AmbientLagrangian
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace Interval

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- Integral Gronwall with zero initial value: a continuous nonnegative function
bounded by a constant times its own primitive vanishes. The primitive, not the
function, carries the derivative used by mathlib's uniqueness theorem. -/
theorem eq_zero_of_le_mul_integral {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {K s r : ℝ} (hb : ∀ t ∈ Icc s r, f t ≤ K * ∫ y in s..t, f y) :
    ∀ t ∈ Icc s r, f t = 0 := by
  let J : ℝ → ℝ := fun t => ∫ y in s..t, f y
  have hJd (x : ℝ) : HasDerivAt J (f x) x := (hf.integral_hasStrictDerivAt s x).hasDerivAt
  have hJnn (t : ℝ) (ht : t ∈ Icc s r) : 0 ≤ J t :=
    intervalIntegral.integral_nonneg ht.1 fun y _ => hf0 y
  have hz := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := J) (f' := f) (K := K) (a := s) (b := r)
    (fun x _ => (hJd x).continuousAt.continuousWithinAt)
    (fun x _ => (hJd x).hasDerivWithinAt) intervalIntegral.integral_same
    (fun x hx => by
      have hx' : x ∈ Icc s r := Ico_subset_Icc_self hx
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf0 x),
        abs_of_nonneg (hJnn x hx')]
      exact hb x hx')
  intro t ht
  have h := hb t ht
  have hJt : J t = 0 := hz t ht
  change f t ≤ K * J t at h
  rw [hJt, mul_zero] at h
  exact le_antisymm h (hf0 t)

theorem planeMomentum_eq_zero_of_momentumSize_eq_zero (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {t : ℝ}
    (ht : momentumSize b F u hc t = 0) (i j : ι) :
    momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t = 0 := by
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
    norm_nonneg (momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t))).mp
      ht i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => norm_nonneg
    (momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t))).mp
      hi j (Finset.mem_univ j)
  exact norm_eq_zero.mp hj

theorem exists_momentumSize_upper_bound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1, momentumSize b F u hc t ≤ B := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (momentumSize_continuousOn b F u hc)
  refine ⟨|M|, abs_nonneg _, fun t ht => ?_⟩
  have h := hM t ht
  rw [Real.norm_eq_abs] at h
  exact (le_abs_self _).trans (h.trans (le_abs_self M))

/-- The actual a.e. force bound on (0,1), restricted to a closed subinterval. -/
theorem planeForce_bound_on_Ioc (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {D B : ℝ}
    (hD : ∀ᵐ t ∂intervalMeasure, ∀ i j,
      ‖force F u (planeRotation (b i) (b j)) t‖ ≤ D * momentumSize b F u hc t ^ 2)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, momentumSize b F u hc t ≤ B) (hD0 : 0 ≤ D)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (i j : ι) :
    ∀ᵐ y ∂volume, y ∈ Ioc s t →
      ‖force F u (planeRotation (b i) (b j)) y‖ ≤ D * B * momentumSize b F u hc y := by
  have hsub : Ioc s t ⊆ Icc (0 : ℝ) 1 := fun y hy => ⟨hs.1.trans hy.1.le, hy.2.trans ht.2⟩
  have h1 : ∀ᵐ y ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ‖force F u (planeRotation (b i) (b j)) y‖ ≤ D * momentumSize b F u hc y ^ 2 ∧
        y ∈ Icc (0 : ℝ) 1 := by
    have h0 := hD
    change ∀ᵐ y ∂(volume.restrict (Ioo (0 : ℝ) 1)), _ at h0
    rw [restrict_Ioo_eq_restrict_Icc] at h0
    filter_upwards [h0, ae_restrict_mem measurableSet_Icc] with y hy hy'
    exact ⟨hy i j, hy'⟩
  have h2 := ae_restrict_of_ae_restrict_of_subset hsub h1
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp h2] with y hy hyI
  obtain ⟨hf, hmem⟩ := hy hyI
  have hm0 := momentumSize_nonneg b F u hc y
  have hle := hB y hmem
  have hprod : 0 ≤ D * (B * momentumSize b F u hc y -
      momentumSize b F u hc y * momentumSize b F u hc y) :=
    mul_nonneg hD0 (sub_nonneg.mpr (mul_le_mul_of_nonneg_right hle hm0))
  nlinarith [hf, hprod]

theorem planeMomentum_increment_le (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {D B : ℝ}
    (hD : ∀ᵐ t ∂intervalMeasure, ∀ i j,
      ‖force F u (planeRotation (b i) (b j)) t‖ ≤ D * momentumSize b F u hc t ^ 2)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, momentumSize b F u hc t ≤ B) (hD0 : 0 ≤ D)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) (i j : ι) :
    ‖momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t -
      momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc s‖ ≤
        D * B * ∫ y in s..t, momentumSize b F u hc y := by
  rw [momentumRepresentative_sub F u _ hc hs ht]
  have hcont : ContinuousOn (momentumSize b F u hc) (Icc s t) :=
    (momentumSize_continuousOn b F u hc).mono (Icc_subset_Icc hs.1 ht.2)
  have hint : IntervalIntegrable (fun y => D * B * momentumSize b F u hc y) volume s t :=
    (hcont.intervalIntegrable_of_Icc hst).const_mul (D * B)
  calc
    _ ≤ ∫ y in s..t, D * B * momentumSize b F u hc y :=
      intervalIntegral.norm_integral_le_of_norm_le hst
        (planeForce_bound_on_Ioc b F u hc hD hB hD0 hs ht i j) hint
    _ = D * B * ∫ y in s..t, momentumSize b F u hc y := intervalIntegral.integral_const_mul _ _

theorem momentumSize_le_integral_of_zero (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {D B : ℝ}
    (hD : ∀ᵐ t ∂intervalMeasure, ∀ i j,
      ‖force F u (planeRotation (b i) (b j)) t‖ ≤ D * momentumSize b F u hc t ^ 2)
    (hB : ∀ t ∈ Icc (0 : ℝ) 1, momentumSize b F u hc t ≤ B) (hD0 : 0 ≤ D)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t)
    (hzero : momentumSize b F u hc s = 0) :
    momentumSize b F u hc t ≤
      (Fintype.card ι : ℝ) ^ 2 * (D * B) * ∫ y in s..t, momentumSize b F u hc y := by
  classical
  have hterm (i j : ι) :
      ‖momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t‖ ≤
        D * B * ∫ y in s..t, momentumSize b F u hc y := by
    have h := planeMomentum_increment_le b F u hc hD hB hD0 hs ht hst i j
    rwa [planeMomentum_eq_zero_of_momentumSize_eq_zero b F u hc hzero i j, sub_zero] at h
  calc
    momentumSize b F u hc t = ∑ i, ∑ j,
        ‖momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t‖ := rfl
    _ ≤ ∑ _i : ι, ∑ _j : ι, D * B * ∫ y in s..t, momentumSize b F u hc y :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- A continuous extension of the size outside [0,1], used only for the primitive. -/
def clampedSize (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) (t : ℝ) : ℝ :=
  momentumSize b F u hc (max 0 (min t 1))

theorem clampedSize_continuous (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    Continuous (clampedSize b F u hc) :=
  (momentumSize_continuousOn b F u hc).comp_continuous
    (continuous_const.max (continuous_id.min continuous_const))
    (fun _ => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩)

theorem clampedSize_eq (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clampedSize b F u hc t = momentumSize b F u hc t := by
  unfold clampedSize
  rw [min_eq_left ht.2, max_eq_right ht.1]

theorem clampedSize_nonneg (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) (t : ℝ) :
    0 ≤ clampedSize b F u hc t :=
  momentumSize_nonneg b F u hc _

/-- Forward propagation of one zero of the actual momentum size to [s,1]. -/
theorem momentumSize_eq_zero_forward (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hzero : momentumSize b F u hc s = 0) :
    ∀ t ∈ Icc s 1, momentumSize b F u hc t = 0 := by
  obtain ⟨D, hDpos, hDb⟩ := exists_plane_force_momentum_bound b F
  obtain ⟨B, _hB0, hB⟩ := exists_momentumSize_upper_bound b F u hc
  have hmem (t : ℝ) (ht : t ∈ Icc s 1) : t ∈ Icc (0 : ℝ) 1 := ⟨hs.1.trans ht.1, ht.2⟩
  have hbound : ∀ t ∈ Icc s 1, clampedSize b F u hc t ≤
      ((Fintype.card ι : ℝ) ^ 2 * (D * B)) * ∫ y in s..t, clampedSize b F u hc y := by
    intro t ht
    have hcongr : (∫ y in s..t, clampedSize b F u hc y) =
        ∫ y in s..t, momentumSize b F u hc y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le ht.1] at hy
      exact clampedSize_eq b F u hc ⟨hs.1.trans hy.1, hy.2.trans ht.2⟩
    rw [hcongr, clampedSize_eq b F u hc (hmem t ht)]
    exact momentumSize_le_integral_of_zero b F u hc (hDb u hc) hB hDpos.le hs
      (hmem t ht) ht.1 hzero
  have hz := eq_zero_of_le_mul_integral (clampedSize_continuous b F u hc)
    (clampedSize_nonneg b F u hc) hbound
  intro t ht
  rw [← clampedSize_eq b F u hc (hmem t ht)]
  exact hz t ht

/-- One zero of the actual momentum size anywhere in [0,1] forces it to vanish. -/
theorem momentumSize_eq_zero_of_eq_zero_at (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hzero : momentumSize b F u hc s = 0) :
    ∀ t ∈ Icc (0 : ℝ) 1, momentumSize b F u hc t = 0 := by
  have h1 : momentumSize b F u hc 1 = 0 :=
    momentumSize_eq_zero_forward b F u hc hs hzero 1 ⟨hs.2, le_rfl⟩
  have h0 : momentumSize b F u hc 0 = 0 := by
    rw [← momentumSize_periodic_trace b F u hc]
    exact h1
  exact momentumSize_eq_zero_forward b F u hc ⟨le_rfl, zero_le_one⟩ h0

theorem momentumSize_pos_of_energy_pos (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (hE : 0 < energy F u) : ∀ t ∈ Icc (0 : ℝ) 1, 0 < momentumSize b F u hc t := by
  intro t ht
  rcases (momentumSize_nonneg b F u hc t).lt_or_eq with h | h
  · exact h
  · exfalso
    have hall := momentumSize_eq_zero_of_eq_zero_at b F u hc ht h.symm
    have hE0 := (energy_eq_zero_iff_momentumSize_zero b F u hc).mpr
      (fun s => hall s s.property)
    linarith

theorem recoveredCovector_ne_zero_of_energy_pos (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (hE : 0 < energy F u) (t : ClosedInterval) : recoveredCovector b F u hc t ≠ 0 := by
  intro h
  have h0 := (momentumSize_eq_zero_iff b F u hc t).mpr h
  have hpos := momentumSize_pos_of_energy_pos b F u hc hE t t.property
  linarith

theorem exists_momentumSize_lower_bound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (hE : 0 < energy F u) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc (0 : ℝ) 1, m ≤ momentumSize b F u hc t := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr zero_le_one)
    (momentumSize_continuousOn b F u hc)
  exact ⟨momentumSize b F u hc t₀, momentumSize_pos_of_energy_pos b F u hc hE t₀ ht₀,
    fun t ht => isMinOn_iff.mp hmin t ht⟩

theorem momentumSize_le_recoveredCovector (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (t : ClosedInterval) :
    momentumSize b F u hc t ≤ 2 * (Fintype.card ι : ℝ) ^ 2 * ‖recoveredCovector b F u hc t‖ := by
  classical
  have hq := u.sphere_constraint t
  have hterm (i j : ι) :
      ‖momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t‖ ≤
        2 * ‖recoveredCovector b F u hc t‖ := by
    rw [← recoveredCovector_rotation b F u hc (planeRotation_isRotation (b i) (b j)) t]
    have hA : ‖planeRotation (b i) (b j) (continuousRepresentative (u.data : Space n) t)‖ ≤ 2 :=
      ((planeRotation (b i) (b j)).le_opNorm _).trans (by
        rw [hq, mul_one]
        exact planeRotation_opNorm_le_two _ _ (b.norm_eq_one i) (b.norm_eq_one j))
    calc
      _ ≤ ‖recoveredCovector b F u hc t‖ *
          ‖planeRotation (b i) (b j) (continuousRepresentative (u.data : Space n) t)‖ :=
        (recoveredCovector b F u hc t).le_opNorm _
      _ ≤ ‖recoveredCovector b F u hc t‖ * 2 := mul_le_mul_of_nonneg_left hA (norm_nonneg _)
      _ = 2 * ‖recoveredCovector b F u hc t‖ := mul_comm _ _
  calc
    momentumSize b F u hc t = ∑ i, ∑ j,
        ‖momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t‖ := rfl
    _ ≤ ∑ _i : ι, ∑ _j : ι, 2 * ‖recoveredCovector b F u hc t‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem norm_tangentCovector_le (q : Ambient n) (p : Ambient n →L[ℝ] ℝ) (hq : ‖q‖ = 1) :
    ‖tangentCovector q p‖ ≤ 2 * ‖p‖ := by
  unfold tangentCovector
  calc
    ‖p - p q • innerSL ℝ q‖ ≤ ‖p‖ + ‖p q • innerSL ℝ q‖ := norm_sub_le _ _
    _ = ‖p‖ + ‖p q‖ * ‖q‖ := by rw [norm_smul, innerSL_apply_norm]
    _ ≤ ‖p‖ + ‖p‖ * ‖q‖ * ‖q‖ := by gcongr; exact p.le_opNorm q
    _ = 2 * ‖p‖ := by rw [hq]; ring

theorem exists_recoveredCovector_lower_bound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (hE : 0 < energy F u) :
    ∃ m : ℝ, 0 < m ∧ ∀ t : ClosedInterval, m ≤ ‖recoveredCovector b F u hc t‖ := by
  obtain ⟨m, hm, hle⟩ := exists_momentumSize_lower_bound b F u hc hE
  set N : ℝ := (Fintype.card ι : ℝ)
  refine ⟨m / (2 * (N ^ 2 + 1)), by positivity, fun t => ?_⟩
  have h1 := hle t t.property
  have h2 := momentumSize_le_recoveredCovector b F u hc t
  have hQ := norm_nonneg (recoveredCovector b F u hc t)
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- Zero-velocity exclusion: a positive-energy tangent-critical loop has weak
velocity bounded below almost everywhere. No regularity is assumed. -/
theorem exists_weakVelocity_lower_bound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (hE : 0 < energy F u) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ t ∂intervalMeasure, c ≤ ‖velocity (u.data : Space n) t‖ := by
  obtain ⟨m, hm, hle⟩ := exists_recoveredCovector_lower_bound b F u hc hE
  obtain ⟨C, hC, hb⟩ := exists_weakJet_partial_bounds F
  refine ⟨m / (2 * C), by positivity, ?_⟩
  filter_upwards [hb u, recoveredCovector_ae b F u hc, ae_restrict_mem measurableSet_Ioo]
    with t ht hQ hmem
  have h1 := hle ⟨t, Ioo_subset_Icc_self hmem⟩
  have hq : ‖continuousRepresentative (u.data : Space n) t‖ = 1 :=
    u.sphere_constraint ⟨t, Ioo_subset_Icc_self hmem⟩
  have h2 : ‖recoveredCovector b F u hc t‖ ≤
      2 * (C * ‖velocity (u.data : Space n) t‖) := by
    rw [hQ]
    exact (norm_tangentCovector_le _ _ hq).trans
      (mul_le_mul_of_nonneg_left ht.2 (by norm_num))
  change m ≤ ‖recoveredCovector b F u hc (⟨t, Ioo_subset_Icc_self hmem⟩ : ClosedInterval)‖
    at h1
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The actual squared Finsler speed is bounded below almost everywhere. -/
theorem exists_density_lower_bound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (hE : 0 < energy F u) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ t ∂intervalMeasure, c ≤ lagrangian F (weakJet u t) := by
  obtain ⟨c, hc0, hv⟩ := exists_weakVelocity_lower_bound b F u hc hE
  obtain ⟨d, _D, hd, _hD, hb⟩ := exists_density_bounds F
  refine ⟨d * c ^ 2, by positivity, ?_⟩
  filter_upwards [hv, hb u] with t ht hbt
  calc
    d * c ^ 2 ≤ d * ‖velocity (u.data : Space n) t‖ ^ 2 := by gcongr
    _ ≤ lagrangian F (weakJet u t) := hbt.1

end

end Finsler.SobolevZeroExclusion
