module

public import Finsler.Analysis.IntervalH1Iteration
public import Finsler.Geometry.EnergyConservation

/-! Actual Finsler energy scales by k² under genuine positive H¹ iteration.
Iteration is continuous in the original strong H¹ topology, preserves the
geometric image, is injective, and maps actual sqrt-energy cuts to scaled cuts.
The inverse from the half-period fixed set is a separate obligation. -/

@[expose] public section

namespace Finsler.SobolevIteration

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergy
open Finsler.SobolevCircleRepresentative Finsler.SobolevPeriodicVelocity
open Finsler.SobolevShiftEnergy Finsler.AmbientLagrangian Finsler.CircleLpTransfer
open Finsler.Geometry Finsler.SobolevReflectionAction
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem iterateData_continuous (n k : ℕ) (hk : k ≠ 0) :
    Continuous (fun u : periodicSubmodule n => iterateData u k hk) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply tendsto_iff_value_velocity.mpr
  constructor
  · simp_rw [value_iterateData]
    exact ((iterateLpL (Ambient n) k hk).continuous.comp
      ((valueL n).continuous.comp continuous_subtype_val)).continuousAt
  · simp_rw [velocity_iterateData]
    have hw : Continuous (fun v : periodicSubmodule n => velocity (v : Space n)) :=
      (show Continuous (fun v : Space n => velocity v) from (velocityL n).continuous).comp
        continuous_subtype_val
    have h : Continuous (fun v : periodicSubmodule n =>
        (k : ℝ) • iterateLpL (Ambient n) k hk (velocity (v : Space n))) :=
      (continuous_const : Continuous (fun _ : periodicSubmodule n => (k : ℝ))).smul
        ((iterateLpL (Ambient n) k hk).continuous.comp hw)
    exact h.continuousAt

theorem iterateSphere_continuous (n k : ℕ) (hk : k ≠ 0) :
    Continuous (fun u : SphereLoop n => iterateSphere u k hk) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  apply sphereLoop_tendsto_iff.mpr
  have hd : Continuous (fun v : SphereLoop n => v.data) :=
    (sphereLoop_data_isometry n).continuous.subtype_mk (fun v => v.data.property)
  exact ((iterateData_continuous n k hk).comp hd).continuousAt

theorem iterateData_norm_sq {n : ℕ} (u : periodicSubmodule n) (k : ℕ) (hk : k ≠ 0) :
    ‖iterateData u k hk‖ ^ 2 = ‖value (u : Space n)‖ ^ 2 +
      (k : ℝ) ^ 2 * ‖velocity (u : Space n)‖ ^ 2 := by
  have hv : ‖value (iterateData u k hk)‖ = ‖value (u : Space n)‖ :=
    (congrArg (fun f : ValueLp n => ‖f‖) (value_iterateData u k hk)).trans
      (iterateLpL_norm (value (u : Space n)) k hk)
  have hw : ‖velocity (iterateData u k hk)‖ = (k : ℝ) * ‖velocity (u : Space n)‖ := by
    calc
      ‖velocity (iterateData u k hk)‖ = ‖iterateVelocityLp u k hk‖ :=
        congrArg (fun f : ValueLp n => ‖f‖) (velocity_iterateData u k hk)
      _ = (k : ℝ) * ‖iterateLpL (Ambient n) k hk (velocity (u : Space n))‖ := by
        change ‖(k : ℝ) • iterateLpL (Ambient n) k hk (velocity (u : Space n))‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg k)]
      _ = _ := congrArg (fun r : ℝ => (k : ℝ) * r)
        (iterateLpL_norm (velocity (u : Space n)) k hk)
  calc
    ‖iterateData u k hk‖ ^ 2 = ‖value (iterateData u k hk)‖ ^ 2 +
      ‖velocity (iterateData u k hk)‖ ^ 2 := norm_sq_eq _
    _ = ‖value (u : Space n)‖ ^ 2 + ((k : ℝ) * ‖velocity (u : Space n)‖) ^ 2 :=
      congrArg₂ (fun x y : ℝ => x ^ 2 + y ^ 2) hv hw
    _ = _ := by ring

theorem density_iterateSphere_ae {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n)
    (k : ℕ) (hk : k ≠ 0) :
    (fun t => lagrangian F (weakJet (iterateSphere u k hk) t)) =ᵐ[intervalMeasure]
      fun t => (k : ℝ) ^ 2 * periodicDensity F u ((k : ℝ) * t) := by
  filter_upwards [velocity_iterateData_ae u.data k hk, ae_restrict_mem measurableSet_Ioo]
    with t hv ht
  change lagrangian F (continuousRepresentative (iterateData u.data k hk) t,
    velocity (iterateData u.data k hk) t) = _
  rw [representative_iterateData u.data k hk (Ioo_subset_Icc_self ht), hv]
  exact Finsler.EnergyConservation.lagrangian_velocity_smul F _ _ (k : ℝ)

theorem energy_iterateSphere {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n)
    (k : ℕ) (hk : k ≠ 0) :
    energy F (iterateSphere u k hk) = (k : ℝ) ^ 2 * energy F u := by
  change (∫ t, lagrangian F (weakJet (iterateSphere u k hk) t) ∂intervalMeasure) = _
  rw [integral_congr_ae (density_iterateSphere_ae F u k hk)]
  have hI : (∫ t in (0 : ℝ)..(k : ℝ), periodicDensity F u t) = (k : ℝ) * energy F u := by
    rw [energy_eq_periodicDensity F u]
    simpa only [zsmul_eq_mul, smul_eq_mul, Int.cast_natCast, mul_one, zero_add] using
      (periodicDensity_periodic F u).intervalIntegral_add_zsmul_eq (k : ℤ) 0
        (periodicDensity_intervalIntegrable F u)
  have h : (∫ t, (k : ℝ) ^ 2 * periodicDensity F u ((k : ℝ) * t) ∂intervalMeasure) =
      ∫ t in (0 : ℝ)..1, (k : ℝ) ^ 2 * periodicDensity F u ((k : ℝ) * t) := by
    change (∫ t in Ioo (0 : ℝ) 1, _) = _
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  rw [h, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ (Nat.cast_ne_zero.mpr hk)]
  simp only [mul_zero, mul_one, smul_eq_mul]
  rw [hI]
  field_simp

theorem energy_doubleSphere {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) :
    energy F (iterateSphere u 2 (by norm_num)) = 4 * energy F u := by
  simpa only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num] using
    energy_iterateSphere F u 2 (by norm_num)

theorem sqrt_energy_iterateSphere {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n)
    (k : ℕ) (hk : k ≠ 0) :
    Real.sqrt (energy F (iterateSphere u k hk)) = (k : ℝ) * Real.sqrt (energy F u) := by
  rw [energy_iterateSphere, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg k)]

theorem degreeCover_surjective (k : ℕ) (hk : k ≠ 0) : Function.Surjective (degreeCover k) := by
  intro x
  refine ⟨((circlePoint x : ℝ) / (k : ℝ) : ℝ), ?_⟩
  rw [degreeCover_coe, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hk), circlePoint_coe]

theorem sphereImage_iterateSphere {n : ℕ} (u : SphereLoop n) (k : ℕ) (hk : k ≠ 0) :
    Finsler.SobolevReverse.sphereImage (iterateSphere u k hk) =
      Finsler.SobolevReverse.sphereImage u := by
  rw [← sphereCircleMap_image, ← sphereCircleMap_image]
  have hm : (sphereCircleMap (iterateSphere u k hk) : Phase → Sphere n) =
      sphereCircleMap u ∘ degreeCover k := funext (circleMap_iterateSphere u k hk)
  rw [hm]
  exact (degreeCover_surjective k hk).range_comp _

theorem iterateSphere_injective (n k : ℕ) (hk : k ≠ 0) :
    Function.Injective (fun u : SphereLoop n => iterateSphere u k hk) := by
  intro u v huv
  apply sphereCircleMap_injective
  apply ContinuousMap.ext
  intro x
  obtain ⟨y, hy⟩ := degreeCover_surjective k hk x
  have h := congrArg (fun w : SphereLoop n => sphereCircleMap w y) huv
  simpa only [circleMap_iterateSphere, hy] using h

theorem iterateSphere_mul {n : ℕ} (u : SphereLoop n) (k l : ℕ)
    (hk : k ≠ 0) (hl : l ≠ 0) :
    iterateSphere (iterateSphere u k hk) l hl = iterateSphere u (k * l) (Nat.mul_ne_zero hk hl) := by
  apply sphereCircleMap_injective
  apply ContinuousMap.ext
  intro x
  simp only [circleMap_iterateSphere, degreeCover_apply, smul_smul]

theorem iterateSphere_vadd {n : ℕ} (u : SphereLoop n) (k : ℕ) (hk : k ≠ 0) (a : Phase) :
    a +ᵥ iterateSphere u k hk = iterateSphere ((k • a) +ᵥ u) k hk := by
  apply sphereCircleMap_injective
  apply ContinuousMap.ext
  intro x
  simp only [Finsler.SobolevCircleAction.sphereCircleMap_vadd,
    circleMap_iterateSphere, degreeCover_apply, smul_add]

theorem doubleSphere_fixed_half {n : ℕ} (u : SphereLoop n) :
    ((1 / 2 : ℝ) : Phase) +ᵥ iterateSphere u 2 (by norm_num) = iterateSphere u 2 (by norm_num) := by
  have hh : (2 : ℕ) • ((1 / 2 : ℝ) : Phase) = 0 := by
    have h := degreeCover_coe 2 (1 / 2)
    change (2 : ℕ) • ((1 / 2 : ℝ) : Phase) = _ at h
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) * (1 / 2) = 1 by norm_num] at h
    exact h.trans (AddCircle.coe_period (1 : ℝ))
  rw [iterateSphere_vadd, hh, zero_vadd]

theorem iterateSphere_mem_scaledCut {n : ℕ} (F : ReversibleMetric n) {b : ℝ}
    (u : SphereLoop n) (hu : u ∈ energyCut F b) (k : ℕ) (hk : k ≠ 0) :
    iterateSphere u k hk ∈ energyCut F ((k : ℝ) * b) := by
  rw [mem_energyCut, sqrt_energy_iterateSphere]
  exact mul_lt_mul_of_pos_left ((mem_energyCut F b u).mp hu)
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk))

def iterateCut {n : ℕ} (F : ReversibleMetric n) (b : ℝ) (k : ℕ) (hk : k ≠ 0) :
    energyCut F b → energyCut F ((k : ℝ) * b) :=
  fun u => ⟨iterateSphere u k hk, iterateSphere_mem_scaledCut F u u.property k hk⟩

theorem iterateCut_val {n : ℕ} (F : ReversibleMetric n) (b : ℝ)
    (k : ℕ) (hk : k ≠ 0) (u : energyCut F b) :
    (iterateCut F b k hk u : SphereLoop n) = iterateSphere (u : SphereLoop n) k hk := rfl

theorem iterateCut_continuous {n : ℕ} (F : ReversibleMetric n) (b : ℝ) (k : ℕ) (hk : k ≠ 0) :
    Continuous (iterateCut F b k hk) :=
  ((iterateSphere_continuous n k hk).comp continuous_subtype_val).subtype_mk _

end

end Finsler.SobolevIteration
