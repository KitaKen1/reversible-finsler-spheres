module

public import Finsler.Analysis.IntervalH1Concat
public import Finsler.Analysis.IntervalH1Length

/-! Length of actual H1 sphere paths, invariant under affine restriction and
additive under concatenation. This supplies the length accounting for the
specified short-arc self-cut, independently of its timing. -/

@[expose] public section
namespace Finsler.H1PathLength

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat
open Finsler.AmbientLagrangian MeasureTheory Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

variable {n : ℕ}

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

def speed (F : ReversibleMetric n) (w : Space n) (t : ℝ) : ℝ :=
  Real.sqrt (lagrangian F (continuousRepresentative w t, velocity w t))

def length (F : ReversibleMetric n) (w : Space n) : ℝ :=
  ∫ t, speed F w t ∂intervalMeasure

theorem speed_sq (F : ReversibleMetric n) (w : Space n) (t : ℝ) :
    speed F w t ^ 2 = lagrangian F (continuousRepresentative w t, velocity w t) :=
  Real.sq_sqrt (sq_nonneg _)

theorem speed_memLp (F : ReversibleMetric n) {w : Space n} (hw : w ∈ SpherePath n) :
    MemLp (speed F w) 2 intervalMeasure := by
  have hm : AEStronglyMeasurable (speed F w) intervalMeasure :=
    (density_aestronglyMeasurable hw F).aemeasurable.sqrt.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  simpa only [speed_sq] using density_integrable F hw

theorem speed_integrable (F : ReversibleMetric n) {w : Space n} (hw : w ∈ SpherePath n) :
    Integrable (speed F w) intervalMeasure :=
  (speed_memLp F hw).integrable (by norm_num)

theorem speed_intervalIntegrable (F : ReversibleMetric n) {w : Space n}
    (hw : w ∈ SpherePath n) : IntervalIntegrable (speed F w) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (speed_integrable F hw)

theorem length_nonneg (F : ReversibleMetric n) (w : Space n) : 0 ≤ length F w :=
  integral_nonneg fun _ => Real.sqrt_nonneg _

theorem length_sphereLoop (F : ReversibleMetric n) (u : SphereLoop n) :
    length F (u.data : Space n) = SobolevLength.length F u := rfl

theorem length_sq_le_energy (F : ReversibleMetric n) {w : Space n}
    (hw : w ∈ SpherePath n) : length F w ^ 2 ≤ pathEnergy F w := by
  let L := length F w
  have hi := speed_integrable F hw
  have hi2 : Integrable (fun t => speed F w t ^ 2) intervalMeasure := by
    simpa only [speed_sq] using density_integrable F hw
  have hexp : (fun t => (speed F w t - L) ^ 2) =
      fun t => speed F w t ^ 2 - (2 * L) * speed F w t + L ^ 2 := by
    funext t
    ring
  have hnonneg := integral_nonneg (μ := intervalMeasure) (fun t => sq_nonneg (speed F w t - L))
  have hA : Integrable (fun t => speed F w t ^ 2 - (2 * L) * speed F w t)
      intervalMeasure := hi2.sub (hi.const_mul (2 * L))
  have hB : Integrable (fun _ : ℝ => L ^ 2) intervalMeasure := integrable_const _
  have hC : Integrable (fun t => (2 * L) * speed F w t) intervalMeasure :=
    hi.const_mul (2 * L)
  rw [hexp, integral_add hA hB,
    integral_sub hi2 hC, integral_const_mul, integral_const] at hnonneg
  have he : (∫ t, speed F w t ^ 2 ∂intervalMeasure) = pathEnergy F w := by
    simp only [speed_sq, pathEnergy]
  rw [he] at hnonneg
  simp only [Measure.real, SobolevLength.intervalMeasure_univ,
    ENNReal.toReal_one, one_smul] at hnonneg
  change 0 ≤ pathEnergy F w - 2 * L * L + L ^ 2 at hnonneg
  change L ^ 2 ≤ pathEnergy F w
  nlinarith

theorem length_eq_intervalIntegral (F : ReversibleMetric n) (w : Space n) :
    length F w = ∫ t in (0 : ℝ)..1, speed F w t := by
  change (∫ t in Ioo (0 : ℝ) 1, speed F w t) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]

theorem speed_smul (F : ReversibleMetric n) (q v : Ambient n) {r : ℝ} (hr : 0 ≤ r) :
    Real.sqrt (lagrangian F (q, r • v)) = r * Real.sqrt (lagrangian F (q, v)) := by
  rw [Finsler.EnergyConservation.lagrangian_velocity_smul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hr]

theorem length_restrict (F : ReversibleMetric n) (u : Space n) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    length F (restrict u hs ht hst) = ∫ x in s..t, speed F u x := by
  have hae : speed F (restrict u hs ht hst) =ᵐ[intervalMeasure]
      fun τ => (t - s) * speed F u (s + (t - s) * τ) := by
    filter_upwards [velocity_restrict_ae u hs ht hst,
      ae_restrict_mem measurableSet_Ioo] with τ hv hτ
    unfold speed
    rw [representative_restrict u hs ht hst (Ioo_subset_Icc_self hτ), hv]
    exact speed_smul F _ _ (sub_nonneg.mpr hst)
  rw [length, integral_congr_ae hae]
  change (∫ τ in Ioo (0 : ℝ) 1, (t-s) * speed F u (s+(t-s)*τ)) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_add_mul (speed F u) (t-s) s
    (a := 0) (b := 1)
  simpa only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] using h

theorem length_concat (F : ReversibleMetric n) (u w : Space n) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hu : u ∈ SpherePath n) (hw : w ∈ SpherePath n)
    (hmatch : continuousRepresentative u 1 = continuousRepresentative w 0) :
    length F (concat u w ha0 ha1) = length F u + length F w := by
  let c := concat u w ha0 ha1
  have hcm : c ∈ SpherePath n := concat_mem u w ha0 ha1 hu hw hmatch
  have hint := speed_intervalIntegrable F hcm
  have h0a : IntervalIntegrable (speed F c) volume 0 a := by
    apply hint.mono_set
    rw [uIcc_of_le ha0.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ha1.le
  have ha1' : IntervalIntegrable (speed F c) volume a 1 := by
    apply hint.mono_set
    rw [uIcc_of_le ha1.le, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha0.le le_rfl
  have hleft : length F u = ∫ t in (0 : ℝ)..a, speed F c t := by
    have h := length_restrict F c zero_mem_unit (split_mem ha0 ha1) ha0.le
    rw [restrict_concat_left u w ha0 ha1] at h
    exact h
  have hright : length F w = ∫ t in a..1, speed F c t := by
    have h := length_restrict F c (split_mem ha0 ha1) one_mem_unit ha1.le
    rw [restrict_concat_right u w ha0 ha1 hmatch] at h
    exact h
  rw [length_eq_intervalIntegral, ← intervalIntegral.integral_add_adjacent_intervals h0a ha1',
    ← hleft, ← hright]

theorem length_restrictions_add (F : ReversibleMetric n) {u : Space n}
    (hu : u ∈ SpherePath n) (t : ClosedInterval) :
    length F (restrict u (by norm_num) t.property t.property.1) +
      length F (restrict u t.property (by norm_num) t.property.2) = length F u := by
  rw [length_restrict, length_restrict, length_eq_intervalIntegral]
  have hi := speed_intervalIntegrable F hu
  apply intervalIntegral.integral_add_adjacent_intervals
  · apply hi.mono_set
    rw [uIcc_of_le t.property.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl t.property.2
  · apply hi.mono_set
    rw [uIcc_of_le t.property.2, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc t.property.1 le_rfl

end
end Finsler.H1PathLength
