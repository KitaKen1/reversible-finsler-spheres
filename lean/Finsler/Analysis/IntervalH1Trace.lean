module

public import Finsler.Analysis.IntervalH1Representative
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Topology.ContinuousMap.Compact

/-! Bounded evaluation of the actual interval H¹ continuous representative.
The estimate is obtained from its actual weak velocity and probability measure
on (0,1), with no assumed trace or arbitrary velocity field. -/

@[expose] public section

namespace Finsler.IntervalSobolev

open Finsler.SphereGeometry MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

theorem intervalMeasure_probability : IsProbabilityMeasure intervalMeasure := by
  constructor
  change (volume.restrict (Ioo (0 : ℝ) 1)) univ = 1
  simp [Measure.restrict_apply, Real.volume_Ioo]

theorem integral_norm_le_valueLp_norm {n : ℕ} (f : ValueLp n) :
    (∫ t, ‖f t‖ ∂intervalMeasure) ≤ ‖f‖ := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  change (eLpNorm (fun t => f t) 1 intervalMeasure).toReal ≤
    (eLpNorm (fun t => f t) 2 intervalMeasure).toReal
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))

theorem norm_velocity_integral_le {n : ℕ} (u : Space n) {s t : ℝ}
    (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    ‖∫ x in s..t, velocity u x‖ ≤ ‖velocity u‖ := by
  have hsub : uIoc s t ⊆ Ioc 0 1 := by
    have hs' : s ∈ uIcc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    have ht' : t ∈ uIcc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
    have h : uIoc s t ⊆ uIoc (0 : ℝ) 1 :=
      uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hs' ht')
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h
  calc
    ‖∫ x in s..t, velocity u x‖ ≤ ∫ x in uIoc s t, ‖velocity u x‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ ≤ ∫ x in Ioc (0 : ℝ) 1, ‖velocity u x‖ := by
      apply setIntegral_mono_set (velocity_intervalIntegrable u).1.norm
      · exact Eventually.of_forall fun _ => norm_nonneg _
      · exact Eventually.of_forall hsub
    _ = ∫ x, ‖velocity u x‖ ∂intervalMeasure := by
      rw [integral_Ioc_eq_integral_Ioo]
      rfl
    _ ≤ ‖velocity u‖ := integral_norm_le_valueLp_norm _

theorem continuousRepresentative_increment_norm_le {n : ℕ} (u : Space n) {s t : ℝ}
    (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    ‖continuousRepresentative u t - continuousRepresentative u s‖ ≤ ‖velocity u‖ := by
  rw [continuousRepresentative_sub u hs ht]
  exact norm_velocity_integral_le u hs ht

theorem continuousRepresentative_norm_le {n : ℕ} (u : Space n) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    ‖continuousRepresentative u t‖ ≤ ‖value u‖ + ‖velocity u‖ := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hiv : Integrable (value u) intervalMeasure :=
    (Lp.memLp (value u)).integrable (by norm_num)
  have hiq : Integrable (continuousRepresentative u) intervalMeasure :=
    hiv.congr (value_ae_continuousRepresentative u)
  have hmem : ∀ᵐ s ∂intervalMeasure, s ∈ Icc (0 : ℝ) 1 :=
    (ae_restrict_mem measurableSet_Ioo).mono fun _ hs => Ioo_subset_Icc_self hs
  have hpoint : ∀ᵐ s ∂intervalMeasure,
      ‖continuousRepresentative u t‖ ≤ ‖continuousRepresentative u s‖ + ‖velocity u‖ := by
    filter_upwards [hmem] with s hs
    calc
      ‖continuousRepresentative u t‖ ≤
          ‖continuousRepresentative u s‖ +
            ‖continuousRepresentative u t - continuousRepresentative u s‖ :=
        norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖continuousRepresentative u s‖ + ‖velocity u‖ :=
        add_le_add le_rfl (continuousRepresentative_increment_norm_le u hs ht)
  have h := integral_mono_ae (integrable_const ‖continuousRepresentative u t‖)
    (hiq.norm.add (integrable_const ‖velocity u‖)) hpoint
  change (∫ s, ‖continuousRepresentative u t‖ ∂intervalMeasure) ≤
    ∫ s, ‖continuousRepresentative u s‖ + ‖velocity u‖ ∂intervalMeasure at h
  rw [integral_add hiq.norm (integrable_const _)] at h
  have hnorm : (∫ s, ‖continuousRepresentative u s‖ ∂intervalMeasure) =
      ∫ s, ‖value u s‖ ∂intervalMeasure :=
    integral_congr_ae ((value_ae_continuousRepresentative u).symm.fun_comp norm)
  rw [hnorm] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  exact h.trans (add_le_add (integral_norm_le_valueLp_norm (value u)) le_rfl)

theorem continuousRepresentative_norm_le_two {n : ℕ} (u : Space n) {t : ℝ}
    (ht : t ∈ Icc 0 1) : ‖continuousRepresentative u t‖ ≤ 2 * ‖u‖ := by
  calc
    ‖continuousRepresentative u t‖ ≤ ‖value u‖ + ‖velocity u‖ :=
      continuousRepresentative_norm_le u ht
    _ ≤ ‖u‖ + ‖u‖ := add_le_add (value_norm_le u) (velocity_norm_le u)
    _ = 2 * ‖u‖ := by ring

theorem continuousRepresentative_add {n : ℕ} (u v : Space n) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    continuousRepresentative (u + v) t =
      continuousRepresentative u t + continuousRepresentative v t := by
  have hvalue : value (u + v) = value u + value v := by
    exact (valueL n).map_add u v
  have hsum : value (u + v) =ᵐ[intervalMeasure]
      fun s => continuousRepresentative u s + continuousRepresentative v s := by
    rw [hvalue]
    filter_upwards [Lp.coeFn_add (value u) (value v),
      value_ae_continuousRepresentative u, value_ae_continuousRepresentative v] with s ha hu hv
    change (value u + value v) s = value u s + value v s at ha
    exact ha.trans (congrArg₂ (· + ·) hu hv)
  exact continuous_representative_unique (continuousRepresentative_continuousOn (u + v))
    ((continuousRepresentative_continuousOn u).add (continuousRepresentative_continuousOn v))
    (value_ae_continuousRepresentative (u + v)) hsum ht

theorem continuousRepresentative_smul {n : ℕ} (a : ℝ) (u : Space n) {t : ℝ}
    (ht : t ∈ Icc 0 1) :
    continuousRepresentative (a • u) t = a • continuousRepresentative u t := by
  have hvalue : value (a • u) = a • value u := by
    exact (valueL n).map_smul a u
  have hsmul : value (a • u) =ᵐ[intervalMeasure]
      fun s => a • continuousRepresentative u s := by
    rw [hvalue]
    filter_upwards [Lp.coeFn_smul a (value u), value_ae_continuousRepresentative u] with s ha hu
    change (a • value u) s = a • value u s at ha
    exact ha.trans (congrArg (fun x => a • x) hu)
  exact continuous_representative_unique (continuousRepresentative_continuousOn (a • u))
    ((continuousRepresentative_continuousOn u).const_smul a)
    (value_ae_continuousRepresentative (a • u)) hsmul ht

abbrev ClosedInterval := Icc (0 : ℝ) 1

def continuousRepresentativeMap {n : ℕ} (u : Space n) : C(ClosedInterval, Ambient n) :=
  ⟨fun t => continuousRepresentative u t,
    (continuousRepresentative_continuousOn u).domRestrict⟩

theorem continuousRepresentativeMap_norm_le {n : ℕ} (u : Space n) :
    ‖continuousRepresentativeMap u‖ ≤ 2 * ‖u‖ := by
  apply (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ 2 * ‖u‖)).mpr
  intro t
  exact continuousRepresentative_norm_le_two u t.property

def representativeLinear (n : ℕ) : Space n →ₗ[ℝ] C(ClosedInterval, Ambient n) where
  toFun := continuousRepresentativeMap
  map_add' u v := by
    apply ContinuousMap.ext
    intro t
    change continuousRepresentative (u + v) t =
      continuousRepresentative u t + continuousRepresentative v t
    exact continuousRepresentative_add u v t.property
  map_smul' a u := by
    apply ContinuousMap.ext
    intro t
    change continuousRepresentative (a • u) t = a • continuousRepresentative u t
    exact continuousRepresentative_smul a u t.property

def representativeL (n : ℕ) : Space n →L[ℝ] C(ClosedInterval, Ambient n) :=
  (representativeLinear n).mkContinuous 2 (by
    intro u
    exact continuousRepresentativeMap_norm_le u)

theorem representativeL_apply {n : ℕ} (u : Space n) (t : ClosedInterval) :
    representativeL n u t = continuousRepresentative u t := rfl

def traceL (n : ℕ) (t : ClosedInterval) : Space n →L[ℝ] Ambient n :=
  (ContinuousMap.evalCLM ℝ t).comp (representativeL n)

theorem traceL_apply {n : ℕ} (u : Space n) (t : ClosedInterval) :
    traceL n t u = continuousRepresentative u t := rfl

theorem traceL_norm_le (n : ℕ) (t : ClosedInterval) : ‖traceL n t‖ ≤ 2 := by
  apply (traceL n t).opNorm_le_bound (by norm_num)
  intro u
  exact continuousRepresentative_norm_le_two u t.property

def traceZeroL (n : ℕ) : Space n →L[ℝ] Ambient n := traceL n ⟨0, by norm_num⟩

def traceOneL (n : ℕ) : Space n →L[ℝ] Ambient n := traceL n ⟨1, by norm_num⟩

theorem traceZeroL_apply {n : ℕ} (u : Space n) : traceZeroL n u = traceZero u := rfl

theorem traceOneL_apply {n : ℕ} (u : Space n) : traceOneL n u = traceOne u := rfl

def periodicSubmodule (n : ℕ) : Submodule ℝ (Space n) :=
  (traceOneL n - traceZeroL n).ker

theorem mem_periodicSubmodule_iff {n : ℕ} (u : Space n) :
    u ∈ periodicSubmodule n ↔ traceOne u = traceZero u := by
  change traceOneL n u - traceZeroL n u = 0 ↔ _
  rw [traceOneL_apply, traceZeroL_apply, sub_eq_zero]

theorem mem_periodicSubmodule_iff_integral_zero {n : ℕ} (u : Space n) :
    u ∈ periodicSubmodule n ↔ (∫ x in (0 : ℝ)..1, velocity u x) = 0 := by
  rw [mem_periodicSubmodule_iff, trace_eq_iff_velocity_integral_eq_zero]

theorem periodicSubmodule_closed (n : ℕ) : IsClosed (periodicSubmodule n : Set (Space n)) :=
  (traceOneL n - traceZeroL n).isClosed_ker

theorem periodicSubmodule_complete (n : ℕ) : IsComplete (periodicSubmodule n : Set (Space n)) :=
  (periodicSubmodule_closed n).isComplete

instance (n : ℕ) : CompleteSpace (periodicSubmodule n) :=
  (periodicSubmodule_complete n).completeSpace_coe

theorem subintervalMeasure_le_intervalMeasure {s t : ℝ}
    (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    volume.restrict (uIoc s t) ≤ intervalMeasure := by
  have hs' : s ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  have ht' : t ∈ uIcc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  have hsub : uIoc s t ⊆ Ioc 0 1 := by
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      uIoc_subset_uIoc_of_uIcc_subset_uIcc (uIcc_subset_uIcc hs' ht')
  have hmeasure : volume.restrict (Ioc (0 : ℝ) 1) = intervalMeasure := by
    rw [restrict_Ioc_eq_restrict_Icc, ← restrict_Ioo_eq_restrict_Icc]
    rfl
  rw [← hmeasure]
  exact Measure.restrict_mono hsub le_rfl

theorem norm_valueLp_intervalIntegral_le_sqrt {n : ℕ} (f : ValueLp n) {s t : ℝ}
    (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    ‖∫ x in s..t, f x‖ ≤ Real.sqrt |t - s| * ‖f‖ := by
  let ν := volume.restrict (uIoc s t)
  have hle : ν ≤ intervalMeasure := subintervalMeasure_le_intervalMeasure hs ht
  have hf : MemLp (fun x => f x) 2 ν := (Lp.memLp f).mono_measure hle
  have hm : ν univ = ENNReal.ofReal |t - s| := by
    simp only [ν, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_uIoc]
  have hh : eLpNorm (fun x => f x) 1 ν ≤
      eLpNorm (fun x => f x) 2 intervalMeasure * (ENNReal.ofReal |t - s|) ^ (1 / (2 : ℝ)) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hf.aestronglyMeasurable
    rw [hm] at h
    norm_num at h
    apply h.trans
    gcongr
  have hfinite : eLpNorm (fun x => f x) 2 intervalMeasure *
      (ENNReal.ofReal |t - s|) ^ (1 / (2 : ℝ)) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
  have hreal := ENNReal.toReal_mono hfinite hh
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (abs_nonneg _), ← Real.sqrt_eq_rpow] at hreal
  calc
    ‖∫ x in s..t, f x‖ ≤ ∫ x in uIoc s t, ‖f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ = (eLpNorm (fun x => f x) 1 ν).toReal := by
      rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable,
        eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    _ ≤ (eLpNorm (fun x => f x) 2 intervalMeasure).toReal * Real.sqrt |t - s| := hreal
    _ = Real.sqrt |t - s| * ‖f‖ := by rw [mul_comm]; rfl

theorem continuousRepresentative_holder_half {n : ℕ} (u : Space n) {s t : ℝ}
    (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    ‖continuousRepresentative u t - continuousRepresentative u s‖ ≤
      Real.sqrt |t - s| * ‖velocity u‖ := by
  rw [continuousRepresentative_sub u hs ht]
  exact norm_valueLp_intervalIntegral_le_sqrt (velocity u) hs ht

theorem continuousRepresentative_holder_half_norm {n : ℕ} (u : Space n) {s t : ℝ}
    (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    ‖continuousRepresentative u t - continuousRepresentative u s‖ ≤
      Real.sqrt |t - s| * ‖u‖ := by
  exact (continuousRepresentative_holder_half u hs ht).trans
    (mul_le_mul_of_nonneg_left (velocity_norm_le u) (Real.sqrt_nonneg _))

end

end Finsler.IntervalSobolev
