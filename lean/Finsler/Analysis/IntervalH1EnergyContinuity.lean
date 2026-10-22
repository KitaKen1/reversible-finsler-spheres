module

public import Finsler.Analysis.IntervalH1ReflectionAction
public import Finsler.Analysis.L2QuadraticUniformIntegrability
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Sequences

/-! Actual Finsler energy is continuous in the original strong H¹ metric.
L² velocity convergence and the genuine quadratic density bound supply uniform
L¹ integrability. An a.e. convergent velocity subsequence, bounded trace maps
and density continuity permit Vitali. No first variation is assumed. -/

@[expose] public section

namespace Finsler.SobolevEnergy

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.Geometry
open Finsler.AmbientLagrangian Finsler.QuadraticVitali
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem sphereLoop_representative_tendsto {n : ℕ} {I : Type*} {l : Filter I}
    {v : I → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v l (𝓝 u))
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    Tendsto (fun i => continuousRepresentative ((v i).data : Space n) t) l
      (𝓝 (continuousRepresentative (u.data : Space n) t)) := by
  have h := ((traceL n ⟨t, ht⟩).continuous.tendsto (u.data : Space n)).comp
    (sphereLoop_tendsto_iff.mp hv)
  change Tendsto (fun i => traceL n ⟨t, ht⟩ ((v i).data : Space n)) l
    (𝓝 (traceL n ⟨t, ht⟩ (u.data : Space n))) at h
  simpa only [traceL_apply] using h

theorem sphereLoop_velocity_tendsto {n : ℕ} {I : Type*} {l : Filter I}
    {v : I → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v l (𝓝 u)) :
    Tendsto (fun i => velocity ((v i).data : Space n)) l
      (𝓝 (velocity (u.data : Space n))) :=
  (velocityL n).continuous.tendsto (u.data : Space n) |>.comp (sphereLoop_tendsto_iff.mp hv)

theorem density_seq_unifIntegrable {n : ℕ} (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    UnifIntegrable (fun i t => lagrangian F (weakJet (v i) t)) 1 intervalMeasure := by
  obtain ⟨c, C, _hc, hC, hb⟩ := exists_density_bounds F
  apply lp_convergent_quadratic_unifIntegrable (sphereLoop_velocity_tendsto hv)
    (fun i => density_aestronglyMeasurable F (v i)) hC.le
  intro i
  filter_upwards [hb (v i)] with t ht
  simpa only [Real.norm_eq_abs, abs_of_nonneg (density_nonneg F (v i) t)] using ht.2

theorem density_ae_tendsto_of_velocity_ae_tendsto {n : ℕ} (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u))
    (hvel : ∀ᵐ t ∂intervalMeasure,
      Tendsto (fun i => velocity ((v i).data : Space n) t) atTop
        (𝓝 (velocity (u.data : Space n) t))) :
    ∀ᵐ t ∂intervalMeasure, Tendsto (fun i => lagrangian F (weakJet (v i) t)) atTop
      (𝓝 (lagrangian F (weakJet u t))) := by
  filter_upwards [hvel, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  have hq := sphereLoop_representative_tendsto hv (Ioo_subset_Icc_self hmem)
  have hz : weakJet u t ∈ nonzeroPosition n := by
    change continuousRepresentative (u.data : Space n) t ≠ 0
    intro hzero
    have hs := u.sphere_constraint ⟨t, Ioo_subset_Icc_self hmem⟩
    rw [hzero, norm_zero] at hs
    norm_num at hs
  have hcont := (density_continuousOn F).continuousAt ((nonzeroPosition_open n).mem_nhds hz)
  exact hcont.tendsto.comp (hq.prodMk_nhds ht)

theorem density_seq_tendsto_L1 {n : ℕ} (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun i => eLpNorm
      ((fun t => lagrangian F (weakJet (v i) t)) - fun t => lagrangian F (weakJet u t))
      1 intervalMeasure) atTop (𝓝 0) := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hui := density_seq_unifIntegrable F hv
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hvns := sphereLoop_velocity_tendsto (hv.comp hns)
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvns).exists_seq_tendsto_ae
  have hsub := hv.comp (hns.comp hms.tendsto_atTop)
  refine ⟨ms, tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun i => density_aestronglyMeasurable F (v (ns (ms i))))
    (memLp_one_iff_integrable.mpr (density_integrable F u))
    (hui.comp (fun i => ns (ms i))) (density_ae_tendsto_of_velocity_ae_tendsto F hsub hae)⟩

theorem energy_tendsto_seq {n : ℕ} (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun i => energy F (v i)) atTop (𝓝 (energy F u)) := by
  change Tendsto (fun i => ∫ t, lagrangian F (weakJet (v i) t) ∂intervalMeasure) atTop
    (𝓝 (∫ t, lagrangian F (weakJet u t) ∂intervalMeasure))
  exact tendsto_integral_of_L1' _ (Eventually.of_forall fun i => density_integrable F (v i))
    (density_seq_tendsto_L1 F hv)

theorem energy_continuous {n : ℕ} (F : ReversibleMetric n) : Continuous (energy F) := by
  apply continuous_iff_seqContinuous.mpr
  intro v u hv
  exact energy_tendsto_seq F hv

theorem sqrt_energy_continuous {n : ℕ} (F : ReversibleMetric n) :
    Continuous (fun u : SphereLoop n => Real.sqrt (energy F u)) :=
  Real.continuous_sqrt.comp (energy_continuous F)

end

end Finsler.SobolevEnergy
