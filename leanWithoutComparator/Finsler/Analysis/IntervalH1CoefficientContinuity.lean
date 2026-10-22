module

public import Finsler.Analysis.IntervalH1VariationLinear
public import Finsler.Analysis.L2CoefficientUniformIntegrability

/-! Strong L¹/L² convergence of the actual first-variation coefficients
along original strongly converging sphere H¹ loops. Vitali replaces an
unavailable fixed pointwise dominator for arbitrary L² velocities. The
Fréchet difference quotient of the energy remains a separate obligation. -/

@[expose] public section

namespace Finsler.SobolevEnergyDifferential

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.AmbientLagrangian Finsler.AmbientEnergyRegularity Finsler.SobolevEnergy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem position_seq_unifIntegrable (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    UnifIntegrable (fun i t => positionDifferential F (weakJet (v i) t)) 1 intervalMeasure := by
  obtain ⟨C, hC, hb⟩ := exists_weakJet_partial_bounds F
  exact Finsler.CoefficientVitali.lp_convergent_quadratic_unifIntegrable
    (sphereLoop_velocity_tendsto hv) (fun i => position_aestronglyMeasurable F (v i)) hC.le
    (fun i => (hb (v i)).mono fun _ ht => ht.1)

theorem velocity_seq_unifIntegrable (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    UnifIntegrable (fun i t => velocityDifferential F (weakJet (v i) t)) 2 intervalMeasure := by
  obtain ⟨C, hC, hb⟩ := exists_weakJet_partial_bounds F
  exact Finsler.CoefficientVitali.lp_convergent_linear_unifIntegrable
    (sphereLoop_velocity_tendsto hv) (fun i => velocity_aestronglyMeasurable F (v i)) hC.le
    (fun i => (hb (v i)).mono fun _ ht => ht.2)

theorem partials_ae_tendsto_of_velocity_ae_tendsto (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u))
    (hvel : ∀ᵐ t ∂intervalMeasure,
      Tendsto (fun i => velocity ((v i).data : Space n) t) atTop
        (𝓝 (velocity (u.data : Space n) t))) :
    ∀ᵐ t ∂intervalMeasure,
      Tendsto (fun i => positionDifferential F (weakJet (v i) t)) atTop
        (𝓝 (positionDifferential F (weakJet u t))) ∧
      Tendsto (fun i => velocityDifferential F (weakJet (v i) t)) atTop
        (𝓝 (velocityDifferential F (weakJet u t))) := by
  filter_upwards [hvel, weakJet_position_ne_zero_ae u, ae_restrict_mem measurableSet_Ioo]
    with t ht hz hi
  have hq := sphereLoop_representative_tendsto hv (Ioo_subset_Icc_self hi)
  have hd := (lagrangian_fderiv_continuousAt F hz).tendsto.comp (hq.prodMk_nhds ht)
  have hp : Continuous (fun D : Ambient n × Ambient n →L[ℝ] ℝ =>
      D.comp (ContinuousLinearMap.inl ℝ (Ambient n) (Ambient n))) :=
    continuous_id.clm_comp continuous_const
  have hs : Continuous (fun D : Ambient n × Ambient n →L[ℝ] ℝ =>
      D.comp (ContinuousLinearMap.inr ℝ (Ambient n) (Ambient n))) :=
    continuous_id.clm_comp continuous_const
  exact ⟨hp.continuousAt.tendsto.comp hd, hs.continuousAt.tendsto.comp hd⟩

theorem position_seq_tendsto_L1 (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun i => eLpNorm
      ((fun t => positionDifferential F (weakJet (v i) t)) -
        fun t => positionDifferential F (weakJet u t)) 1 intervalMeasure) atTop (𝓝 0) := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hui := position_seq_unifIntegrable F hv
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hvns := sphereLoop_velocity_tendsto (hv.comp hns)
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvns).exists_seq_tendsto_ae
  have hsub := hv.comp (hns.comp hms.tendsto_atTop)
  refine ⟨ms, tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun i => position_aestronglyMeasurable F (v (ns (ms i))))
    (memLp_one_iff_integrable.mpr (position_integrable F u))
    (hui.comp (fun i => ns (ms i))) ?_⟩
  exact (partials_ae_tendsto_of_velocity_ae_tendsto F hsub hae).mono fun _ ht => ht.1

theorem velocity_seq_tendsto_L2 (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun i => eLpNorm
      ((fun t => velocityDifferential F (weakJet (v i) t)) -
        fun t => velocityDifferential F (weakJet u t)) 2 intervalMeasure) atTop (𝓝 0) := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hui := velocity_seq_unifIntegrable F hv
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hvns := sphereLoop_velocity_tendsto (hv.comp hns)
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvns).exists_seq_tendsto_ae
  have hsub := hv.comp (hns.comp hms.tendsto_atTop)
  refine ⟨ms, tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun i => velocity_aestronglyMeasurable F (v (ns (ms i))))
    (velocity_memLp_two F u) (hui.comp (fun i => ns (ms i))) ?_⟩
  exact (partials_ae_tendsto_of_velocity_ae_tendsto F hsub hae).mono fun _ ht => ht.2

def positionCoefficient (F : ReversibleMetric n) (u : SphereLoop n) :
    Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure :=
  (memLp_one_iff_integrable.mpr (position_integrable F u)).toLp
    (fun t => positionDifferential F (weakJet u t))

def velocityCoefficient (F : ReversibleMetric n) (u : SphereLoop n) :
    Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure :=
  (velocity_memLp_two F u).toLp (fun t => velocityDifferential F (weakJet u t))

theorem positionCoefficient_apply_ae (F : ReversibleMetric n) (u : SphereLoop n) :
    positionCoefficient F u =ᵐ[intervalMeasure] fun t => positionDifferential F (weakJet u t) :=
  MemLp.coeFn_toLp _

theorem velocityCoefficient_apply_ae (F : ReversibleMetric n) (u : SphereLoop n) :
    velocityCoefficient F u =ᵐ[intervalMeasure] fun t => velocityDifferential F (weakJet u t) :=
  MemLp.coeFn_toLp _

theorem positionCoefficient_tendsto_seq (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun i => positionCoefficient F (v i)) atTop (𝓝 (positionCoefficient F u)) :=
  (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun i t => positionDifferential F (weakJet (v i) t))
    (fun i => memLp_one_iff_integrable.mpr (position_integrable F (v i)))
    (fun t => positionDifferential F (weakJet u t))
    (memLp_one_iff_integrable.mpr (position_integrable F u))).mpr (position_seq_tendsto_L1 F hv)

theorem velocityCoefficient_tendsto_seq (F : ReversibleMetric n)
    {v : ℕ → SphereLoop n} {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun i => velocityCoefficient F (v i)) atTop (𝓝 (velocityCoefficient F u)) :=
  (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun i t => velocityDifferential F (weakJet (v i) t))
    (fun i => velocity_memLp_two F (v i))
    (fun t => velocityDifferential F (weakJet u t)) (velocity_memLp_two F u)).mpr
      (velocity_seq_tendsto_L2 F hv)

theorem positionCoefficient_continuous (F : ReversibleMetric n) :
    Continuous (positionCoefficient F) := by
  apply continuous_iff_seqContinuous.mpr
  intro v u hv
  exact positionCoefficient_tendsto_seq F hv

theorem velocityCoefficient_continuous (F : ReversibleMetric n) :
    Continuous (velocityCoefficient F) := by
  apply continuous_iff_seqContinuous.mpr
  intro v u hv
  exact velocityCoefficient_tendsto_seq F hv

end

end Finsler.SobolevEnergyDifferential
