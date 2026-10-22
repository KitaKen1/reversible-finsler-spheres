module

public import Finsler.Analysis.IntervalH1EnergyNeighbourhood

/-! Continuity of actual energy, L1/L2 coefficients and the candidate differential
on genuine ambient open H1 neighbourhoods. A.e. subsequences and Vitali
handle arbitrary original strong-H1 sequences without a fixed dominator.
This is not yet differentiation of integral energy. -/

@[expose] public section

namespace Finsler.AmbientSobolevEnergy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.AmbientLagrangian Finsler.AmbientEnergyRegularity Finsler.SobolevEnergy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

variable {n : ℕ}
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem localSpace_tendsto {I : Type*} {l : Filter I} {u : SphereLoop n}
    {v : I → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => (v i : Space n)) l (𝓝 (w : Space n)) :=
  continuous_subtype_val.tendsto w |>.comp hv

theorem localSpace_representative_tendsto {I : Type*} {l : Filter I} {u : SphereLoop n}
    {v : I → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v l (𝓝 w))
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    Tendsto (fun i => continuousRepresentative (v i : Space n) t) l
      (𝓝 (continuousRepresentative (w : Space n) t)) := by
  have h := (traceL n ⟨t, ht⟩).continuous.tendsto (w : Space n) |>.comp (localSpace_tendsto hv)
  exact h

theorem localSpace_velocity_tendsto {I : Type*} {l : Filter I} {u : SphereLoop n}
    {v : I → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun i => velocity (v i : Space n)) l (𝓝 (velocity (w : Space n))) :=
  (velocityL n).continuous.tendsto (w : Space n) |>.comp (localSpace_tendsto hv)

theorem density_seq_unifIntegrable (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w)) :
    UnifIntegrable (fun i t => lagrangian F (ambientJet (v i : Space n) t)) 1 intervalMeasure := by
  obtain ⟨C, hC, hb⟩ := exists_local_jet_bounds F
  exact Finsler.CoefficientVitali.lp_convergent_quadratic_unifIntegrable
    (localSpace_velocity_tendsto hv) (fun i => density_aestronglyMeasurable F (v i)) hC.le
    (fun i => (hb u (v i)).mono fun _ ht => ht.1)

theorem density_ae_tendsto_of_velocity_ae_tendsto (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w))
    (hvel : ∀ᵐ t ∂intervalMeasure, Tendsto (fun i => velocity (v i : Space n) t) atTop
      (𝓝 (velocity (w : Space n) t))) :
    ∀ᵐ t ∂intervalMeasure,
      Tendsto (fun i => lagrangian F (ambientJet (v i : Space n) t)) atTop
        (𝓝 (lagrangian F (ambientJet (w : Space n) t))) := by
  filter_upwards [hvel, localJet_position_ne_zero_ae w, ae_restrict_mem measurableSet_Ioo]
    with t ht hz hi
  have hq := localSpace_representative_tendsto hv (Ioo_subset_Icc_self hi)
  exact ((lagrangian_contDiffAt_one F hz).continuousAt.tendsto).comp (hq.prodMk_nhds ht)

theorem density_seq_tendsto_L1 (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun i => eLpNorm
      ((fun t => lagrangian F (ambientJet (v i : Space n) t)) -
        fun t => lagrangian F (ambientJet (w : Space n) t)) 1 intervalMeasure) atTop (𝓝 0) := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hui := density_seq_unifIntegrable F hv
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hvns := localSpace_velocity_tendsto (hv.comp hns)
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvns).exists_seq_tendsto_ae
  have hsub := hv.comp (hns.comp hms.tendsto_atTop)
  exact ⟨ms, tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun i => density_aestronglyMeasurable F (v (ns (ms i))))
    (memLp_one_iff_integrable.mpr (density_integrable F w))
    (hui.comp (fun i => ns (ms i))) (density_ae_tendsto_of_velocity_ae_tendsto F hsub hae)⟩

theorem energy_tendsto_seq (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun i => ambientEnergy F (v i : Space n)) atTop
      (𝓝 (ambientEnergy F (w : Space n))) :=
  tendsto_integral_of_L1' _ (Eventually.of_forall fun i => density_integrable F (v i))
    (density_seq_tendsto_L1 F hv)

theorem local_energy_continuous (F : ReversibleMetric n) (u : SphereLoop n) :
    Continuous (fun v : LocalSpace u => ambientEnergy F (v : Space n)) := by
  apply continuous_iff_seqContinuous.mpr
  intro v w hv
  exact energy_tendsto_seq F hv

theorem ambientEnergy_continuousOn_neighbourhood (F : ReversibleMetric n) (u : SphereLoop n) :
    ContinuousOn (ambientEnergy F) (neighbourhood u) :=
  continuousOn_iff_continuous_domRestrict.mpr (local_energy_continuous F u)

theorem ambientEnergy_continuousAt_centre (F : ReversibleMetric n) (u : SphereLoop n) :
    ContinuousAt (ambientEnergy F) (u.data : Space n) :=
  (ambientEnergy_continuousOn_neighbourhood F u).continuousAt (neighbourhood_mem_nhds u)

theorem position_seq_unifIntegrable (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w)) :
    UnifIntegrable (fun i t => positionDifferential F (ambientJet ((v i) : Space n) t)) 1 intervalMeasure := by
  obtain ⟨C, hC, hb⟩ := exists_local_jet_bounds F
  exact Finsler.CoefficientVitali.lp_convergent_quadratic_unifIntegrable
    (localSpace_velocity_tendsto hv) (fun i => position_aestronglyMeasurable F (v i)) hC.le
    (fun i => (hb u (v i)).mono fun _ ht => ht.2.1)

theorem velocity_seq_unifIntegrable (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w)) :
    UnifIntegrable (fun i t => velocityDifferential F (ambientJet ((v i) : Space n) t)) 2 intervalMeasure := by
  obtain ⟨C, hC, hb⟩ := exists_local_jet_bounds F
  exact Finsler.CoefficientVitali.lp_convergent_linear_unifIntegrable
    (localSpace_velocity_tendsto hv) (fun i => velocity_aestronglyMeasurable F (v i)) hC.le
    (fun i => (hb u (v i)).mono fun _ ht => ht.2.2)

theorem partials_ae_tendsto_of_velocity_ae_tendsto (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w))
    (hvel : ∀ᵐ t ∂intervalMeasure,
      Tendsto (fun i => velocity ((v i) : Space n) t) atTop
        (𝓝 (velocity (w : Space n) t))) :
    ∀ᵐ t ∂intervalMeasure,
      Tendsto (fun i => positionDifferential F (ambientJet ((v i) : Space n) t)) atTop
        (𝓝 (positionDifferential F (ambientJet (w : Space n) t))) ∧
      Tendsto (fun i => velocityDifferential F (ambientJet ((v i) : Space n) t)) atTop
        (𝓝 (velocityDifferential F (ambientJet (w : Space n) t))) := by
  filter_upwards [hvel, localJet_position_ne_zero_ae w, ae_restrict_mem measurableSet_Ioo]
    with t ht hz hi
  have hq := localSpace_representative_tendsto hv (Ioo_subset_Icc_self hi)
  have hd := (lagrangian_fderiv_continuousAt F hz).tendsto.comp (hq.prodMk_nhds ht)
  have hp : Continuous (fun D : Ambient n × Ambient n →L[ℝ] ℝ =>
      D.comp (ContinuousLinearMap.inl ℝ (Ambient n) (Ambient n))) :=
    continuous_id.clm_comp continuous_const
  have hs : Continuous (fun D : Ambient n × Ambient n →L[ℝ] ℝ =>
      D.comp (ContinuousLinearMap.inr ℝ (Ambient n) (Ambient n))) :=
    continuous_id.clm_comp continuous_const
  exact ⟨hp.continuousAt.tendsto.comp hd, hs.continuousAt.tendsto.comp hd⟩

theorem position_seq_tendsto_L1 (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun i => eLpNorm
      ((fun t => positionDifferential F (ambientJet ((v i) : Space n) t)) -
        fun t => positionDifferential F (ambientJet (w : Space n) t)) 1 intervalMeasure) atTop (𝓝 0) := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hui := position_seq_unifIntegrable F hv
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hvns := localSpace_velocity_tendsto (hv.comp hns)
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvns).exists_seq_tendsto_ae
  have hsub := hv.comp (hns.comp hms.tendsto_atTop)
  refine ⟨ms, tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun i => position_aestronglyMeasurable F (v (ns (ms i))))
    (memLp_one_iff_integrable.mpr (position_integrable F w))
    (hui.comp (fun i => ns (ms i))) ?_⟩
  exact (partials_ae_tendsto_of_velocity_ae_tendsto F hsub hae).mono fun _ ht => ht.1

theorem velocity_seq_tendsto_L2 (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun i => eLpNorm
      ((fun t => velocityDifferential F (ambientJet ((v i) : Space n) t)) -
        fun t => velocityDifferential F (ambientJet (w : Space n) t)) 2 intervalMeasure) atTop (𝓝 0) := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hui := velocity_seq_unifIntegrable F hv
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hvns := localSpace_velocity_tendsto (hv.comp hns)
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvns).exists_seq_tendsto_ae
  have hsub := hv.comp (hns.comp hms.tendsto_atTop)
  refine ⟨ms, tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun i => velocity_aestronglyMeasurable F (v (ns (ms i))))
    (velocity_memLp_two F w) (hui.comp (fun i => ns (ms i))) ?_⟩
  exact (partials_ae_tendsto_of_velocity_ae_tendsto F hsub hae).mono fun _ ht => ht.2

theorem positionCoefficient_tendsto_seq (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun i => positionCoefficient F (v i)) atTop (𝓝 (positionCoefficient F w)) :=
  (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun i t => positionDifferential F (ambientJet (v i : Space n) t))
    (fun i => memLp_one_iff_integrable.mpr (position_integrable F (v i)))
    (fun t => positionDifferential F (ambientJet (w : Space n) t))
    (memLp_one_iff_integrable.mpr (position_integrable F w))).mpr (position_seq_tendsto_L1 F hv)

theorem velocityCoefficient_tendsto_seq (F : ReversibleMetric n)
    {u : SphereLoop n} {v : ℕ → LocalSpace u} {w : LocalSpace u} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun i => velocityCoefficient F (v i)) atTop (𝓝 (velocityCoefficient F w)) :=
  (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun i t => velocityDifferential F (ambientJet (v i : Space n) t))
    (fun i => velocity_memLp_two F (v i))
    (fun t => velocityDifferential F (ambientJet (w : Space n) t))
    (velocity_memLp_two F w)).mpr (velocity_seq_tendsto_L2 F hv)

theorem positionCoefficient_continuous (F : ReversibleMetric n) (u : SphereLoop n) :
    Continuous (fun v : LocalSpace u => positionCoefficient F v) := by
  apply continuous_iff_seqContinuous.mpr
  intro v w hv
  exact positionCoefficient_tendsto_seq F hv

theorem velocityCoefficient_continuous (F : ReversibleMetric n) (u : SphereLoop n) :
    Continuous (fun v : LocalSpace u => velocityCoefficient F v) := by
  apply continuous_iff_seqContinuous.mpr
  intro v w hv
  exact velocityCoefficient_tendsto_seq F hv

theorem variationL_continuous (F : ReversibleMetric n) (u : SphereLoop n) :
    Continuous (fun v : LocalSpace u => variationL F v) :=
  Finsler.SobolevEnergyDifferential.coefficientPairingL_continuous.comp
    ((positionCoefficient_continuous F u).prodMk (velocityCoefficient_continuous F u))

theorem variationL_norm_sub_le (F : ReversibleMetric n) {u : SphereLoop n}
    (v w : LocalSpace u) : ‖variationL F v - variationL F w‖ ≤
      2 * ‖positionCoefficient F v - positionCoefficient F w‖ +
        ‖velocityCoefficient F v - velocityCoefficient F w‖ :=
  Finsler.SobolevEnergyDifferential.coefficientPairingL_norm_sub_le _ _ _ _

theorem variationL_joint_continuous (F : ReversibleMetric n) (u : SphereLoop n) :
    Continuous (fun p : LocalSpace u × Space n => variationL F p.1 p.2) :=
  ((variationL_continuous F u).comp continuous_fst).clm_apply continuous_snd

end

end Finsler.AmbientSobolevEnergy

