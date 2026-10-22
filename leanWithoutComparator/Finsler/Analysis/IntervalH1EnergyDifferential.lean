module

public import Finsler.Geometry.AmbientEnergyRegularity
public import Finsler.Analysis.C1QuadraticGrowth
public import Finsler.Analysis.IntervalH1EnergyContinuity

/-! Genuine ambient energy differentials along arbitrary sphere H¹ weak jets.
Position coefficients are L¹, velocity coefficients are L², and the actual
first-variation candidate is integrable for every original H¹ direction.
This does not assert a Fréchet differential of the integral functional. -/

@[expose] public section

namespace Finsler.SobolevEnergyDifferential

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.AmbientLagrangian Finsler.AmbientEnergyRegularity Finsler.SobolevEnergy
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem fderiv_continuousOn (F : ReversibleMetric n) :
    ContinuousOn (fderiv ℝ (lagrangian F)) (nonzeroPosition n) := by
  intro z hz
  exact (lagrangian_fderiv_continuousAt F hz).continuousWithinAt

def differentialExtension (F : ReversibleMetric n) :
    Ambient n × Ambient n → (Ambient n × Ambient n →L[ℝ] ℝ) := by
  classical
  exact (nonzeroPosition n).piecewise (fderiv ℝ (lagrangian F)) (fun _ => 0)

theorem differentialExtension_eq (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z.1 ≠ 0) : differentialExtension F z = fderiv ℝ (lagrangian F) z := by
  classical
  exact piecewise_eq_of_mem (nonzeroPosition n) (fderiv ℝ (lagrangian F)) (fun _ => 0) hz

theorem differentialExtension_measurable (F : ReversibleMetric n) :
    Measurable (differentialExtension F) := by
  classical
  exact (fderiv_continuousOn F).measurable_piecewise continuousOn_const
    (nonzeroPosition_open n).measurableSet

theorem weakJet_position_ne_zero_ae (u : SphereLoop n) :
    ∀ᵐ t ∂intervalMeasure, (weakJet u t).1 ≠ 0 := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  change continuousRepresentative (u.data : Space n) t ≠ 0
  intro hz
  have h := u.sphere_constraint ⟨t, Ioo_subset_Icc_self ht⟩
  rw [hz, norm_zero] at h
  norm_num at h

theorem differential_aestronglyMeasurable (F : ReversibleMetric n) (u : SphereLoop n) :
    AEStronglyMeasurable (fun t => fderiv ℝ (lagrangian F) (weakJet u t)) intervalMeasure := by
  have h := ((differentialExtension_measurable F).comp_aemeasurable
    (weakJet_aestronglyMeasurable u).aemeasurable).aestronglyMeasurable
  apply h.congr
  filter_upwards [weakJet_position_ne_zero_ae u] with t ht
  exact differentialExtension_eq F ht

theorem position_aestronglyMeasurable (F : ReversibleMetric n) (u : SphereLoop n) :
    AEStronglyMeasurable (fun t => positionDifferential F (weakJet u t)) intervalMeasure := by
  change AEStronglyMeasurable (fun t =>
    (fderiv ℝ (lagrangian F) (weakJet u t)).comp
      (ContinuousLinearMap.inl ℝ (Ambient n) (Ambient n))) intervalMeasure
  exact (continuous_id.clm_comp continuous_const).comp_aestronglyMeasurable
    (differential_aestronglyMeasurable F u)

theorem velocity_aestronglyMeasurable (F : ReversibleMetric n) (u : SphereLoop n) :
    AEStronglyMeasurable (fun t => velocityDifferential F (weakJet u t)) intervalMeasure := by
  change AEStronglyMeasurable (fun t =>
    (fderiv ℝ (lagrangian F) (weakJet u t)).comp
      (ContinuousLinearMap.inr ℝ (Ambient n) (Ambient n))) intervalMeasure
  exact (continuous_id.clm_comp continuous_const).comp_aestronglyMeasurable
    (differential_aestronglyMeasurable F u)

theorem exists_sphere_partial_bounds (F : ReversibleMetric n) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : Ambient n, ‖q‖ = 1 → ∀ v : Ambient n,
      ‖positionDifferential F (q, v)‖ ≤ C * ‖v‖ ^ 2 ∧
      ‖velocityDifferential F (q, v)‖ ≤ C * ‖v‖ := by
  have hsub : Metric.sphere (0 : Ambient n) 1 ⊆ {q : Ambient n | q ≠ 0} := by
    intro q hq hz
    simp [hz] at hq
  obtain ⟨C, hC, hb⟩ := Finsler.C1QuadraticGrowth.exists_partial_bounds_on_compact
    (f := lagrangian F) (isCompact_sphere (0 : Ambient n) 1) hsub
    (fun q r v => Finsler.EnergyConservation.lagrangian_velocity_smul F q v r)
    (fun z hz => lagrangian_contDiffAt_one F hz)
  refine ⟨C, hC, fun q hq v => ?_⟩
  have hm : q ∈ Metric.sphere (0 : Ambient n) 1 := by simpa using hq
  exact (hb q hm v).2

theorem exists_weakJet_partial_bounds (F : ReversibleMetric n) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : SphereLoop n, ∀ᵐ t ∂intervalMeasure,
      ‖positionDifferential F (weakJet u t)‖ ≤ C * ‖velocity (u.data : Space n) t‖ ^ 2 ∧
      ‖velocityDifferential F (weakJet u t)‖ ≤ C * ‖velocity (u.data : Space n) t‖ := by
  obtain ⟨C, hC, hb⟩ := exists_sphere_partial_bounds F
  refine ⟨C, hC, fun u => ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact hb _ (u.sphere_constraint ⟨t, Ioo_subset_Icc_self ht⟩) _

theorem position_integrable (F : ReversibleMetric n) (u : SphereLoop n) :
    Integrable (fun t => positionDifferential F (weakJet u t)) intervalMeasure := by
  obtain ⟨C, _hC, hb⟩ := exists_weakJet_partial_bounds F
  exact ((integrable_velocity_sq (u.data : Space n)).const_mul C).mono'
    (position_aestronglyMeasurable F u) ((hb u).mono fun _ ht => ht.1)

theorem velocity_memLp_two (F : ReversibleMetric n) (u : SphereLoop n) :
    MemLp (fun t => velocityDifferential F (weakJet u t)) 2 intervalMeasure := by
  obtain ⟨C, _hC, hb⟩ := exists_weakJet_partial_bounds F
  exact ((Lp.memLp (velocity (u.data : Space n))).norm.const_mul C).mono'
    (velocity_aestronglyMeasurable F u) ((hb u).mono fun _ ht => ht.2)

theorem position_variation_integrable (F : ReversibleMetric n) (u : SphereLoop n)
    (h : Space n) : Integrable (fun t =>
      positionDifferential F (weakJet u t) (continuousRepresentative h t)) intervalMeasure := by
  have hr := (Lp.aestronglyMeasurable (value h)).congr (value_ae_continuousRepresentative h)
  have hc : Continuous (fun p : (Ambient n →L[ℝ] ℝ) × Ambient n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hm := hc.comp_aestronglyMeasurable ((position_aestronglyMeasurable F u).prodMk hr)
  apply ((position_integrable F u).norm.const_mul (2 * ‖h‖)).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  calc
    ‖positionDifferential F (weakJet u t) (continuousRepresentative h t)‖ ≤
        ‖positionDifferential F (weakJet u t)‖ * ‖continuousRepresentative h t‖ :=
      (positionDifferential F (weakJet u t)).le_opNorm _
    _ ≤ ‖positionDifferential F (weakJet u t)‖ * (2 * ‖h‖) :=
      mul_le_mul_of_nonneg_left (continuousRepresentative_norm_le_two h
        (Ioo_subset_Icc_self ht)) (norm_nonneg _)
    _ = (2 * ‖h‖) * ‖positionDifferential F (weakJet u t)‖ := mul_comm _ _

theorem velocity_variation_integrable (F : ReversibleMetric n) (u : SphereLoop n)
    (h : Space n) : Integrable (fun t =>
      velocityDifferential F (weakJet u t) (velocity h t)) intervalMeasure := by
  have hc : Continuous (fun p : (Ambient n →L[ℝ] ℝ) × Ambient n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hm := hc.comp_aestronglyMeasurable ((velocity_aestronglyMeasurable F u).prodMk
    (Lp.aestronglyMeasurable (velocity h)))
  apply ((velocity_memLp_two F u).norm.integrable_mul (Lp.memLp (velocity h)).norm).mono' hm
  exact ae_of_all _ fun t => (velocityDifferential F (weakJet u t)).le_opNorm _

def variationCandidate (F : ReversibleMetric n) (u : SphereLoop n) (h : Space n) : ℝ :=
  ∫ t, positionDifferential F (weakJet u t) (continuousRepresentative h t) +
    velocityDifferential F (weakJet u t) (velocity h t) ∂intervalMeasure

theorem variationCandidate_integrable (F : ReversibleMetric n) (u : SphereLoop n)
    (h : Space n) : Integrable (fun t =>
      positionDifferential F (weakJet u t) (continuousRepresentative h t) +
      velocityDifferential F (weakJet u t) (velocity h t)) intervalMeasure :=
  (position_variation_integrable F u h).add (velocity_variation_integrable F u h)

theorem variationCandidate_eq_full_differential (F : ReversibleMetric n)
    (u : SphereLoop n) (h : Space n) : variationCandidate F u h =
      ∫ t, fderiv ℝ (lagrangian F) (weakJet u t)
        (continuousRepresentative h t, velocity h t) ∂intervalMeasure := by
  apply integral_congr_ae
  exact ae_of_all _ fun t => (differential_split F (weakJet u t)
    (continuousRepresentative h t) (velocity h t)).symm

end

end Finsler.SobolevEnergyDifferential
