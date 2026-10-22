module

public import Finsler.Analysis.IntervalH1VariationContinuity

/-! Actual ambient energy on a genuine open ball in the original weak H¹ space.
The 1/8 ball around each sphere loop stays inside a compact nonzero-position
annulus. All velocities, including radial and zero velocities, are admitted.
No Frechet derivative of integral energy or sphere H¹ chart is asserted. -/

@[expose] public section

namespace Finsler.AmbientSobolevEnergy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.AmbientLagrangian Finsler.AmbientEnergyRegularity Finsler.SobolevEnergy
open Finsler.SobolevEnergyDifferential MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

noncomputable section

variable {n : ℕ}
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def neighbourhood (u : SphereLoop n) : Set (Space n) :=
  Metric.ball (u.data : Space n) (1 / 8)

abbrev LocalSpace (u : SphereLoop n) := ↥(neighbourhood u)

theorem neighbourhood_open (u : SphereLoop n) : IsOpen (neighbourhood u) := Metric.isOpen_ball

theorem centre_mem_neighbourhood (u : SphereLoop n) : (u.data : Space n) ∈ neighbourhood u :=
  Metric.mem_ball_self (by norm_num)

theorem neighbourhood_mem_nhds (u : SphereLoop n) :
    neighbourhood u ∈ 𝓝 (u.data : Space n) := Metric.ball_mem_nhds _ (by norm_num)

theorem neighbourhood_convex (u : SphereLoop n) : Convex ℝ (neighbourhood u) :=
  convex_ball _ _

def centre (u : SphereLoop n) : LocalSpace u := ⟨u.data, centre_mem_neighbourhood u⟩

theorem representative_norm_bounds_of_mem_neighbourhood (u : SphereLoop n)
    {v : Space n} (hv : v ∈ neighbourhood u) {t : ℝ} (ht : t ∈ Icc 0 1) :
    3 / 4 < ‖continuousRepresentative v t‖ ∧ ‖continuousRepresentative v t‖ < 5 / 4 := by
  have hd : ‖v - (u.data : Space n)‖ < 1 / 8 := by
    simpa only [neighbourhood, Metric.mem_ball, dist_eq_norm] using hv
  have hp : ‖continuousRepresentative v t - continuousRepresentative (u.data : Space n) t‖ ≤
      2 * ‖v - (u.data : Space n)‖ := by
    have h := continuousRepresentative_norm_le_two (v - (u.data : Space n)) ht
    change ‖traceL n ⟨t, ht⟩ (v - (u.data : Space n))‖ ≤ _ at h
    rw [map_sub] at h
    exact h
  have hn := u.sphere_constraint ⟨t, ht⟩
  have h1 := norm_sub_norm_le (continuousRepresentative v t)
    (continuousRepresentative (u.data : Space n) t)
  have h2 := norm_sub_norm_le (continuousRepresentative (u.data : Space n) t)
    (continuousRepresentative v t)
  rw [norm_sub_rev] at h2
  constructor <;> linarith

def compactAnnulus (n : ℕ) : Set (Ambient n) :=
  {q | 3 / 4 ≤ ‖q‖ ∧ ‖q‖ ≤ 5 / 4}

theorem compactAnnulus_compact (n : ℕ) : IsCompact (compactAnnulus n) := by
  have he : compactAnnulus n = Metric.closedBall (0 : Ambient n) (5 / 4) ∩
      {q : Ambient n | 3 / 4 ≤ ‖q‖} := by
    ext q
    simp only [compactAnnulus, mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall,
      dist_zero_right]
    exact and_comm
  rw [he]
  exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const continuous_norm)

theorem compactAnnulus_nonzero (n : ℕ) : compactAnnulus n ⊆ {q : Ambient n | q ≠ 0} := by
  intro q hq hz
  have h := hq.1
  rw [hz, norm_zero] at h
  norm_num at h

def ambientJet (v : Space n) (t : ℝ) : Ambient n × Ambient n :=
  (continuousRepresentative v t, velocity v t)

theorem ambientJet_sphereLoop (u : SphereLoop n) :
    ambientJet (u.data : Space n) = weakJet u := rfl

theorem ambientJet_aestronglyMeasurable (v : Space n) :
    AEStronglyMeasurable (ambientJet v) intervalMeasure :=
  ((Lp.aestronglyMeasurable (value v)).congr (value_ae_continuousRepresentative v)).prodMk
    (Lp.aestronglyMeasurable (velocity v))

theorem localJet_position_mem_annulus_ae {u : SphereLoop n} (v : LocalSpace u) :
    ∀ᵐ t ∂intervalMeasure, (ambientJet (v : Space n) t).1 ∈ compactAnnulus n := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have h := representative_norm_bounds_of_mem_neighbourhood u v.property (Ioo_subset_Icc_self ht)
  exact ⟨h.1.le, h.2.le⟩

theorem localJet_position_ne_zero_ae {u : SphereLoop n} (v : LocalSpace u) :
    ∀ᵐ t ∂intervalMeasure, (ambientJet (v : Space n) t).1 ≠ 0 :=
  (localJet_position_mem_annulus_ae v).mono fun _ ht => compactAnnulus_nonzero n ht

theorem exists_annulus_bounds (F : ReversibleMetric n) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ compactAnnulus n, ∀ v : Ambient n,
      ‖lagrangian F (q, v)‖ ≤ C * ‖v‖ ^ 2 ∧
      ‖positionDifferential F (q, v)‖ ≤ C * ‖v‖ ^ 2 ∧
      ‖velocityDifferential F (q, v)‖ ≤ C * ‖v‖ :=
  Finsler.C1QuadraticGrowth.exists_partial_bounds_on_compact
    (compactAnnulus_compact n) (compactAnnulus_nonzero n)
    (fun q r v => Finsler.EnergyConservation.lagrangian_velocity_smul F q v r)
    (fun _z hz => lagrangian_contDiffAt_one F hz)

theorem exists_local_jet_bounds (F : ReversibleMetric n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : SphereLoop n) (v : LocalSpace u), ∀ᵐ t ∂intervalMeasure,
      ‖lagrangian F (ambientJet (v : Space n) t)‖ ≤ C * ‖velocity (v : Space n) t‖ ^ 2 ∧
      ‖positionDifferential F (ambientJet (v : Space n) t)‖ ≤ C * ‖velocity (v : Space n) t‖ ^ 2 ∧
      ‖velocityDifferential F (ambientJet (v : Space n) t)‖ ≤ C * ‖velocity (v : Space n) t‖ := by
  obtain ⟨C, hC, hb⟩ := exists_annulus_bounds F
  refine ⟨C, hC, fun u v => ?_⟩
  filter_upwards [localJet_position_mem_annulus_ae v] with t ht
  exact hb _ ht _

theorem density_aestronglyMeasurable (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) :
    AEStronglyMeasurable (fun t => lagrangian F (ambientJet (v : Space n) t)) intervalMeasure := by
  have h := ((densityExtension_measurable F).comp_aemeasurable
    (ambientJet_aestronglyMeasurable (v : Space n)).aemeasurable).aestronglyMeasurable
  exact h.congr ((localJet_position_ne_zero_ae v).mono fun _ ht => densityExtension_eq F ht)

theorem differential_aestronglyMeasurable (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) : AEStronglyMeasurable
      (fun t => fderiv ℝ (lagrangian F) (ambientJet (v : Space n) t)) intervalMeasure := by
  have h := ((differentialExtension_measurable F).comp_aemeasurable
    (ambientJet_aestronglyMeasurable (v : Space n)).aemeasurable).aestronglyMeasurable
  exact h.congr ((localJet_position_ne_zero_ae v).mono fun _ ht => differentialExtension_eq F ht)

theorem position_aestronglyMeasurable (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) : AEStronglyMeasurable
      (fun t => positionDifferential F (ambientJet (v : Space n) t)) intervalMeasure :=
  (continuous_id.clm_comp continuous_const).comp_aestronglyMeasurable
    (differential_aestronglyMeasurable F v)

theorem velocity_aestronglyMeasurable (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) : AEStronglyMeasurable
      (fun t => velocityDifferential F (ambientJet (v : Space n) t)) intervalMeasure :=
  (continuous_id.clm_comp continuous_const).comp_aestronglyMeasurable
    (differential_aestronglyMeasurable F v)

theorem density_integrable (F : ReversibleMetric n) {u : SphereLoop n} (v : LocalSpace u) :
    Integrable (fun t => lagrangian F (ambientJet (v : Space n) t)) intervalMeasure := by
  obtain ⟨C, _hC, hb⟩ := exists_local_jet_bounds F
  exact ((integrable_velocity_sq (v : Space n)).const_mul C).mono'
    (density_aestronglyMeasurable F v) ((hb u v).mono fun _ ht => ht.1)

theorem position_integrable (F : ReversibleMetric n) {u : SphereLoop n} (v : LocalSpace u) :
    Integrable (fun t => positionDifferential F (ambientJet (v : Space n) t)) intervalMeasure := by
  obtain ⟨C, _hC, hb⟩ := exists_local_jet_bounds F
  exact ((integrable_velocity_sq (v : Space n)).const_mul C).mono'
    (position_aestronglyMeasurable F v) ((hb u v).mono fun _ ht => ht.2.1)

theorem velocity_memLp_two (F : ReversibleMetric n) {u : SphereLoop n} (v : LocalSpace u) :
    MemLp (fun t => velocityDifferential F (ambientJet (v : Space n) t)) 2 intervalMeasure := by
  obtain ⟨C, _hC, hb⟩ := exists_local_jet_bounds F
  exact ((Lp.memLp (velocity (v : Space n))).norm.const_mul C).mono'
    (velocity_aestronglyMeasurable F v) ((hb u v).mono fun _ ht => ht.2.2)

def ambientEnergy (F : ReversibleMetric n) (v : Space n) : ℝ :=
  ∫ t, lagrangian F (ambientJet v t) ∂intervalMeasure

theorem ambientEnergy_sphereLoop (F : ReversibleMetric n) (u : SphereLoop n) :
    ambientEnergy F (u.data : Space n) = Finsler.SobolevEnergy.energy F u := rfl

theorem ambientEnergy_nonneg (F : ReversibleMetric n) (v : Space n) : 0 ≤ ambientEnergy F v :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem exists_local_energy_bound (F : ReversibleMetric n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : SphereLoop n) (v : LocalSpace u),
      ‖ambientEnergy F (v : Space n)‖ ≤ C * ‖velocity (v : Space n)‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_local_jet_bounds F
  refine ⟨C, hC, fun u v => ?_⟩
  have h := norm_integral_le_of_norm_le ((integrable_velocity_sq (v : Space n)).const_mul C)
    ((hb u v).mono fun _ ht => ht.1)
  simpa only [ambientEnergy, integral_const_mul, velocity_sq_integral_eq_norm_sq] using h

def positionCoefficient (F : ReversibleMetric n) {u : SphereLoop n} (v : LocalSpace u) :
    Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure :=
  (memLp_one_iff_integrable.mpr (position_integrable F v)).toLp
    (fun t => positionDifferential F (ambientJet (v : Space n) t))

def velocityCoefficient (F : ReversibleMetric n) {u : SphereLoop n} (v : LocalSpace u) :
    Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure :=
  (velocity_memLp_two F v).toLp (fun t => velocityDifferential F (ambientJet (v : Space n) t))

theorem positionCoefficient_apply_ae (F : ReversibleMetric n) {u : SphereLoop n} (v : LocalSpace u) :
    positionCoefficient F v =ᵐ[intervalMeasure] fun t =>
      positionDifferential F (ambientJet (v : Space n) t) := MemLp.coeFn_toLp _

theorem velocityCoefficient_apply_ae (F : ReversibleMetric n) {u : SphereLoop n} (v : LocalSpace u) :
    velocityCoefficient F v =ᵐ[intervalMeasure] fun t =>
      velocityDifferential F (ambientJet (v : Space n) t) := MemLp.coeFn_toLp _

def variationL (F : ReversibleMetric n) {u : SphereLoop n} (v : LocalSpace u) : Space n →L[ℝ] ℝ :=
  coefficientPairingL (positionCoefficient F v) (velocityCoefficient F v)

theorem variationL_apply_eq_full_differential (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) (h : Space n) : variationL F v h =
      ∫ t, fderiv ℝ (lagrangian F) (ambientJet (v : Space n) t)
        (continuousRepresentative h t, velocity h t) ∂intervalMeasure := by
  apply integral_congr_ae
  filter_upwards [positionCoefficient_apply_ae F v, velocityCoefficient_apply_ae F v] with t hA hB
  change (positionCoefficient F v) t (continuousRepresentative h t) +
      (velocityCoefficient F v) t (velocity h t) = _
  rw [hA, hB]
  exact (differential_split F _ _ _).symm

theorem variationL_centre (F : ReversibleMetric n) (u : SphereLoop n) :
    variationL F (centre u) = Finsler.SobolevEnergyDifferential.variationL F u := by
  apply ContinuousLinearMap.ext
  intro h
  rw [variationL_apply_eq_full_differential,
    Finsler.SobolevEnergyDifferential.variationL_apply_eq_full_differential]
  rfl

end

end Finsler.AmbientSobolevEnergy
