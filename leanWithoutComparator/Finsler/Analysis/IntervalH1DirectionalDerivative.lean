module

public import Finsler.Analysis.IntervalH1NeighbourhoodContinuity
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Actual directional differentiation of ambient energy on the original H1
open neighbourhood. Fixed velocity representatives are used in the affine
jet; agreement with the actual weak jet is proved separately for each scalar.
No uncountable intersection of a.e. equalities or point evaluation on L2 is
used. Frechet differentiation and intrinsic sphere charts remain separate. -/

@[expose] public section

namespace Finsler.AmbientSobolevEnergy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.AmbientLagrangian Finsler.AmbientEnergyRegularity
open Finsler.SobolevEnergyDifferential MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

noncomputable section
variable {n : ℕ}
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

def affineJet (v h : Space n) (s t : ℝ) : Ambient n × Ambient n :=
  ambientJet v t + s • ambientJet h t

theorem affineJet_zero (v h : Space n) (t : ℝ) :
    affineJet v h 0 t = ambientJet v t := by simp [affineJet]

theorem affineJet_position_eq_representative (v h : Space n) (s : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    (affineJet v h s t).1 = continuousRepresentative (v + s • h) t := by
  rw [continuousRepresentative_add v (s • h) ht, continuousRepresentative_smul s h ht]
  rfl

theorem affineJet_eq_actual_ae (v h : Space n) (s : ℝ) :
    affineJet v h s =ᵐ[intervalMeasure] ambientJet (v + s • h) := by
  filter_upwards [velocity_add_ae v (s • h), velocity_smul_ae s h,
    ae_restrict_mem measurableSet_Ioo] with t ha hs ht
  apply Prod.ext
  · exact affineJet_position_eq_representative v h s (Ioo_subset_Icc_self ht)
  · change velocity v t + s • velocity h t = velocity (v + s • h) t
    rw [ha, hs]

theorem affineJet_hasDerivAt (v h : Space n) (s t : ℝ) :
    HasDerivAt (fun r : ℝ => affineJet v h r t) (ambientJet h t) s := by
  simpa only [affineJet, id_eq, one_smul] using
    ((hasDerivAt_id s).smul_const (ambientJet h t)).const_add (ambientJet v t)

theorem affine_line_continuous (v h : Space n) :
    Continuous (fun s : ℝ => v + s • h) :=
  continuous_const.add (continuous_id.smul continuous_const)

def lineParameters {u : SphereLoop n} (v : LocalSpace u) (h : Space n) : Set ℝ :=
  (fun s : ℝ => (v : Space n) + s • h) ⁻¹' neighbourhood u ∩ Ioo (-1) 1

theorem lineParameters_open {u : SphereLoop n} (v : LocalSpace u) (h : Space n) :
    IsOpen (lineParameters v h) :=
  ((neighbourhood_open u).preimage (affine_line_continuous (v : Space n) h)).inter isOpen_Ioo

theorem zero_mem_lineParameters {u : SphereLoop n} (v : LocalSpace u) (h : Space n) :
    (0 : ℝ) ∈ lineParameters v h := by
  constructor
  · simpa only [mem_preimage, zero_smul, add_zero] using v.property
  · constructor <;> norm_num

theorem lineParameters_mem_nhds {u : SphereLoop n} (v : LocalSpace u) (h : Space n) :
    lineParameters v h ∈ 𝓝 (0 : ℝ) :=
  (lineParameters_open v h).mem_nhds (zero_mem_lineParameters v h)

theorem abs_lt_one_of_mem_lineParameters {u : SphereLoop n} (v : LocalSpace u)
    (h : Space n) {s : ℝ} (hs : s ∈ lineParameters v h) : |s| < 1 :=
  abs_lt.mpr hs.2

theorem affineJet_position_mem_annulus {u : SphereLoop n} (v : LocalSpace u)
    (h : Space n) {s t : ℝ} (hs : s ∈ lineParameters v h) (ht : t ∈ Icc 0 1) :
    (affineJet (v : Space n) h s t).1 ∈ compactAnnulus n := by
  rw [affineJet_position_eq_representative _ _ _ ht]
  have hb := representative_norm_bounds_of_mem_neighbourhood u hs.1 ht
  exact ⟨hb.1.le, hb.2.le⟩

def lineDensity (F : ReversibleMetric n) (v h : Space n) (s t : ℝ) : ℝ :=
  lagrangian F (affineJet v h s t)

def lineDifferential (F : ReversibleMetric n) (v h : Space n) (s t : ℝ) : ℝ :=
  fderiv ℝ (lagrangian F) (affineJet v h s t) (ambientJet h t)

theorem lineDensity_hasDerivAt (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) (h : Space n) {s t : ℝ}
    (hs : s ∈ lineParameters v h) (ht : t ∈ Icc 0 1) :
    HasDerivAt (fun r => lineDensity F (v : Space n) h r t)
      (lineDifferential F (v : Space n) h s t) s := by
  have hz := compactAnnulus_nonzero n (affineJet_position_mem_annulus v h hs ht)
  exact ((lagrangian_contDiffAt_one F hz).differentiableAt (by norm_num)).hasFDerivAt
    |>.comp_hasDerivAt s (affineJet_hasDerivAt (v : Space n) h s t)

theorem lineDensity_aestronglyMeasurable (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) (h : Space n) {s : ℝ} (hs : s ∈ lineParameters v h) :
    AEStronglyMeasurable (lineDensity F (v : Space n) h s) intervalMeasure := by
  have hm := density_aestronglyMeasurable F
    (⟨(v : Space n) + s • h, hs.1⟩ : LocalSpace u)
  exact hm.congr ((affineJet_eq_actual_ae (v : Space n) h s).symm.mono
    fun _ ht => congrArg (lagrangian F) ht)

theorem lineDensity_zero_integrable (F : ReversibleMetric n) {u : SphereLoop n}
    (v : LocalSpace u) (h : Space n) :
    Integrable (lineDensity F (v : Space n) h 0) intervalMeasure := by
  have he : lineDensity F (v : Space n) h 0 =
      fun t => lagrangian F (ambientJet (v : Space n) t) := by
    funext t
    exact congrArg (lagrangian F) (affineJet_zero (v : Space n) h t)
  rw [he]
  exact density_integrable F v

theorem lineDifferential_zero_aestronglyMeasurable (F : ReversibleMetric n)
    {u : SphereLoop n} (v : LocalSpace u) (h : Space n) :
    AEStronglyMeasurable (lineDifferential F (v : Space n) h 0) intervalMeasure := by
  have hc : Continuous (fun p : (Ambient n × Ambient n →L[ℝ] ℝ) ×
      (Ambient n × Ambient n) => p.1 p.2) := continuous_fst.clm_apply continuous_snd
  have hm := hc.comp_aestronglyMeasurable
    ((differential_aestronglyMeasurable F v).prodMk (ambientJet_aestronglyMeasurable h))
  have he : lineDifferential F (v : Space n) h 0 =
      fun t => fderiv ℝ (lagrangian F) (ambientJet (v : Space n) t) (ambientJet h t) := by
    funext t
    exact congrArg (fun z => fderiv ℝ (lagrangian F) z (ambientJet h t))
      (affineJet_zero (v : Space n) h t)
  rw [he]
  exact hm

def directionalBound (C : ℝ) (v h : Space n) (t : ℝ) : ℝ :=
  C * (2 * ‖h‖ + 1) * (2 * ‖velocity v t‖ ^ 2 + 2 * ‖velocity h t‖ ^ 2)

theorem directionalBound_integrable (C : ℝ) (v h : Space n) :
    Integrable (directionalBound C v h) intervalMeasure :=
  (((integrable_velocity_sq v).const_mul 2).add
    ((integrable_velocity_sq h).const_mul 2)).const_mul (C * (2 * ‖h‖ + 1))

theorem lineDifferential_norm_le (F : ReversibleMetric n) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ q ∈ compactAnnulus n, ∀ w : Ambient n,
      ‖lagrangian F (q, w)‖ ≤ C * ‖w‖ ^ 2 ∧
      ‖positionDifferential F (q, w)‖ ≤ C * ‖w‖ ^ 2 ∧
      ‖velocityDifferential F (q, w)‖ ≤ C * ‖w‖)
    {u : SphereLoop n} (v : LocalSpace u) (h : Space n) {s t : ℝ}
    (hs : s ∈ lineParameters v h) (ht : t ∈ Icc 0 1) :
    ‖lineDifferential F (v : Space n) h s t‖ ≤ directionalBound C (v : Space n) h t := by
  let a := ‖velocity (v : Space n) t‖
  let b := ‖velocity h t‖
  let R := ‖(affineJet (v : Space n) h s t).2‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hR0 : 0 ≤ R := norm_nonneg _
  have hR : R ≤ a + b := by
    change ‖velocity (v : Space n) t + s • velocity h t‖ ≤ a + b
    calc
      _ ≤ ‖velocity (v : Space n) t‖ + ‖s • velocity h t‖ := norm_add_le _ _
      _ = a + |s| * b := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ a + b := by nlinarith [abs_lt_one_of_mem_lineParameters v h hs]
  have hbds := hb _ (affineJet_position_mem_annulus v h hs ht)
    ((affineJet (v : Space n) h s t).2)
  have hp := continuousRepresentative_norm_le_two h ht
  have hn : 0 ≤ 2 * ‖h‖ := by positivity
  have hsq : R ^ 2 ≤ (a + b) ^ 2 := by nlinarith
  have hmix : R * b ≤ (a + b) ^ 2 := by nlinarith
  have hsum : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  rw [lineDifferential, differential_split]
  calc
    _ ≤ ‖positionDifferential F (affineJet (v : Space n) h s t)
        (continuousRepresentative h t)‖ +
        ‖velocityDifferential F (affineJet (v : Space n) h s t) (velocity h t)‖ :=
      norm_add_le _ _
    _ ≤ ‖positionDifferential F (affineJet (v : Space n) h s t)‖ *
        ‖continuousRepresentative h t‖ +
        ‖velocityDifferential F (affineJet (v : Space n) h s t)‖ * b :=
      add_le_add ((positionDifferential F _).le_opNorm _) ((velocityDifferential F _).le_opNorm _)
    _ ≤ (C * R ^ 2) * (2 * ‖h‖) + (C * R) * b := by
      exact add_le_add
        (mul_le_mul hbds.2.1 hp (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right hbds.2.2 hb0)
    _ = C * (R ^ 2 * (2 * ‖h‖) + R * b) := by ring
    _ ≤ C * ((a + b) ^ 2 * (2 * ‖h‖) + (a + b) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hsq hn) hmix) hC
    _ = C * (2 * ‖h‖ + 1) * (a + b) ^ 2 := by ring
    _ ≤ C * (2 * ‖h‖ + 1) * (2 * a ^ 2 + 2 * b ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = directionalBound C (v : Space n) h t := rfl

theorem exists_lineDifferential_integrable_bound (F : ReversibleMetric n)
    {u : SphereLoop n} (v : LocalSpace u) (h : Space n) :
    ∃ B : ℝ → ℝ, Integrable B intervalMeasure ∧
      ∀ᵐ t ∂intervalMeasure, ∀ s ∈ lineParameters v h,
        ‖lineDifferential F (v : Space n) h s t‖ ≤ B t := by
  obtain ⟨C, hC, hb⟩ := exists_annulus_bounds F
  refine ⟨directionalBound C (v : Space n) h, directionalBound_integrable C _ _, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact fun s hs => lineDifferential_norm_le F hC.le hb v h hs (Ioo_subset_Icc_self ht)

theorem lineDensity_integral_eq_ambientEnergy (F : ReversibleMetric n)
    (v h : Space n) (s : ℝ) :
    (∫ t, lineDensity F v h s t ∂intervalMeasure) = ambientEnergy F (v + s • h) := by
  apply integral_congr_ae
  exact (affineJet_eq_actual_ae v h s).mono fun _ ht => congrArg (lagrangian F) ht

theorem ambientEnergy_hasDerivAt_zero (F : ReversibleMetric n)
    {u : SphereLoop n} (v : LocalSpace u) (h : Space n) :
    HasDerivAt (fun s : ℝ => ambientEnergy F ((v : Space n) + s • h))
      (variationL F v h) 0 := by
  obtain ⟨B, hBi, hBb⟩ := exists_lineDifferential_integrable_bound F v h
  have hm : ∀ᶠ s in 𝓝 (0 : ℝ),
      AEStronglyMeasurable (lineDensity F (v : Space n) h s) intervalMeasure :=
    Filter.Eventually.mono (lineParameters_mem_nhds v h)
      fun s hs => lineDensity_aestronglyMeasurable F v h hs
  have hd : ∀ᵐ t ∂intervalMeasure, ∀ s ∈ lineParameters v h,
      HasDerivAt (fun r => lineDensity F (v : Space n) h r t)
        (lineDifferential F (v : Space n) h s t) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact fun s hs => lineDensity_hasDerivAt F v h hs (Ioo_subset_Icc_self ht)
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (lineParameters_mem_nhds v h) hm (lineDensity_zero_integrable F v h)
    (lineDifferential_zero_aestronglyMeasurable F v h) hBb hBi hd
  have he : (∫ t, lineDifferential F (v : Space n) h 0 t ∂intervalMeasure) =
      variationL F v h := by
    rw [variationL_apply_eq_full_differential]
    simp only [lineDifferential, affineJet_zero, ambientJet]
  rw [he] at hi
  exact hi.2.congr_of_eventuallyEq (Eventually.of_forall fun s =>
    (lineDensity_integral_eq_ambientEnergy F (v : Space n) h s).symm)

theorem ambientEnergy_hasLineDerivAt (F : ReversibleMetric n)
    {u : SphereLoop n} (v : LocalSpace u) (h : Space n) :
    HasLineDerivAt ℝ (ambientEnergy F) (variationL F v h) (v : Space n) h :=
  ambientEnergy_hasDerivAt_zero F v h

theorem ambientEnergy_lineDeriv (F : ReversibleMetric n)
    {u : SphereLoop n} (v : LocalSpace u) (h : Space n) :
    lineDeriv ℝ (ambientEnergy F) (v : Space n) h = variationL F v h :=
  (ambientEnergy_hasLineDerivAt F v h).lineDeriv

theorem ambientEnergy_hasDerivAt_sphere_centre (F : ReversibleMetric n)
    (u : SphereLoop n) (h : Space n) :
    HasDerivAt (fun s : ℝ => ambientEnergy F ((u.data : Space n) + s • h))
      (Finsler.SobolevEnergyDifferential.variationL F u h) 0 := by
  have hh := ambientEnergy_hasDerivAt_zero F (centre u) h
  rw [variationL_centre] at hh
  simpa only [centre] using hh

end

end Finsler.AmbientSobolevEnergy
