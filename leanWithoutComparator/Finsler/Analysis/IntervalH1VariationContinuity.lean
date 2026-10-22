module

public import Finsler.Analysis.IntervalH1CoefficientContinuity

/-! Bounded L¹/L² coefficient pairing on the original weak H¹ space.
The genuine first-variation candidate is continuous in operator norm in the
base sphere loop. This does not identify it as the derivative of the energy. -/

@[expose] public section

namespace Finsler.SobolevEnergyDifferential

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.AmbientLagrangian Finsler.SobolevEnergy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem lp_two_norm_eq_sqrt_integral_norm_sq {E : Type*} [NormedAddCommGroup E]
    (f : Lp E 2 intervalMeasure) :
    ‖f‖ = Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂intervalMeasure) := by
  rw [Lp.norm_def, (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
  norm_num

theorem lp_two_norm_product_integral_le {E G : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup G]
    (f : Lp E 2 intervalMeasure) (g : Lp G 2 intervalMeasure) :
    (∫ t, ‖f t‖ * ‖g t‖ ∂intervalMeasure) ≤ ‖f‖ * ‖g‖ := by
  have hf : MemLp (fun t => ‖f t‖) (ENNReal.ofReal (2 : ℝ)) intervalMeasure := by
    simpa using (Lp.memLp f).norm
  have hg : MemLp (fun t => ‖g t‖) (ENNReal.ofReal (2 : ℝ)) intervalMeasure := by
    simpa using (Lp.memLp g).norm
  have hb := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hf hg
  rw [lp_two_norm_eq_sqrt_integral_norm_sq f, lp_two_norm_eq_sqrt_integral_norm_sq g]
  simpa only [norm_norm, Real.rpow_two, Real.sqrt_eq_rpow, one_div] using hb

theorem coefficient_position_pair_integrable
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure) (h : Space n) :
    Integrable (fun t => A t (continuousRepresentative h t)) intervalMeasure := by
  have hr := (Lp.aestronglyMeasurable (value h)).congr (value_ae_continuousRepresentative h)
  have hc : Continuous (fun p : (Ambient n →L[ℝ] ℝ) × Ambient n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  apply ((memLp_one_iff_integrable.mp (Lp.memLp A)).norm.const_mul (2 * ‖h‖)).mono'
    (hc.comp_aestronglyMeasurable ((Lp.aestronglyMeasurable A).prodMk hr))
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  calc
    ‖A t (continuousRepresentative h t)‖ ≤ ‖A t‖ * ‖continuousRepresentative h t‖ :=
      (A t).le_opNorm _
    _ ≤ ‖A t‖ * (2 * ‖h‖) := mul_le_mul_of_nonneg_left
      (continuousRepresentative_norm_le_two h (Ioo_subset_Icc_self ht)) (norm_nonneg _)
    _ = (2 * ‖h‖) * ‖A t‖ := mul_comm _ _

theorem coefficient_velocity_pair_integrable
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) (h : Space n) :
    Integrable (fun t => B t (velocity h t)) intervalMeasure := by
  have hc : Continuous (fun p : (Ambient n →L[ℝ] ℝ) × Ambient n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact ((Lp.memLp B).norm.integrable_mul (Lp.memLp (velocity h)).norm).mono'
    (hc.comp_aestronglyMeasurable ((Lp.aestronglyMeasurable B).prodMk
      (Lp.aestronglyMeasurable (velocity h)))) (ae_of_all _ fun t => (B t).le_opNorm _)

def coefficientPairing
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) (h : Space n) : ℝ :=
  ∫ t, A t (continuousRepresentative h t) + B t (velocity h t) ∂intervalMeasure

theorem coefficientPairing_integrable
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) (h : Space n) :
    Integrable (fun t => A t (continuousRepresentative h t) + B t (velocity h t))
      intervalMeasure :=
  (coefficient_position_pair_integrable A h).add (coefficient_velocity_pair_integrable B h)

theorem coefficientPairing_norm_le
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) (h : Space n) :
    ‖coefficientPairing A B h‖ ≤ (2 * ‖A‖ + ‖B‖) * ‖h‖ := by
  have hA := norm_integral_le_of_norm_le
    ((memLp_one_iff_integrable.mp (Lp.memLp A)).norm.const_mul (2 * ‖h‖)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact ((A t).le_opNorm _).trans (by
        have hb := mul_le_mul_of_nonneg_left
          (continuousRepresentative_norm_le_two h (Ioo_subset_Icc_self ht)) (norm_nonneg (A t))
        simpa [mul_comm] using hb))
  have hB := norm_integral_le_of_norm_le
    ((Lp.memLp B).norm.integrable_mul (Lp.memLp (velocity h)).norm)
    (ae_of_all _ fun t => (B t).le_opNorm (velocity h t))
  rw [integral_const_mul, ← L1.norm_eq_integral_norm] at hA
  have hB' : ‖∫ t, B t (velocity h t) ∂intervalMeasure‖ ≤ ‖B‖ * ‖h‖ :=
    hB.trans ((lp_two_norm_product_integral_le B (velocity h)).trans
      (mul_le_mul_of_nonneg_left (velocity_norm_le h) (norm_nonneg B)))
  rw [coefficientPairing, integral_add (coefficient_position_pair_integrable A h)
    (coefficient_velocity_pair_integrable B h)]
  exact (norm_add_le _ _).trans ((add_le_add hA hB').trans_eq (by ring))

theorem coefficientPairing_add_direction
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) (h k : Space n) :
    coefficientPairing A B (h + k) = coefficientPairing A B h + coefficientPairing A B k := by
  unfold coefficientPairing
  calc
    _ = ∫ t, (A t (continuousRepresentative h t) + B t (velocity h t)) +
        (A t (continuousRepresentative k t) + B t (velocity k t)) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [velocity_add_ae h k, ae_restrict_mem measurableSet_Ioo] with t ht hmem
      rw [continuousRepresentative_add h k (Ioo_subset_Icc_self hmem), ht, map_add, map_add]
      ring
    _ = _ := integral_add (coefficientPairing_integrable A B h) (coefficientPairing_integrable A B k)

theorem coefficientPairing_smul_direction
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) (a : ℝ) (h : Space n) :
    coefficientPairing A B (a • h) = a • coefficientPairing A B h := by
  unfold coefficientPairing
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [velocity_smul_ae a h, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  rw [continuousRepresentative_smul a h (Ioo_subset_Icc_self hmem), ht, map_smul, map_smul,
    smul_add]

def coefficientPairingLinear
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) : Space n →ₗ[ℝ] ℝ where
  toFun := coefficientPairing A B
  map_add' := coefficientPairing_add_direction A B
  map_smul' := coefficientPairing_smul_direction A B

def coefficientPairingL
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) : Space n →L[ℝ] ℝ :=
  (coefficientPairingLinear A B).mkContinuous (2 * ‖A‖ + ‖B‖) (coefficientPairing_norm_le A B)

theorem coefficientPairingL_apply
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) (h : Space n) :
    coefficientPairingL A B h = coefficientPairing A B h := rfl

theorem coefficientPairingL_opNorm_le
    (A : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) :
    ‖coefficientPairingL A B‖ ≤ 2 * ‖A‖ + ‖B‖ :=
  (coefficientPairingLinear A B).mkContinuous_norm_le (by positivity) (coefficientPairing_norm_le A B)

theorem coefficientPairingL_sub
    (A C : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B D : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) :
    coefficientPairingL (A - C) (B - D) = coefficientPairingL A B - coefficientPairingL C D := by
  ext h
  change coefficientPairing (A - C) (B - D) h = coefficientPairing A B h - coefficientPairing C D h
  unfold coefficientPairing
  calc
    _ = ∫ t, (A t (continuousRepresentative h t) + B t (velocity h t)) -
        (C t (continuousRepresentative h t) + D t (velocity h t)) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub A C, Lp.coeFn_sub B D] with t hA hB
      rw [hA, hB, Pi.sub_apply, Pi.sub_apply, sub_apply, sub_apply]
      ring
    _ = _ := integral_sub (coefficientPairing_integrable A B h) (coefficientPairing_integrable C D h)

theorem coefficientPairingL_norm_sub_le
    (A C : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure)
    (B D : Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure) :
    ‖coefficientPairingL A B - coefficientPairingL C D‖ ≤ 2 * ‖A - C‖ + ‖B - D‖ := by
  rw [← coefficientPairingL_sub]
  exact coefficientPairingL_opNorm_le _ _

theorem coefficientPairingL_lipschitz :
    LipschitzWith 3 (fun p : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure ×
      Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure => coefficientPairingL p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change dist (coefficientPairingL p.1 p.2) (coefficientPairingL q.1 q.2) ≤
    (3 : ℝ) * dist p q
  calc
    _ = ‖coefficientPairingL p.1 p.2 - coefficientPairingL q.1 q.2‖ :=
      dist_eq_norm (coefficientPairingL p.1 p.2) (coefficientPairingL q.1 q.2)
    _ ≤ 2 * ‖p.1 - q.1‖ + ‖p.2 - q.2‖ := coefficientPairingL_norm_sub_le _ _ _ _
    _ ≤ 3 * dist p q := by
      rw [dist_eq_norm]
      have hp : ‖p.1 - q.1‖ ≤ ‖p - q‖ := norm_fst_le (p - q)
      have hq : ‖p.2 - q.2‖ ≤ ‖p - q‖ := norm_snd_le (p - q)
      nlinarith

theorem coefficientPairingL_continuous :
    Continuous (fun p : Lp (Ambient n →L[ℝ] ℝ) 1 intervalMeasure ×
      Lp (Ambient n →L[ℝ] ℝ) 2 intervalMeasure => coefficientPairingL p.1 p.2) :=
  coefficientPairingL_lipschitz.continuous

theorem variationL_eq_coefficientPairingL (F : ReversibleMetric n) (u : SphereLoop n) :
    variationL F u = coefficientPairingL (positionCoefficient F u) (velocityCoefficient F u) := by
  ext h
  change variationCandidate F u h = coefficientPairing (positionCoefficient F u) (velocityCoefficient F u) h
  apply integral_congr_ae
  filter_upwards [positionCoefficient_apply_ae F u, velocityCoefficient_apply_ae F u] with t hA hB
  rw [hA, hB]

theorem variationL_norm_sub_le (F : ReversibleMetric n) (u v : SphereLoop n) :
    ‖variationL F u - variationL F v‖ ≤
      2 * ‖positionCoefficient F u - positionCoefficient F v‖ +
        ‖velocityCoefficient F u - velocityCoefficient F v‖ := by
  rw [variationL_eq_coefficientPairingL, variationL_eq_coefficientPairingL]
  exact coefficientPairingL_norm_sub_le _ _ _ _

theorem variationL_continuous (F : ReversibleMetric n) : Continuous (variationL F) := by
  have hc := coefficientPairingL_continuous.comp
    ((positionCoefficient_continuous F).prodMk (velocityCoefficient_continuous F))
  exact hc.congr (fun u => (variationL_eq_coefficientPairingL F u).symm)

theorem variationCandidate_continuous (F : ReversibleMetric n) :
    Continuous (fun p : SphereLoop n × Space n => variationCandidate F p.1 p.2) :=
  ((variationL_continuous F).comp continuous_fst).clm_apply continuous_snd

end

end Finsler.SobolevEnergyDifferential
