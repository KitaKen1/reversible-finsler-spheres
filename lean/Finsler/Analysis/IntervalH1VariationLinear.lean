module

public import Finsler.Analysis.IntervalH1EnergyDifferential

/-! The genuine integral first-variation candidate is a bounded linear
functional on the original ambient weak H¹ graph. This constructs the
candidate functional and its quantitative bound; it does not differentiate
the energy integral or change the topology of the loop space. -/

@[expose] public section

namespace Finsler.SobolevEnergyDifferential

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.AmbientLagrangian Finsler.SobolevEnergy
open MeasureTheory Set Filter
open scoped Topology ENNReal

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem velocity_add_ae (h k : Space n) :
    velocity (h + k) =ᵐ[intervalMeasure] fun t => velocity h t + velocity k t := by
  have hv : velocity (h + k) = velocity h + velocity k := (velocityL n).map_add h k
  rw [hv]
  exact Lp.coeFn_add (velocity h) (velocity k)

theorem velocity_smul_ae (a : ℝ) (h : Space n) :
    velocity (a • h) =ᵐ[intervalMeasure] fun t => a • velocity h t := by
  have hv : velocity (a • h) = a • velocity h := (velocityL n).map_smul a h
  rw [hv]
  exact Lp.coeFn_smul a (velocity h)

theorem variationCandidate_add (F : ReversibleMetric n) (u : SphereLoop n)
    (h k : Space n) :
    variationCandidate F u (h + k) = variationCandidate F u h + variationCandidate F u k := by
  unfold variationCandidate
  calc
    _ = ∫ t, (positionDifferential F (weakJet u t) (continuousRepresentative h t) +
        velocityDifferential F (weakJet u t) (velocity h t)) +
        (positionDifferential F (weakJet u t) (continuousRepresentative k t) +
        velocityDifferential F (weakJet u t) (velocity k t)) ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [velocity_add_ae h k, ae_restrict_mem measurableSet_Ioo] with t hv ht
      rw [continuousRepresentative_add h k (Ioo_subset_Icc_self ht), hv, map_add, map_add]
      ring
    _ = _ := integral_add (variationCandidate_integrable F u h)
      (variationCandidate_integrable F u k)

theorem variationCandidate_smul (F : ReversibleMetric n) (u : SphereLoop n)
    (a : ℝ) (h : Space n) :
    variationCandidate F u (a • h) = a • variationCandidate F u h := by
  rw [variationCandidate, variationCandidate, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [velocity_smul_ae a h, ae_restrict_mem measurableSet_Ioo] with t hv ht
  rw [continuousRepresentative_smul a h (Ioo_subset_Icc_self ht), hv,
    map_smul, map_smul, smul_add]

def variationLinear (F : ReversibleMetric n) (u : SphereLoop n) : Space n →ₗ[ℝ] ℝ where
  toFun := variationCandidate F u
  map_add' := variationCandidate_add F u
  map_smul' := variationCandidate_smul F u

theorem variationLinear_apply (F : ReversibleMetric n) (u : SphereLoop n)
    (h : Space n) : variationLinear F u h = variationCandidate F u h := rfl

theorem variationCandidate_zero (F : ReversibleMetric n) (u : SphereLoop n) :
    variationCandidate F u (0 : Space n) = 0 :=
  (variationLinear F u).map_zero

theorem velocity_norm_product_integral_le (h k : Space n) :
    (∫ t, ‖velocity h t‖ * ‖velocity k t‖ ∂intervalMeasure) ≤
      ‖velocity h‖ * ‖velocity k‖ := by
  have hh : MemLp (velocity h) (ENNReal.ofReal (2 : ℝ)) intervalMeasure := by
    simpa using Lp.memLp (velocity h)
  have hk : MemLp (velocity k) (ENNReal.ofReal (2 : ℝ)) intervalMeasure := by
    simpa using Lp.memLp (velocity k)
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hh hk
  simpa only [Real.rpow_two, velocity_sq_integral_eq_norm_sq,
    ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)] using h

theorem position_variation_integral_norm_le (F : ReversibleMetric n) (u : SphereLoop n)
    (h : Space n) {C : ℝ} (hb : ∀ᵐ t ∂intervalMeasure,
      ‖positionDifferential F (weakJet u t)‖ ≤ C * ‖velocity (u.data : Space n) t‖ ^ 2) :
    ‖∫ t, positionDifferential F (weakJet u t) (continuousRepresentative h t)
      ∂intervalMeasure‖ ≤ 2 * C * ‖velocity (u.data : Space n)‖ ^ 2 * ‖h‖ := by
  have hm := integral_mono_ae (position_variation_integrable F u h).norm
    ((integrable_velocity_sq (u.data : Space n)).const_mul (C * (2 * ‖h‖)))
    (by
      filter_upwards [hb, ae_restrict_mem measurableSet_Ioo] with t ht hi
      calc
        ‖positionDifferential F (weakJet u t) (continuousRepresentative h t)‖ ≤
            ‖positionDifferential F (weakJet u t)‖ * ‖continuousRepresentative h t‖ :=
          (positionDifferential F (weakJet u t)).le_opNorm _
        _ ≤ ‖positionDifferential F (weakJet u t)‖ * (2 * ‖h‖) :=
          mul_le_mul_of_nonneg_left (continuousRepresentative_norm_le_two h
            (Ioo_subset_Icc_self hi)) (norm_nonneg _)
        _ ≤ (C * ‖velocity (u.data : Space n) t‖ ^ 2) * (2 * ‖h‖) :=
          mul_le_mul_of_nonneg_right ht (by positivity)
        _ = (C * (2 * ‖h‖)) * ‖velocity (u.data : Space n) t‖ ^ 2 := by ring)
  rw [integral_const_mul, velocity_sq_integral_eq_norm_sq] at hm
  exact (norm_integral_le_integral_norm _).trans (hm.trans_eq (by ring))

theorem velocity_variation_integral_norm_le (F : ReversibleMetric n) (u : SphereLoop n)
    (h : Space n) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ t ∂intervalMeasure,
      ‖velocityDifferential F (weakJet u t)‖ ≤ C * ‖velocity (u.data : Space n) t‖) :
    ‖∫ t, velocityDifferential F (weakJet u t) (velocity h t) ∂intervalMeasure‖ ≤
      C * ‖velocity (u.data : Space n)‖ * ‖h‖ := by
  have hi := (Lp.memLp (velocity (u.data : Space n))).norm.integrable_mul
    (Lp.memLp (velocity h)).norm
  have hm := integral_mono_ae (velocity_variation_integrable F u h).norm (hi.const_mul C)
    (by
      filter_upwards [hb] with t ht
      calc
        ‖velocityDifferential F (weakJet u t) (velocity h t)‖ ≤
            ‖velocityDifferential F (weakJet u t)‖ * ‖velocity h t‖ :=
          (velocityDifferential F (weakJet u t)).le_opNorm _
        _ ≤ (C * ‖velocity (u.data : Space n) t‖) * ‖velocity h t‖ :=
          mul_le_mul_of_nonneg_right ht (norm_nonneg _)
        _ = C * (‖velocity (u.data : Space n) t‖ * ‖velocity h t‖) := by ring)
  rw [integral_const_mul] at hm
  calc
    ‖∫ t, velocityDifferential F (weakJet u t) (velocity h t) ∂intervalMeasure‖ ≤
        C * (∫ t, ‖velocity (u.data : Space n) t‖ * ‖velocity h t‖ ∂intervalMeasure) :=
      (norm_integral_le_integral_norm _).trans hm
    _ ≤ C * (‖velocity (u.data : Space n)‖ * ‖velocity h‖) :=
      mul_le_mul_of_nonneg_left (velocity_norm_product_integral_le _ h) hC
    _ ≤ C * (‖velocity (u.data : Space n)‖ * ‖h‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (velocity_norm_le h) (norm_nonneg _)) hC
    _ = C * ‖velocity (u.data : Space n)‖ * ‖h‖ := by ring

theorem exists_variationCandidate_bound (F : ReversibleMetric n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : SphereLoop n) (h : Space n),
      ‖variationCandidate F u h‖ ≤
        C * (2 * ‖velocity (u.data : Space n)‖ ^ 2 + ‖velocity (u.data : Space n)‖) * ‖h‖ := by
  obtain ⟨C, hC, hb⟩ := exists_weakJet_partial_bounds F
  refine ⟨C, hC, fun u h => ?_⟩
  rw [variationCandidate, integral_add (position_variation_integrable F u h)
    (velocity_variation_integrable F u h)]
  exact (norm_add_le _ _).trans ((add_le_add
    (position_variation_integral_norm_le F u h ((hb u).mono fun _ ht => ht.1))
    (velocity_variation_integral_norm_le F u h hC.le ((hb u).mono fun _ ht => ht.2)))
    |>.trans_eq (by ring))

def variationBound (F : ReversibleMetric n) : ℝ :=
  (exists_variationCandidate_bound F).choose

theorem variationBound_pos (F : ReversibleMetric n) : 0 < variationBound F :=
  (exists_variationCandidate_bound F).choose_spec.1

theorem variationCandidate_norm_le (F : ReversibleMetric n) (u : SphereLoop n)
    (h : Space n) : ‖variationCandidate F u h‖ ≤
      variationBound F *
        (2 * ‖velocity (u.data : Space n)‖ ^ 2 + ‖velocity (u.data : Space n)‖) * ‖h‖ :=
  (exists_variationCandidate_bound F).choose_spec.2 u h

def variationL (F : ReversibleMetric n) (u : SphereLoop n) : Space n →L[ℝ] ℝ :=
  (variationLinear F u).mkContinuous
    (variationBound F *
      (2 * ‖velocity (u.data : Space n)‖ ^ 2 + ‖velocity (u.data : Space n)‖))
    (variationCandidate_norm_le F u)

theorem variationL_apply (F : ReversibleMetric n) (u : SphereLoop n) (h : Space n) :
    variationL F u h = variationCandidate F u h := rfl

theorem variationL_opNorm_le (F : ReversibleMetric n) (u : SphereLoop n) :
    ‖variationL F u‖ ≤ variationBound F *
      (2 * ‖velocity (u.data : Space n)‖ ^ 2 + ‖velocity (u.data : Space n)‖) := by
  exact (variationLinear F u).mkContinuous_norm_le
    (by have h := variationBound_pos F; positivity) (variationCandidate_norm_le F u)

theorem variationCandidate_continuous_direction (F : ReversibleMetric n) (u : SphereLoop n) :
    Continuous (variationCandidate F u) := (variationL F u).continuous

theorem variationL_zero_of_velocity_zero (F : ReversibleMetric n) (u : SphereLoop n)
    (hv : velocity (u.data : Space n) = 0) : variationL F u = 0 := by
  apply (norm_eq_zero (a := variationL F u)).mp
  have he : ‖variationL F u‖ ≤ 0 := by simpa [hv] using variationL_opNorm_le F u
  exact le_antisymm he (norm_nonneg (variationL F u))

theorem variationL_constantSphereLoop (F : ReversibleMetric n) (x : Sphere n) :
    variationL F (constantSphereLoop x) = 0 :=
  variationL_zero_of_velocity_zero F _ (velocity_constantData (x : Ambient n))

theorem variationL_apply_eq_full_differential (F : ReversibleMetric n)
    (u : SphereLoop n) (h : Space n) : variationL F u h =
      ∫ t, fderiv ℝ (lagrangian F) (weakJet u t)
        (continuousRepresentative h t, velocity h t) ∂intervalMeasure :=
  variationCandidate_eq_full_differential F u h

end

end Finsler.SobolevEnergyDifferential
