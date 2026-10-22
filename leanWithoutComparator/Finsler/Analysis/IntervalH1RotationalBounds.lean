module

public import Finsler.Analysis.IntervalH1RotationalRecovery
public import Finsler.Analysis.IntervalH1EnergyZero

/-! Quantitative estimates from the actual recovered tangential covector.
The velocity Euler identity includes zero velocity. Finite continuous momenta
bound the actual weak velocity and its rotational force. Zero propagation,
Legendre inversion and smooth critical regularity are separate. -/

@[expose] public section

namespace Finsler.SobolevRotationalBounds

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevRotationalVariation Finsler.SobolevRotationalRecovery
open Finsler.SobolevCurveVariation Finsler.SobolevEnergyDifferential
open Finsler.SobolevEnergy Finsler.AmbientLagrangian
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- A continuous finite-component size, avoiding a norm on skew operators. -/
def momentumSize (b : OrthonormalBasis ι ℝ (Ambient n)) (F : ReversibleMetric n)
    (u : SphereLoop n) (hc : TangentCritical F u) (t : ℝ) : ℝ :=
  ∑ i, ∑ j, ‖momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t‖

theorem momentumSize_nonneg (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) (t : ℝ) :
    0 ≤ momentumSize b F u hc t := by
  apply Finset.sum_nonneg
  intro i _
  exact Finset.sum_nonneg fun j _ => norm_nonneg _

theorem momentumSize_continuousOn (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    ContinuousOn (momentumSize b F u hc) (Icc 0 1) := by
  apply continuousOn_finsetSum
  intro i _
  apply continuousOn_finsetSum
  intro j _
  exact (momentumRepresentative_continuousOn F u (planeRotation_isRotation (b i) (b j)) hc).norm

theorem momentumSize_periodic_trace (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    momentumSize b F u hc 1 = momentumSize b F u hc 0 := by
  unfold momentumSize
  simp_rw [momentumRepresentative_periodic_trace F u _ hc]

theorem norm_recoveredCovector_le_momentumSize (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (t : ClosedInterval) : ‖recoveredCovector b F u hc t‖ ≤ momentumSize b F u hc t := by
  classical
  have hq := u.sphere_constraint t
  have h := norm_sum_le Finset.univ (fun i =>
    (∑ j, ⟪b j, continuousRepresentative (u.data : Space n) t⟫ *
      momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc t) • innerSL ℝ (b i))
  simp only [norm_smul, innerSL_apply_norm, b.norm_eq_one, mul_one] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  have hj : ‖⟪b j, continuousRepresentative (u.data : Space n) t⟫‖ ≤ 1 :=
    (norm_inner_le_norm _ _).trans_eq (by rw [b.norm_eq_one, hq, one_mul])
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hj (norm_nonneg _)

theorem momentumSize_eq_zero_iff (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (t : ClosedInterval) : momentumSize b F u hc t = 0 ↔ recoveredCovector b F u hc t = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    exact le_antisymm ((norm_recoveredCovector_le_momentumSize b F u hc t).trans_eq h)
      (norm_nonneg _)
  · intro h
    unfold momentumSize
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [← recoveredCovector_rotation b F u hc (planeRotation_isRotation (b i) (b j)) t, h]
    simp

theorem planeRotation_opNorm_le_two (a b : Ambient n) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖planeRotation a b‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [planeRotation_apply]
  have h₁ : ‖(⟪b, x⟫ : ℝ)‖ ≤ ‖b‖ * ‖x‖ := norm_inner_le_norm b x
  have h₂ : ‖(⟪a, x⟫ : ℝ)‖ ≤ ‖a‖ * ‖x‖ := norm_inner_le_norm a x
  rw [hb, one_mul] at h₁
  rw [ha, one_mul] at h₂
  calc
    _ ≤ ‖⟪b, x⟫ • a‖ + ‖⟪a, x⟫ • b‖ := norm_sub_le _ _
    _ = ‖⟪b, x⟫‖ + ‖⟪a, x⟫‖ := by rw [norm_smul, norm_smul, ha, hb, mul_one, mul_one]
    _ ≤ 2 * ‖x‖ := by linarith

/-- The actual C1 Lagrangian suffices for Euler's identity even at zero velocity. -/
theorem velocity_euler_identity_nonzeroPosition (F : ReversibleMetric n)
    {z : Ambient n × Ambient n} (hz : z.1 ≠ 0) :
    velocityDifferential F z z.2 = 2 * lagrangian F z := by
  have hd := Finsler.AmbientEnergyRegularity.lagrangian_hasFDerivAt F hz
  have hp : HasFDerivAt (fun v : Ambient n => (z.1, v))
      (ContinuousLinearMap.inr ℝ (Ambient n) (Ambient n)) z.2 :=
    hasFDerivAt_prodMk_right z.1 z.2
  have h : HasFDerivAt (fun v : Ambient n => lagrangian F (z.1, v))
      ((fderiv ℝ (lagrangian F) z).comp (ContinuousLinearMap.inr ℝ _ _)) z.2 := by
    convert! hd.comp z.2 hp using 1
  have he := h.apply_self_eq_nsmul_of_homogeneous (k := 2) (fun r v => by
    simpa only [smul_eq_mul] using Finsler.EnergyConservation.lagrangian_velocity_smul F z.1 v r)
  simpa only [velocityDifferential, Prod.mk.eta, nsmul_eq_mul, Nat.cast_ofNat] using he

theorem recoveredCovector_velocity_euler_ae (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    (fun t => recoveredCovector b F u hc t (velocity (u.data : Space n) t)) =ᵐ[intervalMeasure]
      fun t => 2 * lagrangian F (weakJet u t) := by
  filter_upwards [recoveredCovector_velocity_ae b F u hc,
    weakJet_position_ne_zero_ae u] with t ht hz
  rw [ht]
  exact velocity_euler_identity_nonzeroPosition F hz

theorem exists_weakVelocity_momentum_bound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) : ∃ K : ℝ, 0 < K ∧
      ∀ (u : SphereLoop n) (hc : TangentCritical F u), ∀ᵐ t ∂intervalMeasure,
        ‖velocity (u.data : Space n) t‖ ≤ K * momentumSize b F u hc t := by
  obtain ⟨c, C, hc, _hC, hb⟩ := exists_density_bounds F
  have h2c : 0 < 2 * c := by positivity
  refine ⟨(2 * c)⁻¹, inv_pos.mpr h2c, fun u hu => ?_⟩
  filter_upwards [hb u, recoveredCovector_velocity_euler_ae b F u hu,
    ae_restrict_mem measurableSet_Ioo] with t ht he hmem
  have hq := norm_recoveredCovector_le_momentumSize b F u hu ⟨t, Ioo_subset_Icc_self hmem⟩
  have hle : 2 * c * ‖velocity (u.data : Space n) t‖ ^ 2 ≤
      ‖recoveredCovector b F u hu t‖ * ‖velocity (u.data : Space n) t‖ := by
    calc
      _ ≤ 2 * lagrangian F (weakJet u t) := by nlinarith [ht.1]
      _ = recoveredCovector b F u hu t (velocity (u.data : Space n) t) := he.symm
      _ ≤ ‖recoveredCovector b F u hu t (velocity (u.data : Space n) t)‖ := le_abs_self _
      _ ≤ _ := (recoveredCovector b F u hu t).le_opNorm _
  by_cases hv : ‖velocity (u.data : Space n) t‖ = 0
  · rw [hv]
    exact mul_nonneg (le_of_lt (inv_pos.mpr h2c)) (momentumSize_nonneg b F u hu t)
  · have hvp := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have hh : (2 * c) * ‖velocity (u.data : Space n) t‖ ≤ ‖recoveredCovector b F u hu t‖ :=
      (mul_le_mul_iff_right₀ hvp).mp (by nlinarith [hle])
    calc
      _ ≤ (2 * c)⁻¹ * ‖recoveredCovector b F u hu t‖ := by
        have hdiv : ‖velocity (u.data : Space n) t‖ ≤
            ‖recoveredCovector b F u hu t‖ / (2 * c) :=
          (le_div_iff₀ h2c).mpr (by nlinarith [hh])
        simpa only [div_eq_mul_inv, mul_comm] using hdiv
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (le_of_lt (inv_pos.mpr h2c))

theorem exists_force_quadratic_bound (F : ReversibleMetric n) : ∃ C : ℝ, 0 < C ∧
    ∀ (u : SphereLoop n) (A : Ambient n →L[ℝ] Ambient n), ∀ᵐ t ∂intervalMeasure,
      ‖force F u A t‖ ≤ C * ‖A‖ * ‖velocity (u.data : Space n) t‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_weakJet_partial_bounds F
  refine ⟨2 * C, by positivity, fun u A => ?_⟩
  filter_upwards [hb u, operator_representative_bound u A] with t ht hq
  unfold force
  calc
    _ ≤ ‖positionDifferential F (weakJet u t) (A (continuousRepresentative (u.data : Space n) t))‖ +
        ‖velocityDifferential F (weakJet u t) (A (velocity (u.data : Space n) t))‖ := norm_add_le _ _
    _ ≤ (C * ‖velocity (u.data : Space n) t‖ ^ 2) * ‖A‖ +
        (C * ‖velocity (u.data : Space n) t‖) * (‖A‖ * ‖velocity (u.data : Space n) t‖) := by
      apply add_le_add
      · exact ((positionDifferential F (weakJet u t)).le_opNorm _).trans
          (mul_le_mul ht.1 hq (norm_nonneg _) (by positivity))
      · exact ((velocityDifferential F (weakJet u t)).le_opNorm _).trans
          (mul_le_mul ht.2 (A.le_opNorm _) (norm_nonneg _) (by positivity))
    _ = _ := by ring

theorem exists_plane_force_momentum_bound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) : ∃ D : ℝ, 0 < D ∧
      ∀ (u : SphereLoop n) (hc : TangentCritical F u), ∀ᵐ t ∂intervalMeasure, ∀ i j,
        ‖force F u (planeRotation (b i) (b j)) t‖ ≤ D * momentumSize b F u hc t ^ 2 := by
  obtain ⟨C, hC, hf⟩ := exists_force_quadratic_bound F
  obtain ⟨K, hK, hv⟩ := exists_weakVelocity_momentum_bound b F
  refine ⟨2 * C * K ^ 2, by positivity, fun u hu => ?_⟩
  have hall : ∀ᵐ t ∂intervalMeasure, ∀ i j,
      ‖force F u (planeRotation (b i) (b j)) t‖ ≤
        C * ‖planeRotation (b i) (b j)‖ * ‖velocity (u.data : Space n) t‖ ^ 2 :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => hf u _
  filter_upwards [hall, hv u hu] with t ht hvt
  intro i j
  calc
    _ ≤ C * ‖planeRotation (b i) (b j)‖ * ‖velocity (u.data : Space n) t‖ ^ 2 := ht i j
    _ ≤ C * 2 * (K * momentumSize b F u hu t) ^ 2 := by
      gcongr
      exact planeRotation_opNorm_le_two _ _ (b.norm_eq_one i) (b.norm_eq_one j)
    _ = _ := by ring

theorem exists_weakVelocity_ae_bound (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ t ∂intervalMeasure, ‖velocity (u.data : Space n) t‖ ≤ B := by
  obtain ⟨K, hK, hb⟩ := exists_weakVelocity_momentum_bound b F
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (momentumSize_continuousOn b F u hc)
  refine ⟨K * (|M| + 1), by positivity, ?_⟩
  filter_upwards [hb u hc, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (le_of_lt hK)
  have hm := hM t (Ioo_subset_Icc_self hmem)
  calc
    _ ≤ ‖momentumSize b F u hc t‖ := le_abs_self _
    _ ≤ M := hm
    _ ≤ |M| + 1 := by linarith [le_abs_self M]

theorem energy_eq_zero_iff_momentumSize_zero (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u) :
    energy F u = 0 ↔ ∀ t : ClosedInterval, momentumSize b F u hc t = 0 := by
  constructor
  · intro hE
    have hv : (velocity (u.data : Space n) : ℝ → Ambient n) =ᵐ[intervalMeasure] fun _ => 0 := by
      rw [velocity_eq_zero_of_energy_eq_zero F u hE]
      exact Lp.coeFn_zero _ _ _
    obtain ⟨C, _hC, hb⟩ := exists_weakJet_partial_bounds F
    have hp : (fun t => velocityDifferential F (weakJet u t)) =ᵐ[intervalMeasure] fun _ => 0 := by
      filter_upwards [hv, hb u] with t hv ht
      apply norm_eq_zero.mp
      have h := ht.2
      rw [hv, norm_zero, mul_zero] at h
      exact le_antisymm h (norm_nonneg _)
    have hm (i j : ι) : EqOn
        (momentumRepresentative F u (planeRotation_isRotation (b i) (b j)) hc)
        (fun _ => 0) (Icc 0 1) := by
      apply momentumRepresentative_unique F u (planeRotation_isRotation (b i) (b j)) hc
        continuousOn_const
      filter_upwards [hp] with t ht
      simp only [momentum, ht, zero_apply]
    intro t
    unfold momentumSize
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [hm i j t.property, norm_zero]
  · intro hY
    obtain ⟨K, _hK, hb⟩ := exists_weakVelocity_momentum_bound b F
    have hv : (velocity (u.data : Space n) : ℝ → Ambient n) =ᵐ[intervalMeasure] fun _ => 0 := by
      filter_upwards [hb u hc, ae_restrict_mem measurableSet_Ioo] with t ht hmem
      apply norm_eq_zero.mp
      rw [hY ⟨t, Ioo_subset_Icc_self hmem⟩, mul_zero] at ht
      exact le_antisymm ht (norm_nonneg _)
    have hz : velocity (u.data : Space n) = 0 :=
      Lp.ext (hv.trans (Lp.coeFn_zero _ _ _).symm)
    rw [sphereLoop_eq_constant_of_velocity_eq_zero u hz]
    exact energy_constantSphereLoop F _

theorem exists_momentumSize_pos_of_energy_pos (b : OrthonormalBasis ι ℝ (Ambient n))
    (F : ReversibleMetric n) (u : SphereLoop n) (hc : TangentCritical F u)
    (hE : 0 < energy F u) : ∃ t : ClosedInterval, 0 < momentumSize b F u hc t := by
  by_contra h
  push Not at h
  have hz : ∀ t : ClosedInterval, momentumSize b F u hc t = 0 :=
    fun t => le_antisymm (h t) (momentumSize_nonneg b F u hc t)
  have he := (energy_eq_zero_iff_momentumSize_zero b F u hc).mpr hz
  linarith

end

end Finsler.SobolevRotationalBounds
