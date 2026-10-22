module

public import Finsler.Analysis.IntervalH1SmoothMultiplier
public import Finsler.Analysis.IntervalH1CurveVariation

/-! Actual rotational H¹ test fields and their scalar weak momentum equation.
For a fixed skew ambient operator A, the field ψ A u is constructed in the
original weak graph. Tangent criticality gives the distributional derivative
of the actual scalar momentum, not a postulated Euler identity. Zero exclusion,
Legendre inversion and positive-critical regularity remain separate. -/

@[expose] public section

namespace Finsler.SobolevRotationalVariation

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.SobolevSmoothMultiplier Finsler.SobolevTangent
open Finsler.SobolevCurveVariation Finsler.SobolevEnergyDifferential
open Finsler.AmbientLagrangian MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff RealInnerProductSpace Distributions

noncomputable section

set_option maxHeartbeats 800000

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The quadratic characterization of a skew operator on a real inner product space. -/
def InfinitesimalRotation (A : Ambient n →L[ℝ] Ambient n) : Prop :=
  ∀ q, ⟪q, A q⟫ = 0

theorem rotation_skew_pairing {A : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) (q r : Ambient n) :
    ⟪q, A r⟫ = -⟪r, A q⟫ := by
  have h := hA (q + r)
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hA q, hA r] at h
  linarith

theorem fieldData_tangent {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (u : SphereLoop n) (hp : ψ 1 = ψ 0) :
    fieldData hψ A (u.data : Space n) ∈ tangentSubmodule u := by
  apply (mem_tangentSubmodule_iff _ _).mpr
  refine ⟨fieldData_periodic hψ A u.data hp, fun t => ?_⟩
  rw [representative_fieldData hψ A _ t.property, inner_smul_right, hA, mul_zero]

def rotationTangent {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (u : SphereLoop n) (hp : ψ 1 = ψ 0) : TangentSpace u :=
  ⟨fieldData hψ A (u.data : Space n), fieldData_tangent hψ hA u hp⟩

theorem rotationTangent_representative {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (u : SphereLoop n) (hp : ψ 1 = ψ 0) (t : ClosedInterval) :
    continuousRepresentative (rotationTangent hψ hA u hp : Space n) t =
      ψ t • A (continuousRepresentative (u.data : Space n) t) :=
  representative_fieldData hψ A _ t.property

theorem rotationTangent_velocity_ae {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (u : SphereLoop n) (hp : ψ 1 = ψ 0) :
    velocity (rotationTangent hψ hA u hp : Space n) =ᵐ[intervalMeasure]
      fun t => ψ t • A (velocity (u.data : Space n) t) +
        fderiv ℝ ψ t 1 • A (continuousRepresentative (u.data : Space n) t) :=
  velocity_fieldData_ae hψ A _

def momentum (F : ReversibleMetric n) (u : SphereLoop n)
    (A : Ambient n →L[ℝ] Ambient n) (t : ℝ) : ℝ :=
  velocityDifferential F (weakJet u t) (A (continuousRepresentative (u.data : Space n) t))

def force (F : ReversibleMetric n) (u : SphereLoop n)
    (A : Ambient n →L[ℝ] Ambient n) (t : ℝ) : ℝ :=
  positionDifferential F (weakJet u t) (A (continuousRepresentative (u.data : Space n) t)) +
    velocityDifferential F (weakJet u t) (A (velocity (u.data : Space n) t))

theorem variationCandidate_rotation {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (F : ReversibleMetric n) (u : SphereLoop n) (A : Ambient n →L[ℝ] Ambient n) :
    variationCandidate F u (fieldData hψ A (u.data : Space n)) =
      ∫ t, ψ t * force F u A t + fderiv ℝ ψ t 1 * momentum F u A t ∂intervalMeasure := by
  apply integral_congr_ae
  filter_upwards [velocity_fieldData_ae hψ A (u.data : Space n),
    ae_restrict_mem measurableSet_Ioo] with t hv ht
  rw [representative_fieldData hψ A _ (Ioo_subset_Icc_self ht), hv,
    map_smul, map_add, map_smul, map_smul]
  simp only [force, momentum, smul_eq_mul]
  ring

theorem tangentCritical_rotation_identity {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hp : ψ 1 = ψ 0) (hc : TangentCritical F u) :
    (∫ t, ψ t * force F u A t + fderiv ℝ ψ t 1 * momentum F u A t ∂intervalMeasure) = 0 := by
  rw [← variationCandidate_rotation hψ]
  exact (tangentCritical_iff F u).mp hc (rotationTangent hψ hA u hp)

theorem representative_aestronglyMeasurable (u : SphereLoop n) :
    AEStronglyMeasurable (continuousRepresentative (u.data : Space n)) intervalMeasure :=
  (Lp.aestronglyMeasurable (value (u.data : Space n))).congr
    (value_ae_continuousRepresentative (u.data : Space n))

theorem operator_representative_bound (u : SphereLoop n)
    (A : Ambient n →L[ℝ] Ambient n) :
    ∀ᵐ t ∂intervalMeasure, ‖A (continuousRepresentative (u.data : Space n) t)‖ ≤ ‖A‖ := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  simpa only [u.sphere_constraint ⟨t, Ioo_subset_Icc_self ht⟩, mul_one] using
    A.le_opNorm (continuousRepresentative (u.data : Space n) t)

theorem momentum_memLp_two (F : ReversibleMetric n) (u : SphereLoop n)
    (A : Ambient n →L[ℝ] Ambient n) : MemLp (momentum F u A) 2 intervalMeasure := by
  have he : Continuous (fun p : (Ambient n →L[ℝ] ℝ) × Ambient n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hm := he.comp_aestronglyMeasurable ((velocity_aestronglyMeasurable F u).prodMk
    (A.continuous.comp_aestronglyMeasurable (representative_aestronglyMeasurable u)))
  apply ((velocity_memLp_two F u).norm.const_mul ‖A‖).mono' hm
  filter_upwards [operator_representative_bound u A] with t ht
  exact ((velocityDifferential F (weakJet u t)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_comm _ _))

theorem momentum_integrable (F : ReversibleMetric n) (u : SphereLoop n)
    (A : Ambient n →L[ℝ] Ambient n) : Integrable (momentum F u A) intervalMeasure := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  exact (momentum_memLp_two F u A).integrable (by norm_num)

theorem force_integrable (F : ReversibleMetric n) (u : SphereLoop n)
    (A : Ambient n →L[ℝ] Ambient n) : Integrable (force F u A) intervalMeasure := by
  have hq := A.continuous.comp_aestronglyMeasurable (representative_aestronglyMeasurable u)
  have hv := A.continuous.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable (velocity (u.data : Space n)))
  have he : Continuous (fun p : (Ambient n →L[ℝ] ℝ) × Ambient n => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hiq : Integrable (fun t => positionDifferential F (weakJet u t)
      (A (continuousRepresentative (u.data : Space n) t))) intervalMeasure := by
    apply ((position_integrable F u).norm.const_mul ‖A‖).mono'
      (he.comp_aestronglyMeasurable ((position_aestronglyMeasurable F u).prodMk hq))
    filter_upwards [operator_representative_bound u A] with t ht
    exact ((positionDifferential F (weakJet u t)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (mul_comm _ _))
  have hiv : Integrable (fun t => velocityDifferential F (weakJet u t)
      (A (velocity (u.data : Space n) t))) intervalMeasure := by
    apply (((velocity_memLp_two F u).norm.integrable_mul
      (Lp.memLp (velocity (u.data : Space n))).norm).const_mul ‖A‖).mono'
      (he.comp_aestronglyMeasurable ((velocity_aestronglyMeasurable F u).prodMk hv))
    exact ae_of_all _ fun t =>
      ((velocityDifferential F (weakJet u t)).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)).trans_eq
          (by simp only [Pi.mul_apply]; ring))
  exact hiq.add hiv

theorem continuous_mul_integrable {f ψ : ℝ → ℝ}
    (hf : Integrable f intervalMeasure) (hψ : Continuous ψ) :
    Integrable (fun t => ψ t * f t) intervalMeasure := by
  simpa only [smul_eq_mul] using memLp_one_iff_integrable.mp
    (continuous_smul_memLp (memLp_one_iff_integrable.mpr hf) hψ)

theorem tangentCritical_rotation_ibp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hp : ψ 1 = ψ 0) (hc : TangentCritical F u) :
    (∫ t, fderiv ℝ ψ t 1 * momentum F u A t ∂intervalMeasure) =
      -(∫ t, ψ t * force F u A t ∂intervalMeasure) := by
  have h := tangentCritical_rotation_identity hψ F u hA hp hc
  rw [integral_add (continuous_mul_integrable (force_integrable F u A) hψ.continuous)
    (continuous_mul_integrable (momentum_integrable F u A)
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const))] at h
  linarith

theorem momentum_hasWeakLineDeriv (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) :
    TauCeti.HasWeakLineDerivOn volume unitInterval (momentum F u A) (force F u A) 1 := by
  have hm : IntegrableOn (momentum F u A) (Finsler.IntervalSobolev.unitInterval : Set ℝ) volume :=
    momentum_integrable F u A
  have hf : IntegrableOn (force F u A) (Finsler.IntervalSobolev.unitInterval : Set ℝ) volume :=
    force_integrable F u A
  apply (TauCeti.hasWeakLineDerivOn_iff hm.locallyIntegrableOn hf.locallyIntegrableOn).mpr
  intro ψ hψ _hψc hψs
  change tsupport ψ ⊆ Ioo 0 1 at hψs
  have hψ0 : ψ 0 = 0 := image_eq_zero_of_notMem_tsupport (fun hx =>
    lt_irrefl _ (hψs hx).1)
  have hψ1 : ψ 1 = 0 := image_eq_zero_of_notMem_tsupport (fun hx =>
    lt_irrefl _ (hψs hx).2)
  have h := tangentCritical_rotation_ibp hψ F u hA (hψ1.trans hψ0.symm) hc
  have hd (t : ℝ) : lineDeriv ℝ ψ t 1 = fderiv ℝ ψ t 1 :=
    (hψ.differentiable (by simp) t).lineDeriv_eq_fderiv
  have hleft : (∫ t, fderiv ℝ ψ t 1 * momentum F u A t ∂intervalMeasure) =
      ∫ t, lineDeriv ℝ ψ t 1 * momentum F u A t := by
    change (∫ t in Ioo (0 : ℝ) 1, fderiv ℝ ψ t 1 * momentum F u A t) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · simp only [hd]
    · intro t ht
      simp [fderiv_of_notMem_tsupport ℝ (fun hx => ht (hψs hx))]
  have hright : (∫ t, ψ t * force F u A t ∂intervalMeasure) =
      ∫ t, ψ t * force F u A t := by
    change (∫ t in Ioo (0 : ℝ) 1, ψ t * force F u A t) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro t ht
    rw [image_eq_zero_of_notMem_tsupport (fun hx => ht (hψs hx)), zero_mul]
  simpa only [smul_eq_mul, hleft, hright] using h

theorem force_intervalIntegrable (F : ReversibleMetric n) (u : SphereLoop n)
    (A : Ambient n →L[ℝ] Ambient n) : IntervalIntegrable (force F u A) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (force_integrable F u A)

theorem exists_momentum_eq_const_add_primitive (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) :
    ∃ c : ℝ, momentum F u A =ᵐ[intervalMeasure]
      fun t => c + Finsler.IntervalPrimitive.primitive (force F u A) t := by
  obtain ⟨c, he⟩ := Finsler.IntervalWeakConstant.exists_ae_const_of_equal_weak_derivatives
    (momentum_hasWeakLineDeriv F u hA hc)
    (Finsler.IntervalPrimitive.primitive_hasWeakLineDeriv (force_intervalIntegrable F u A))
  refine ⟨c, ?_⟩
  filter_upwards [he] with t ht
  exact sub_eq_iff_eq_add.mp ht

def momentumRepresentative (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) (t : ℝ) : ℝ :=
  (exists_momentum_eq_const_add_primitive F u hA hc).choose +
    Finsler.IntervalPrimitive.primitive (force F u A) t

theorem momentum_ae_representative (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) :
    momentum F u A =ᵐ[intervalMeasure] momentumRepresentative F u hA hc :=
  (exists_momentum_eq_const_add_primitive F u hA hc).choose_spec

theorem momentumRepresentative_continuousOn (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) :
    ContinuousOn (momentumRepresentative F u hA hc) (Icc 0 1) :=
  continuousOn_const.add
    (Finsler.IntervalPrimitive.primitive_continuousOn (force_intervalIntegrable F u A))

theorem momentumRepresentative_sub (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) :
    momentumRepresentative F u hA hc t - momentumRepresentative F u hA hc s =
      ∫ x in s..t, force F u A x := by
  have h0 (z : ℝ) (hz : z ∈ Icc 0 1) : IntervalIntegrable (force F u A) volume 0 z := by
    refine ⟨(force_intervalIntegrable F u A).1.mono_set (Ioc_subset_Ioc le_rfl hz.2), ?_⟩
    simp only [Ioc_eq_empty (not_lt.mpr hz.1), integrableOn_empty]
  change (_ + Finsler.IntervalPrimitive.primitive _ t) -
    (_ + Finsler.IntervalPrimitive.primitive _ s) = _
  rw [add_sub_add_left_eq_sub]
  exact intervalIntegral.integral_interval_sub_left (h0 t ht) (h0 s hs)

theorem force_integral_zero (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) : (∫ t, force F u A t ∂intervalMeasure) = 0 := by
  have h := tangentCritical_rotation_identity (ψ := fun _ => 1) contDiff_const
    F u hA rfl hc
  simpa only [one_mul, fderiv_fun_const, Pi.zero_apply, zero_apply, zero_mul, add_zero]
    using h

theorem momentumRepresentative_periodic_trace (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) :
    momentumRepresentative F u hA hc 1 = momentumRepresentative F u hA hc 0 := by
  apply sub_eq_zero.mp
  rw [momentumRepresentative_sub F u hA hc (by norm_num) (by norm_num),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  exact force_integral_zero F u hA hc

theorem momentumRepresentative_hasWeakLineDeriv (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) : TauCeti.HasWeakLineDerivOn volume unitInterval
      (momentumRepresentative F u hA hc) (force F u A) 1 :=
  (momentum_hasWeakLineDeriv F u hA hc).congr_ae (momentum_ae_representative F u hA hc)

theorem momentumRepresentative_unique (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) {r : ℝ → ℝ}
    (hr : ContinuousOn r (Icc 0 1)) (he : momentum F u A =ᵐ[intervalMeasure] r) :
    EqOn (momentumRepresentative F u hA hc) r (Icc 0 1) := by
  have h := (momentum_ae_representative F u hA hc).symm.trans he
  change _ =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] _ at h
  rw [restrict_Ioo_eq_restrict_Icc] at h
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) h
    (momentumRepresentative_continuousOn F u hA hc) hr

theorem rotation_zero : InfinitesimalRotation (0 : Ambient n →L[ℝ] Ambient n) := by
  intro q
  simp

theorem rotation_add {A B : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) (hB : InfinitesimalRotation B) :
    InfinitesimalRotation (A + B) := by
  intro q
  simp only [add_apply, inner_add_right, hA q, hB q, add_zero]

theorem rotation_smul {A : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) (c : ℝ) : InfinitesimalRotation (c • A) := by
  intro q
  simp only [smul_apply, inner_smul_right, hA q, mul_zero]

theorem momentum_add (F : ReversibleMetric n) (u : SphereLoop n)
    (A B : Ambient n →L[ℝ] Ambient n) (t : ℝ) :
    momentum F u (A + B) t = momentum F u A t + momentum F u B t := by
  simp only [momentum, add_apply, map_add]

theorem momentum_smul (F : ReversibleMetric n) (u : SphereLoop n)
    (A : Ambient n →L[ℝ] Ambient n) (c t : ℝ) :
    momentum F u (c • A) t = c * momentum F u A t := by
  simp only [momentum, smul_apply, map_smul, smul_eq_mul]

theorem momentumRepresentative_zero (F : ReversibleMetric n) (u : SphereLoop n)
    (hc : TangentCritical F u) (t : ClosedInterval) :
    momentumRepresentative F u rotation_zero hc t = 0 := by
  apply momentumRepresentative_unique F u rotation_zero hc continuousOn_const _ t.property
  exact ae_of_all _ fun s => by simp [momentum]

theorem momentumRepresentative_add (F : ReversibleMetric n) (u : SphereLoop n)
    {A B : Ambient n →L[ℝ] Ambient n}
    (hA : InfinitesimalRotation A) (hB : InfinitesimalRotation B)
    (hc : TangentCritical F u) (t : ClosedInterval) :
    momentumRepresentative F u (rotation_add hA hB) hc t =
      momentumRepresentative F u hA hc t + momentumRepresentative F u hB hc t := by
  apply momentumRepresentative_unique F u (rotation_add hA hB) hc
    ((momentumRepresentative_continuousOn F u hA hc).add
      (momentumRepresentative_continuousOn F u hB hc)) _ t.property
  filter_upwards [momentum_ae_representative F u hA hc,
    momentum_ae_representative F u hB hc] with s h₁ h₂
  rw [momentum_add, h₁, h₂]
  rfl

theorem momentumRepresentative_smul (F : ReversibleMetric n) (u : SphereLoop n)
    {A : Ambient n →L[ℝ] Ambient n} (hA : InfinitesimalRotation A)
    (hc : TangentCritical F u) (c : ℝ) (t : ClosedInterval) :
    momentumRepresentative F u (rotation_smul hA c) hc t =
      c * momentumRepresentative F u hA hc t := by
  apply momentumRepresentative_unique F u (rotation_smul hA c) hc
    (continuousOn_const.mul (momentumRepresentative_continuousOn F u hA hc)) _ t.property
  filter_upwards [momentum_ae_representative F u hA hc] with s hs
  rw [momentum_smul, hs]
  rfl

end

end Finsler.SobolevRotationalVariation
