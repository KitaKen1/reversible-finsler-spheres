module

public import Finsler.Geometry.AmbientLagrangian
public import Finsler.Geometry.RoundMetric
public import Mathlib.Topology.Order.Compact

/-! Uniform comparison of an actual Finsler metric with the round metric.
The constants come from extrema on the compact set of unit tangent pairs;
they are not additional metric hypotheses. The integral estimates apply to
all smooth loops, including loops whose velocity vanishes. -/

@[expose] public section

namespace Finsler.MetricComparison

open Finsler.SphereGeometry Finsler.Geometry Finsler.Loops
open Finsler.SphereRetraction Finsler.AmbientLagrangian
open scoped Manifold ContDiff RealInnerProductSpace Interval

noncomputable section

variable {n : ℕ}

def unitTangentPairs (n : ℕ) : Set (Ambient n × Ambient n) :=
  {z | ‖z.1‖ = 1 ∧ ‖z.2‖ = 1 ∧ ⟪z.1, z.2⟫ = 0}

theorem unitTangentPairs_compact (n : ℕ) : IsCompact (unitTangentPairs n) := by
  have hc : IsClosed {z : Ambient n × Ambient n | ⟪z.1, z.2⟫ = 0} :=
    isClosed_eq (continuous_fst.inner continuous_snd) continuous_const
  convert ((isCompact_sphere (0 : Ambient n) 1).prod
    (isCompact_sphere (0 : Ambient n) 1)).inter_right hc using 1
  ext z
  simp [unitTangentPairs, and_assoc]

theorem lagrangian_continuousOn_unit (F : ReversibleMetric n) :
    ContinuousOn (lagrangian F) (unitTangentPairs n) := by
  intro z hz
  have hq : z.1 ≠ 0 := by
    intro h
    have := hz.1
    simp [h] at this
  exact ((F.continuous.continuousAt.comp
    (lift_smoothAt hq).continuousAt).pow 2).continuousWithinAt

theorem unit_pair_has_tangent {z : Ambient n × Ambient n}
    (hz : z ∈ unitTangentPairs n) :
    ∃ p : Total n, ambientPair p = z ∧ p.2 ≠ 0 := by
  let x : Sphere n := ⟨z.1, by simpa using hz.1⟩
  have hr : z.2 ∈ (ambientMap x).range := by
    rw [ambientMap_range]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hz.2.2
  obtain ⟨w, hw⟩ := hr
  refine ⟨⟨x, w⟩, ?_, ?_⟩
  · apply Prod.ext
    · rfl
    · exact hw
  · intro h
    change w = 0 at h
    have hv : z.2 = 0 := by
      rw [← hw, h, map_zero]
    have := hz.2.1
    simp [hv] at this

theorem lagrangian_pos_unit (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z ∈ unitTangentPairs n) : 0 < lagrangian F z := by
  obtain ⟨p, hp, hv⟩ := unit_pair_has_tangent hz
  rw [← hp, lagrangian_ambientPair]
  exact sq_pos_of_pos (F.positive p.proj p.2 hv)

theorem exists_unit_bounds (F : ReversibleMetric n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ z ∈ unitTangentPairs n, c ≤ lagrangian F z ∧ lagrangian F z ≤ C := by
  by_cases hs : (unitTangentPairs n).Nonempty
  · obtain ⟨zmin, hmin, hmin'⟩ := (unitTangentPairs_compact n).exists_isMinOn hs
      (lagrangian_continuousOn_unit F)
    obtain ⟨zmax, hmax, hmax'⟩ := (unitTangentPairs_compact n).exists_isMaxOn hs
      (lagrangian_continuousOn_unit F)
    exact ⟨lagrangian F zmin, lagrangian F zmax, lagrangian_pos_unit F hmin,
      lagrangian_pos_unit F hmax, fun z hz => ⟨hmin' hz, hmax' hz⟩⟩
  · exact ⟨1, 1, by norm_num, by norm_num, fun z hz => (hs ⟨z, hz⟩).elim⟩

theorem normalized_tangent_unit (x : Sphere n) (w : Fiber n x) (hw : w ≠ 0) :
    ambientPair ⟨x, ‖ambientMap x w‖⁻¹ • w⟩ ∈ unitTangentPairs n := by
  have hv := ambientMap_ne_zero x hw
  have hn := norm_ne_zero_iff.mpr hv
  have hi : ⟪(x : Ambient n), ambientMap x w⟫ = 0 := by
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    rw [← ambientMap_range]
    exact ⟨w, rfl⟩
  change ‖(x : Ambient n)‖ = 1 ∧
    ‖ambientMap x (‖ambientMap x w‖⁻¹ • w)‖ = 1 ∧
    ⟪(x : Ambient n), ambientMap x (‖ambientMap x w‖⁻¹ • w)⟫ = 0
  refine ⟨by simp, ?_, ?_⟩
  · simp [norm_smul, inv_mul_cancel₀ hn]
  · simp [inner_smul_right, hi]

/-- A single pair of positive constants controls every genuine tangent fiber. -/
theorem exists_squared_bounds (F : ReversibleMetric n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ p : Total n,
      c * ‖ambientVector n p‖ ^ 2 ≤ F.value p ^ 2 ∧
      F.value p ^ 2 ≤ C * ‖ambientVector n p‖ ^ 2 := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_unit_bounds F
  refine ⟨c, C, hc, hC, ?_⟩
  rintro ⟨x, w⟩
  by_cases hw : w = 0
  · subst w
    simp [ambientVector, F.zero]
  · have hv := ambientMap_ne_zero x hw
    have hn := norm_ne_zero_iff.mpr hv
    have hscale : (‖ambientMap x w‖⁻¹ : ℝ) ^ 2 * ‖ambientMap x w‖ ^ 2 = 1 := by
      field_simp
    have h := hb _ (normalized_tangent_unit x w hw)
    rw [lagrangian_ambientPair, value_smul, mul_pow, sq_abs] at h
    change c * ‖ambientMap x w‖ ^ 2 ≤ F.value ⟨x, w⟩ ^ 2 ∧
      F.value ⟨x, w⟩ ^ 2 ≤ C * ‖ambientMap x w‖ ^ 2
    have he : ((‖ambientMap x w‖⁻¹ : ℝ) ^ 2 * F.value ⟨x, w⟩ ^ 2) *
        ‖ambientMap x w‖ ^ 2 = F.value ⟨x, w⟩ ^ 2 := by
      calc
        _ = ((‖ambientMap x w‖⁻¹ : ℝ) ^ 2 * ‖ambientMap x w‖ ^ 2) *
            F.value ⟨x, w⟩ ^ 2 := by ring
        _ = _ := by rw [hscale, one_mul]
    exact ⟨by simpa only [he] using
        mul_le_mul_of_nonneg_right h.1 (sq_nonneg ‖ambientMap x w‖),
      by simpa only [he] using
        mul_le_mul_of_nonneg_right h.2 (sq_nonneg ‖ambientMap x w‖)⟩

/-- For arbitrary measurable tangent data, finite F² energy is exactly finite
round energy. This lemma does not assert that the data are weak derivatives. -/
theorem integrable_sq_value_iff {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (F : ReversibleMetric n) (p : α → Total n)
    (hF : MeasureTheory.AEStronglyMeasurable (fun t => F.value (p t) ^ 2) μ)
    (hv : MeasureTheory.AEStronglyMeasurable (fun t => ‖ambientVector n (p t)‖ ^ 2) μ) :
    MeasureTheory.Integrable (fun t => F.value (p t) ^ 2) μ ↔
      MeasureTheory.Integrable (fun t => ‖ambientVector n (p t)‖ ^ 2) μ := by
  obtain ⟨c, C, hc, _hC, hb⟩ := exists_squared_bounds F
  constructor
  · intro h
    apply (h.const_mul c⁻¹).mono' hv
    apply MeasureTheory.ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), inv_mul_eq_div]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using (hb (p t)).1
  · intro h
    apply (h.const_mul C).mono' hF
    apply MeasureTheory.ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (hb (p t)).2

theorem integrable_sq_value_iff_of_measurable {α : Type*} [MeasurableSpace α]
    [MeasurableSpace (Total n)] [BorelSpace (Total n)]
    (μ : MeasureTheory.Measure α) (F : ReversibleMetric n) (p : α → Total n)
    (hp : Measurable p) :
    MeasureTheory.Integrable (fun t => F.value (p t) ^ 2) μ ↔
      MeasureTheory.Integrable (fun t => ‖ambientVector n (p t)‖ ^ 2) μ := by
  apply integrable_sq_value_iff μ F p
  · exact ((F.continuous.pow 2).measurable.comp hp).aestronglyMeasurable
  · exact (((ambientVector_continuous n).norm.pow 2).measurable.comp hp).aestronglyMeasurable

theorem round_density (γ : SmoothLoop n) (t : ℝ) :
    Finsler.LoopEnergy.density (roundMetric n) γ t =
      ‖ambientVector n (Finsler.LoopEnergy.velocityLift γ t)‖ ^ 2 := rfl

theorem energy_bounds (F : ReversibleMetric n) {c C : ℝ}
    (hb : ∀ p : Total n,
      c * ‖ambientVector n p‖ ^ 2 ≤ F.value p ^ 2 ∧
      F.value p ^ 2 ≤ C * ‖ambientVector n p‖ ^ 2) (γ : SmoothLoop n) :
    c * Finsler.LoopEnergy.energy (roundMetric n) γ ≤ Finsler.LoopEnergy.energy F γ ∧
      Finsler.LoopEnergy.energy F γ ≤ C * Finsler.LoopEnergy.energy (roundMetric n) γ := by
  have hround := Finsler.LoopEnergy.density_intervalIntegrable (roundMetric n) γ 0 1
  have hF := Finsler.LoopEnergy.density_intervalIntegrable F γ 0 1
  constructor
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      (hround.const_mul c) hF (fun t _ => (hb (Finsler.LoopEnergy.velocityLift γ t)).1)
    simpa only [intervalIntegral.integral_const_mul, Finsler.LoopEnergy.energy] using h
  · have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
      hF (hround.const_mul C) (fun t _ => (hb (Finsler.LoopEnergy.velocityLift γ t)).2)
    simpa only [intervalIntegral.integral_const_mul, Finsler.LoopEnergy.energy] using h

theorem exists_energy_bounds (F : ReversibleMetric n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ γ : SmoothLoop n,
      c * Finsler.LoopEnergy.energy (roundMetric n) γ ≤ Finsler.LoopEnergy.energy F γ ∧
      Finsler.LoopEnergy.energy F γ ≤ C * Finsler.LoopEnergy.energy (roundMetric n) γ := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_squared_bounds F
  exact ⟨c, C, hc, hC, energy_bounds F hb⟩

end

end Finsler.MetricComparison
