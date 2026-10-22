module

public import Finsler.Analysis.IntervalH1Sphere
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! Finite actual Finsler energy of periodic interval sphere H¹ data.
The density uses the actual tangent retraction of the actual weak jet.
Its measurable extension changes only zero ambient positions, which do not
occur on the sphere interval. Differentiability and circle actions are separate. -/

@[expose] public section

namespace Finsler.SobolevEnergy

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.Geometry
open Finsler.SphereRetraction Finsler.AmbientLagrangian MeasureTheory Set Filter
open scoped Topology Manifold RealInnerProductSpace

noncomputable section

def nonzeroPosition (n : ℕ) : Set (Ambient n × Ambient n) := {z | z.1 ≠ 0}

theorem nonzeroPosition_open (n : ℕ) : IsOpen (nonzeroPosition n) :=
  isOpen_ne_fun continuous_fst continuous_const

theorem density_continuousOn {n : ℕ} (F : ReversibleMetric n) :
    ContinuousOn (lagrangian F) (nonzeroPosition n) := by
  intro z hz
  exact ((F.continuous.continuousAt.comp (lift_smoothAt hz).continuousAt).pow 2).continuousWithinAt

def densityExtension {n : ℕ} (F : ReversibleMetric n) : Ambient n × Ambient n → ℝ := by
  classical
  exact (nonzeroPosition n).piecewise (lagrangian F) (fun _ => 0)

theorem densityExtension_eq {n : ℕ} (F : ReversibleMetric n) {z : Ambient n × Ambient n}
    (hz : z.1 ≠ 0) : densityExtension F z = lagrangian F z := by
  classical
  exact piecewise_eq_of_mem (nonzeroPosition n) (lagrangian F) (fun _ => 0) hz

theorem densityExtension_measurable {n : ℕ} (F : ReversibleMetric n) :
    Measurable (densityExtension F) := by
  classical
  exact (density_continuousOn F).measurable_piecewise continuousOn_const
    (nonzeroPosition_open n).measurableSet

theorem density_aestronglyMeasurable {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) :
    AEStronglyMeasurable (fun t => lagrangian F (weakJet u t)) intervalMeasure := by
  have he := ((densityExtension_measurable F).comp_aemeasurable
    (weakJet_aestronglyMeasurable u).aemeasurable).aestronglyMeasurable
  apply he.congr
  filter_upwards [weakJet_has_tangent_ae u] with t ht
  obtain ⟨p, hp⟩ := ht
  change densityExtension F (weakJet u t) = lagrangian F (weakJet u t)
  rw [← hp]
  exact densityExtension_eq F (z := ambientPair p) (ne_zero_of_mem_unit_sphere p.proj)

theorem density_nonneg {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) (t : ℝ) :
    0 ≤ lagrangian F (weakJet u t) := sq_nonneg _

theorem exists_density_bounds {n : ℕ} (F : ReversibleMetric n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : SphereLoop n, ∀ᵐ t ∂intervalMeasure,
      c * ‖velocity (u.data : Space n) t‖ ^ 2 ≤ lagrangian F (weakJet u t) ∧
      lagrangian F (weakJet u t) ≤ C * ‖velocity (u.data : Space n) t‖ ^ 2 := by
  obtain ⟨c, C, hc, hC, hb⟩ := Finsler.MetricComparison.exists_squared_bounds F
  refine ⟨c, C, hc, hC, ?_⟩
  intro u
  filter_upwards [weakJet_has_tangent_ae u] with t ht
  obtain ⟨p, hp⟩ := ht
  have hv : ambientVector n p = velocity (u.data : Space n) t := congrArg Prod.snd hp
  rw [← hp, lagrangian_ambientPair]
  simpa only [hv] using hb p

theorem density_integrable {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) :
    Integrable (fun t => lagrangian F (weakJet u t)) intervalMeasure := by
  obtain ⟨c, C, _hc, _hC, hb⟩ := exists_density_bounds F
  apply ((integrable_velocity_sq (u.data : Space n)).const_mul C).mono'
    (density_aestronglyMeasurable F u)
  filter_upwards [hb u] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (density_nonneg F u t)]
  exact ht.2

def energy {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) : ℝ :=
  ∫ t, lagrangian F (weakJet u t) ∂intervalMeasure

theorem energy_nonneg {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) : 0 ≤ energy F u :=
  integral_nonneg (density_nonneg F u)

theorem energy_eq_intervalIntegral {n : ℕ} (F : ReversibleMetric n) (u : SphereLoop n) :
    energy F u = ∫ t in (0 : ℝ)..1, lagrangian F (weakJet u t) := by
  change (∫ t in Ioo (0 : ℝ) 1, lagrangian F (weakJet u t)) = _
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]

theorem exists_energy_bounds {n : ℕ} (F : ReversibleMetric n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : SphereLoop n,
      c * (∫ t, ‖velocity (u.data : Space n) t‖ ^ 2 ∂intervalMeasure) ≤ energy F u ∧
      energy F u ≤ C * (∫ t, ‖velocity (u.data : Space n) t‖ ^ 2 ∂intervalMeasure) := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_density_bounds F
  refine ⟨c, C, hc, hC, ?_⟩
  intro u
  have hv := integrable_velocity_sq (u.data : Space n)
  have hE := density_integrable F u
  have hl := integral_mono_ae (hv.const_mul c) hE ((hb u).mono fun _ ht => ht.1)
  have hu := integral_mono_ae hE (hv.const_mul C) ((hb u).mono fun _ ht => ht.2)
  change c * (∫ t, ‖velocity (u.data : Space n) t‖ ^ 2 ∂intervalMeasure) ≤
    (∫ t, lagrangian F (weakJet u t) ∂intervalMeasure) ∧
    (∫ t, lagrangian F (weakJet u t) ∂intervalMeasure) ≤
      C * (∫ t, ‖velocity (u.data : Space n) t‖ ^ 2 ∂intervalMeasure)
  exact ⟨by simpa only [MeasureTheory.integral_const_mul] using hl,
    by simpa only [MeasureTheory.integral_const_mul] using hu⟩

theorem velocity_sq_integral_eq_norm_sq {n : ℕ} (u : Space n) :
    (∫ t, ‖velocity u t‖ ^ 2 ∂intervalMeasure) = ‖velocity u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (velocity u), L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun _ => (real_inner_self_eq_norm_sq _).symm

theorem exists_energy_norm_bounds {n : ℕ} (F : ReversibleMetric n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : SphereLoop n,
      c * ‖velocity (u.data : Space n)‖ ^ 2 ≤ energy F u ∧
      energy F u ≤ C * ‖velocity (u.data : Space n)‖ ^ 2 := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_energy_bounds F
  refine ⟨c, C, hc, hC, fun u => ?_⟩
  simpa only [velocity_sq_integral_eq_norm_sq] using hb u

theorem sphereLoop_value_norm_sq {n : ℕ} (u : SphereLoop n) :
    ‖value (u.data : Space n)‖ ^ 2 = 1 := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hm : ∀ᵐ t ∂intervalMeasure, t ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  have hpoint : (fun t => ⟪value (u.data : Space n) t, value (u.data : Space n) t⟫) =ᵐ[intervalMeasure]
      fun _ => (1 : ℝ) := by
    filter_upwards [value_ae_continuousRepresentative (u.data : Space n), hm] with t hv ht
    rw [real_inner_self_eq_norm_sq, hv, u.sphere_constraint ⟨t, Ioo_subset_Icc_self ht⟩]
    norm_num
  rw [integral_congr_ae hpoint]
  simp only [integral_const, probReal_univ, one_smul]

theorem sphereLoop_h1_norm_sq {n : ℕ} (u : SphereLoop n) :
    ‖(u.data : Space n)‖ ^ 2 = 1 + ‖velocity (u.data : Space n)‖ ^ 2 := by
  rw [norm_sq_eq, sphereLoop_value_norm_sq]

theorem exists_energy_h1_bounds {n : ℕ} (F : ReversibleMetric n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : SphereLoop n,
      c * (‖(u.data : Space n)‖ ^ 2 - 1) ≤ energy F u ∧
      energy F u ≤ C * (‖(u.data : Space n)‖ ^ 2 - 1) := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_energy_norm_bounds F
  refine ⟨c, C, hc, hC, fun u => ?_⟩
  simpa only [sphereLoop_h1_norm_sq, add_sub_cancel_left] using hb u

end

end Finsler.SobolevEnergy
