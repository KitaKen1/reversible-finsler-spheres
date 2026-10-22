module

public import Finsler.Analysis.IntervalH1Energy

/-! Actual weak H¹ sphere paths without periodicity. A graph element is a sphere path when its
continuous representative lies on the unit sphere on [0,1]. The weak velocity is then tangent
almost everywhere, so the ambient Finsler density is comparable to the squared velocity and is
integrable. The path energy uses the same ambient Lagrangian as the loop energy and agrees with
it on actual sphere loops. Graph elements are determined by their continuous representatives. -/

@[expose] public section

namespace Finsler.SobolevSpherePath

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.Geometry
open Finsler.SphereRetraction Finsler.AmbientLagrangian Finsler.SobolevEnergy
open MeasureTheory Set Filter
open scoped Topology Manifold RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Graph elements are determined by their continuous representatives on [0,1]. -/
theorem eq_of_representative_eqOn {u w : Space n}
    (h : EqOn (continuousRepresentative u) (continuousRepresentative w) (Icc 0 1)) : u = w := by
  apply TauCeti.WeakDerivStep.ext
  rw [← TauCeti.WeakDerivStep.prevL_apply, ← TauCeti.WeakDerivStep.prevL_apply]
  change value u = value w
  apply Lp.ext
  have hae : continuousRepresentative u =ᵐ[intervalMeasure] continuousRepresentative w := by
    have hmem : ∀ᵐ t ∂intervalMeasure, t ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with t ht
    exact h (Ioo_subset_Icc_self ht)
  exact (value_ae_continuousRepresentative u).trans
    (hae.trans (value_ae_continuousRepresentative w).symm)

/-- Actual weak H¹ sphere paths. -/
def SpherePath (n : ℕ) : Set (Space n) :=
  {w | ∀ t ∈ Icc (0 : ℝ) 1, ‖continuousRepresentative w t‖ = 1}

theorem sphereLoop_mem (u : SphereLoop n) : (u.data : Space n) ∈ SpherePath n :=
  fun t ht => u.sphere_constraint ⟨t, ht⟩

/-- The ambient Finsler energy of an arbitrary weak H¹ graph element. -/
def pathEnergy (F : ReversibleMetric n) (w : Space n) : ℝ :=
  ∫ τ, lagrangian F (continuousRepresentative w τ, velocity w τ) ∂intervalMeasure

theorem pathEnergy_sphereLoop (F : ReversibleMetric n) (u : SphereLoop n) :
    pathEnergy F (u.data : Space n) = energy F u := rfl

theorem pathEnergy_nonneg (F : ReversibleMetric n) (w : Space n) : 0 ≤ pathEnergy F w :=
  integral_nonneg fun _ => sq_nonneg _

section Path

variable {w : Space n} (hw : w ∈ SpherePath n)
include hw

theorem velocity_orthogonal_ae :
    ∀ᵐ t ∂intervalMeasure, ⟪continuousRepresentative w t, velocity w t⟫ = 0 := by
  have hmem : ∀ᵐ t ∂intervalMeasure, t ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [continuousRepresentative_hasDerivAt_ae w, hmem] with t hd ht
  have heq : (fun s => ‖continuousRepresentative w s‖ ^ 2) =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    rw [hw s (Ioo_subset_Icc_self hs)]
    norm_num
  have hz : deriv (fun s => ‖continuousRepresentative w s‖ ^ 2) t = 0 :=
    heq.deriv_eq.trans (deriv_const t 1)
  have h := hd.norm_sq.deriv
  rw [hz] at h
  linarith

theorem jet_has_tangent_ae :
    ∀ᵐ t ∂intervalMeasure, ∃ p : Total n,
      ambientPair p = (continuousRepresentative w t, velocity w t) := by
  have hmem : ∀ᵐ t ∂intervalMeasure, t ∈ Ioo (0 : ℝ) 1 :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [velocity_orthogonal_ae hw, hmem] with t ho ht
  let x : Sphere n := ⟨continuousRepresentative w t, by
    simpa using hw t (Ioo_subset_Icc_self ht)⟩
  have hr : velocity w t ∈ (ambientMap x).range := by
    rw [ambientMap_range]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ho
  obtain ⟨v, hv⟩ := hr
  exact ⟨⟨x, v⟩, Prod.ext rfl hv⟩

theorem density_aestronglyMeasurable (F : ReversibleMetric n) :
    AEStronglyMeasurable (fun t => lagrangian F (continuousRepresentative w t, velocity w t))
      intervalMeasure := by
  have hj : AEStronglyMeasurable (fun t => (continuousRepresentative w t, velocity w t))
      intervalMeasure :=
    ((Lp.aestronglyMeasurable (value w)).congr (value_ae_continuousRepresentative w)).prodMk
      (Lp.aestronglyMeasurable (velocity w))
  have he := ((densityExtension_measurable F).comp_aemeasurable hj.aemeasurable).aestronglyMeasurable
  apply he.congr
  filter_upwards [jet_has_tangent_ae hw] with t ht
  obtain ⟨p, hp⟩ := ht
  change densityExtension F (continuousRepresentative w t, velocity w t) = _
  rw [← hp]
  exact densityExtension_eq F (z := ambientPair p) (ne_zero_of_mem_unit_sphere p.proj)

end Path

theorem exists_density_bounds (F : ReversibleMetric n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w ∈ SpherePath n, ∀ᵐ t ∂intervalMeasure,
      c * ‖velocity w t‖ ^ 2 ≤ lagrangian F (continuousRepresentative w t, velocity w t) ∧
      lagrangian F (continuousRepresentative w t, velocity w t) ≤ C * ‖velocity w t‖ ^ 2 := by
  obtain ⟨c, C, hc, hC, hb⟩ := Finsler.MetricComparison.exists_squared_bounds F
  refine ⟨c, C, hc, hC, ?_⟩
  intro w hw
  filter_upwards [jet_has_tangent_ae hw] with t ht
  obtain ⟨p, hp⟩ := ht
  have hv : ambientVector n p = velocity w t := congrArg Prod.snd hp
  rw [← hp, lagrangian_ambientPair]
  simpa only [hv] using hb p

theorem density_integrable (F : ReversibleMetric n) {w : Space n} (hw : w ∈ SpherePath n) :
    Integrable (fun t => lagrangian F (continuousRepresentative w t, velocity w t))
      intervalMeasure := by
  obtain ⟨c, C, _hc, _hC, hb⟩ := exists_density_bounds F
  apply ((integrable_velocity_sq w).const_mul C).mono' (density_aestronglyMeasurable hw F)
  filter_upwards [hb w hw] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact ht.2

theorem density_intervalIntegrable (F : ReversibleMetric n) {w : Space n}
    (hw : w ∈ SpherePath n) :
    IntervalIntegrable (fun t => lagrangian F (continuousRepresentative w t, velocity w t))
      volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    (density_integrable F hw)

theorem pathEnergy_eq_intervalIntegral (F : ReversibleMetric n) (w : Space n) :
    pathEnergy F w =
      ∫ t in (0 : ℝ)..1, lagrangian F (continuousRepresentative w t, velocity w t) := by
  change (∫ t in Ioo (0 : ℝ) 1, lagrangian F (continuousRepresentative w t, velocity w t)) = _
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]

theorem exists_pathEnergy_bounds (F : ReversibleMetric n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ w ∈ SpherePath n,
      c * (∫ t, ‖velocity w t‖ ^ 2 ∂intervalMeasure) ≤ pathEnergy F w ∧
      pathEnergy F w ≤ C * (∫ t, ‖velocity w t‖ ^ 2 ∂intervalMeasure) := by
  obtain ⟨c, C, hc, hC, hb⟩ := exists_density_bounds F
  refine ⟨c, C, hc, hC, ?_⟩
  intro w hw
  have hv := integrable_velocity_sq w
  have hE := density_integrable F hw
  have hl := integral_mono_ae (hv.const_mul c) hE ((hb w hw).mono fun _ ht => ht.1)
  have hu := integral_mono_ae hE (hv.const_mul C) ((hb w hw).mono fun _ ht => ht.2)
  change c * (∫ t, ‖velocity w t‖ ^ 2 ∂intervalMeasure) ≤
    (∫ t, lagrangian F (continuousRepresentative w t, velocity w t) ∂intervalMeasure) ∧
    (∫ t, lagrangian F (continuousRepresentative w t, velocity w t) ∂intervalMeasure) ≤
      C * (∫ t, ‖velocity w t‖ ^ 2 ∂intervalMeasure)
  exact ⟨by simpa only [MeasureTheory.integral_const_mul] using hl,
    by simpa only [MeasureTheory.integral_const_mul] using hu⟩

end

end Finsler.SobolevSpherePath
