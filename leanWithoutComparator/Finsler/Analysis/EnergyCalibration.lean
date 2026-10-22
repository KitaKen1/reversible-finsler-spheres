module

public import Finsler.Analysis.SphereDistance
public import Finsler.Analysis.IntervalChainRule

/-! Calibration of the path energy by an eikonal subsolution. If f ≥ 0 is C¹ and on a set U its
derivative in tangent directions ξ is at most 2√f(x)·√(F²(x,ξ)), then along every actual H¹
sphere path staying in U the square root √f grows by at most the square root of the energy.
The proof applies the one-dimensional chain rule to √(f + ε), bounds the integrand by the speed
√F² almost everywhere, uses (∫√F²)² ≤ ∫F² on the unit interval and lets ε → 0. In particular a
path from a zero of f to q has energy at least f(q). -/

@[expose] public section

namespace Finsler.EnergyCalibration

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevSpherePath Finsler.SphereDistance
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

noncomputable section

variable {n : ℕ}

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

/-- The speed density of a graph element. -/
def pathSpeed (F : ReversibleMetric n) (w : Space n) (t : ℝ) : ℝ :=
  Real.sqrt (lagrangian F (continuousRepresentative w t, velocity w t))

theorem pathSpeed_memLp (F : ReversibleMetric n) {w : Space n} (hw : w ∈ SpherePath n) :
    MemLp (pathSpeed F w) 2 intervalMeasure := by
  have hm : AEStronglyMeasurable (pathSpeed F w) intervalMeasure :=
    (density_aestronglyMeasurable hw F).aemeasurable.sqrt.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq hm).mpr ?_
  have hfun : (fun t => pathSpeed F w t ^ 2) =
      fun t => lagrangian F (continuousRepresentative w t, velocity w t) :=
    funext fun t => Real.sq_sqrt (sq_nonneg _)
  rw [hfun]
  exact density_integrable F hw

/-- The integral of the speed is at most the square root of the energy. -/
theorem integral_pathSpeed_le (F : ReversibleMetric n) {w : Space n} (hw : w ∈ SpherePath n) :
    ∫ t, pathSpeed F w t ∂intervalMeasure ≤ Real.sqrt (pathEnergy F w) := by
  have h := sq_integral_le_integral_sq (pathSpeed_memLp F hw)
  have hfun : (fun t => pathSpeed F w t ^ 2) =
      fun t => lagrangian F (continuousRepresentative w t, velocity w t) :=
    funext fun t => Real.sq_sqrt (sq_nonneg _)
  rw [hfun] at h
  exact Real.le_sqrt_of_sq_le h

theorem sqrt_add_le (a ε : ℝ) (ha : 0 ≤ a) (hε : 0 ≤ ε) :
    Real.sqrt (a + ε) ≤ Real.sqrt a + Real.sqrt ε := by
  rw [Real.sqrt_le_left (by positivity)]
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hε
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg ε]

section Calibration

variable (F : ReversibleMetric n) {f : Ambient n → ℝ} (hf : ContDiff ℝ 1 f) (hf0 : ∀ x, 0 ≤ f x)
  {U : Set (Ambient n)}
  (heik : ∀ x ∈ U, ‖x‖ = 1 → ∀ ξ : Ambient n, ⟪x, ξ⟫ = 0 →
    fderiv ℝ f x ξ ≤ 2 * Real.sqrt (f x) * Real.sqrt (lagrangian F (x, ξ)))
  {w : Space n} (hw : w ∈ SpherePath n)
  (hU : ∀ t ∈ Icc (0 : ℝ) 1, continuousRepresentative w t ∈ U)

include hf hf0 heik hw hU

theorem sqrt_add_eps_le {ε : ℝ} (hε : 0 < ε) :
    Real.sqrt (f (continuousRepresentative w 1) + ε) ≤
      Real.sqrt (f (continuousRepresentative w 0) + ε) + Real.sqrt (pathEnergy F w) := by
  set φ : Ambient n → ℝ := fun x => Real.sqrt (f x + ε) with hφdef
  have hpos : ∀ x, 0 < f x + ε := fun x => add_pos_of_nonneg_of_pos (hf0 x) hε
  have hφ : ContDiff ℝ 1 φ := (hf.add contDiff_const).sqrt fun x => (hpos x).ne'
  have hfd : ∀ x, fderiv ℝ φ x = (1 / (2 * Real.sqrt (f x + ε))) • fderiv ℝ f x := by
    intro x
    have h1 : HasFDerivAt (fun y => f y + ε) (fderiv ℝ f x) x :=
      ((hf.differentiable (by norm_num)) x).hasFDerivAt.add_const ε
    exact (h1.sqrt (hpos x).ne').fderiv
  have hprim : ∀ t ∈ Icc (0 : ℝ) 1, continuousRepresentative w t =
      continuousRepresentative w 0 + ∫ s in (0 : ℝ)..t, velocity w s := by
    intro t ht
    rw [← continuousRepresentative_sub w (left_mem_Icc.mpr zero_le_one) ht]
    abel
  have hchain := Finsler.IntervalChainRule.comp_sub_eq_integral hφ (velocity_intervalIntegrable w)
    hprim (continuousRepresentative_hasDerivAt_ae w) (right_mem_Icc.mpr zero_le_one)
  -- pointwise bound by the speed
  have hbound : ∀ᵐ s ∂intervalMeasure,
      fderiv ℝ φ (continuousRepresentative w s) (velocity w s) ≤ pathSpeed F w s := by
    filter_upwards [velocity_orthogonal_ae hw, ae_restrict_mem measurableSet_Ioo] with s ho hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self hs
    set x := continuousRepresentative w s
    set ξ := velocity w s
    have he := heik x (hU s hs') (hw s hs') ξ ho
    rw [hfd, smul_apply, smul_eq_mul]
    have hq : 0 < Real.sqrt (f x + ε) := Real.sqrt_pos.mpr (hpos x)
    have hle : Real.sqrt (f x) ≤ Real.sqrt (f x + ε) := Real.sqrt_le_sqrt (by linarith)
    have hL : 0 ≤ Real.sqrt (lagrangian F (x, ξ)) := Real.sqrt_nonneg _
    unfold pathSpeed
    rw [one_div, inv_mul_le_iff₀ (by positivity)]
    calc fderiv ℝ f x ξ ≤ 2 * Real.sqrt (f x) * Real.sqrt (lagrangian F (x, ξ)) := he
      _ ≤ 2 * Real.sqrt (f x + ε) * Real.sqrt (lagrangian F (x, ξ)) := by gcongr
  have hint : ∫ s in (0 : ℝ)..1,
      fderiv ℝ φ (continuousRepresentative w s) (velocity w s) ≤
      ∫ s, pathSpeed F w s ∂intervalMeasure := by
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    change ∫ s, fderiv ℝ φ (continuousRepresentative w s) (velocity w s) ∂intervalMeasure ≤ _
    by_cases hi : Integrable (fun s => fderiv ℝ φ (continuousRepresentative w s) (velocity w s))
      intervalMeasure
    · exact integral_mono_ae hi
        ((pathSpeed_memLp F hw).integrable (by norm_num)) hbound
    · rw [integral_undef hi]
      exact integral_nonneg fun s => Real.sqrt_nonneg _
  have hE := integral_pathSpeed_le F hw
  change φ (continuousRepresentative w 1) - φ (continuousRepresentative w 0) = _ at hchain
  have : φ (continuousRepresentative w 1) - φ (continuousRepresentative w 0) ≤
      Real.sqrt (pathEnergy F w) := by
    rw [hchain]
    exact hint.trans hE
  change φ (continuousRepresentative w 1) ≤ φ (continuousRepresentative w 0) + _
  linarith

/-- Calibration: √f grows along a sphere path in U by at most √E. -/
theorem sqrt_le_add_sqrt_energy :
    Real.sqrt (f (continuousRepresentative w 1)) ≤
      Real.sqrt (f (continuousRepresentative w 0)) + Real.sqrt (pathEnergy F w) := by
  apply le_of_forall_pos_lt_add
  intro δ hδ
  set ε := (δ / 2) ^ 2 with hεdef
  have hε : 0 < ε := by positivity
  have h1 := sqrt_add_eps_le F hf hf0 heik hw hU hε
  have h2 : Real.sqrt (f (continuousRepresentative w 1)) ≤
      Real.sqrt (f (continuousRepresentative w 1) + ε) := Real.sqrt_le_sqrt (by linarith)
  have h3 := sqrt_add_le (f (continuousRepresentative w 0)) ε (hf0 _) hε.le
  have h4 : Real.sqrt ε = δ / 2 := by
    rw [hεdef, Real.sqrt_sq (by positivity)]
  linarith

/-- A path from a zero of f to q has energy at least f(q). -/
theorem le_pathEnergy (h0 : f (continuousRepresentative w 0) = 0) :
    f (continuousRepresentative w 1) ≤ pathEnergy F w := by
  have h := sqrt_le_add_sqrt_energy F hf hf0 heik hw hU
  rw [h0, Real.sqrt_zero, zero_add] at h
  have hE := pathEnergy_nonneg F w
  have hf1 := hf0 (continuousRepresentative w 1)
  calc f (continuousRepresentative w 1) = Real.sqrt (f (continuousRepresentative w 1)) ^ 2 :=
        (Real.sq_sqrt hf1).symm
    _ ≤ Real.sqrt (pathEnergy F w) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    _ = pathEnergy F w := Real.sq_sqrt hE

end Calibration

end

end Finsler.EnergyCalibration
