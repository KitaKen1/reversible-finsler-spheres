module

public import Finsler.Geometry.MetricComparison
public import Finsler.Analysis.QuadraticHomogeneous

/-! Actual fiberwise F² is C¹, including the zero vector.
The model is the genuine tangent space of the standard sphere, read in its
existing Euclidean coordinates. Slit smoothness comes from the actual tangent
retraction. No smoothness or Hessian at zero is assumed. This is fiberwise
calculus; joint base--velocity and H¹ energy regularity remain separate. -/

@[expose] public section

namespace Finsler.FiberEnergy

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open scoped Manifold ContDiff

noncomputable section

variable {n : ℕ}

abbrev Model (n : ℕ) := EuclideanSpace ℝ (Fin n)

def squared (F : ReversibleMetric n) (x : Sphere n) (w : Model n) : ℝ :=
  F.value ⟨x, w⟩ ^ 2

theorem squared_zero (F : ReversibleMetric n) (x : Sphere n) : squared F x 0 = 0 := by
  change F.value ⟨x, (0 : Fiber n x)⟩ ^ 2 = 0
  rw [F.zero, zero_pow (by decide : 2 ≠ 0)]

theorem squared_smul (F : ReversibleMetric n) (x : Sphere n) (r : ℝ) (w : Model n) :
    squared F x (r • w) = r ^ 2 * squared F x w := by
  change F.value ⟨x, r • (w : Fiber n x)⟩ ^ 2 = r ^ 2 * F.value ⟨x, w⟩ ^ 2
  calc
    _ = (|r| * F.value ⟨x, w⟩) ^ 2 :=
      congrArg (fun z : ℝ => z ^ 2) (value_smul F x (w : Fiber n x) r)
    _ = r ^ 2 * F.value ⟨x, w⟩ ^ 2 := by rw [mul_pow, sq_abs]

theorem fiberInclusion_smooth (x : Sphere n) :
    ContMDiff 𝓘(ℝ, Model n) (𝓡 n).tangent ∞
      (fun w : Model n => (⟨x, w⟩ : Total n)) := by
  let D : Model n →L[ℝ] Ambient n := ambientMap x
  have hpair : ContDiff ℝ ∞ (fun w : Model n => ((x : Ambient n), D w)) :=
    contDiff_const.prodMk D.contDiff
  have he : (lift ∘ fun w : Model n => ((x : Ambient n), D w)) =
      (fun w : Model n => (⟨x, w⟩ : Total n)) := by
    funext w
    exact lift_ambientPair ⟨x, w⟩
  intro w
  have h := (lift_smoothAt (ne_zero_of_mem_unit_sphere x)).comp w
    hpair.contDiffAt.contMDiffAt
  rw [he] at h
  exact h

theorem squared_smoothAt (F : ReversibleMetric n) (x : Sphere n) {w : Model n}
    (hw : w ≠ 0) : ContDiffAt ℝ ∞ (squared F x) w :=
  (((value_smoothAt F ⟨x, w⟩ hw).comp w (fiberInclusion_smooth x w)).contDiffAt.pow 2)

theorem exists_quadratic_bound (F : ReversibleMetric n) (x : Sphere n) :
    ∃ K : ℝ, ∀ w : Model n, ‖squared F x w‖ ≤ K * ‖w‖ ^ 2 := by
  let D : Model n →L[ℝ] Ambient n := ambientMap x
  obtain ⟨_c, C, _hc, hC, hb⟩ := Finsler.MetricComparison.exists_squared_bounds F
  refine ⟨C * ‖D‖ ^ 2, ?_⟩
  intro w
  change ‖F.value ⟨x, w⟩ ^ 2‖ ≤ _
  calc
    ‖F.value ⟨x, w⟩ ^ 2‖ = F.value ⟨x, w⟩ ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    _ ≤ C * ‖D w‖ ^ 2 := (hb ⟨x, w⟩).2
    _ ≤ C * (‖D‖ * ‖w‖) ^ 2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (D.le_opNorm w) 2) hC.le
    _ = (C * ‖D‖ ^ 2) * ‖w‖ ^ 2 := by ring

theorem squared_hasFDerivAt_zero (F : ReversibleMetric n) (x : Sphere n) :
    HasFDerivAt (squared F x) (0 : Model n →L[ℝ] ℝ) 0 := by
  obtain ⟨K, hK⟩ := exists_quadratic_bound F x
  exact Finsler.QuadraticHomogeneous.quadratic_bound_hasFDerivAt_zero
    (squared_zero F x) K hK

theorem squared_differentiable (F : ReversibleMetric n) (x : Sphere n) :
    Differentiable ℝ (squared F x) := by
  obtain ⟨K, hK⟩ := exists_quadratic_bound F x
  exact Finsler.QuadraticHomogeneous.differentiable_of_quadratic_bound
    (squared_zero F x) K hK (fun _ hw => squared_smoothAt F x hw)

theorem squared_contDiff_one (F : ReversibleMetric n) (x : Sphere n) :
    ContDiff ℝ 1 (squared F x) := by
  obtain ⟨K, hK⟩ := exists_quadratic_bound F x
  exact Finsler.QuadraticHomogeneous.contDiff_one (squared_zero F x) K hK
    (fun _ hw => squared_smoothAt F x hw) (squared_smul F x)

theorem squared_fderiv_zero (F : ReversibleMetric n) (x : Sphere n) :
    fderiv ℝ (squared F x) 0 = 0 := (squared_hasFDerivAt_zero F x).fderiv

theorem squared_fderiv_bound (F : ReversibleMetric n) (x : Sphere n) :
    ∃ K : ℝ, 0 < K ∧ ∀ w : Model n, ‖fderiv ℝ (squared F x) w‖ ≤ K * ‖w‖ :=
  Finsler.QuadraticHomogeneous.exists_fderiv_bound (squared_differentiable F x)
    (squared_fderiv_zero F x) (fun _ hw => squared_smoothAt F x hw) (squared_smul F x)

theorem energy_contDiff_one (F : ReversibleMetric n) (x : Sphere n) :
    ContDiff ℝ 1 (fun w : Model n => Finsler.Geometry.energy F ⟨x, w⟩) :=
  (squared_contDiff_one F x).div_const 2

theorem fiber_energy_hasFDerivAt_zero (F : ReversibleMetric n) (x : Sphere n) :
    HasFDerivAt (fun w : Fiber n x => Finsler.Geometry.energy F ⟨x, w⟩)
      (0 : Fiber n x →L[ℝ] ℝ) 0 := by
  let : NormedAddCommGroup (Fiber n x) := inferInstanceAs (NormedAddCommGroup (Model n))
  let : NormedSpace ℝ (Fiber n x) := inferInstanceAs (NormedSpace ℝ (Model n))
  obtain ⟨_c, C, _hc, hC, hb⟩ := Finsler.MetricComparison.exists_squared_bounds F
  apply Finsler.QuadraticHomogeneous.quadratic_bound_hasFDerivAt_zero
    (by change F.value ⟨x, (0 : Fiber n x)⟩ ^ 2 / 2 = 0; rw [F.zero]; norm_num)
    (C * ‖ambientMap x‖ ^ 2 / 2)
  intro w
  change ‖F.value ⟨x, w⟩ ^ 2 / 2‖ ≤ _
  calc
    ‖F.value ⟨x, w⟩ ^ 2 / 2‖ = F.value ⟨x, w⟩ ^ 2 / 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
    _ ≤ C * ‖ambientMap x w‖ ^ 2 / 2 :=
      div_le_div_of_nonneg_right (hb ⟨x, w⟩).2 (by norm_num)
    _ ≤ C * (‖ambientMap x‖ * ‖w‖) ^ 2 / 2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) ((ambientMap x).le_opNorm w) 2) hC.le)
        (by norm_num)
    _ = (C * ‖ambientMap x‖ ^ 2 / 2) * ‖w‖ ^ 2 := by ring

end

end Finsler.FiberEnergy
