module

public import Finsler.Geometry.FiberEnergy
public import Finsler.Geometry.AmbientEnergyRegularity
public import Finsler.Analysis.HessianMonotone

/-! Injectivity of the actual fiber Legendre map. The metric's own positive
fiber Hessian gives strict monotonicity of the derivative of F²/2 along
segments avoiding zero; Euler's identity handles segments through zero. The
ambient velocity differential restricted to tangent vectors is identified with
the fiber derivative through the actual sphere inclusion, so two tangent
velocities with the same tangent covector coincide. No Legendre inverse,
dual metric or second derivative at zero is constructed. -/

@[expose] public section

namespace Finsler.FiberLegendre

open Finsler.SphereGeometry Finsler.Geometry Finsler.SphereRetraction
open Finsler.AmbientLagrangian Finsler.FiberEnergy
open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Half the squared Finsler value on the model of one actual tangent fiber. -/
def halfSquared (F : ReversibleMetric n) (x : Sphere n) (w : Model n) : ℝ :=
  F.value ⟨x, w⟩ ^ 2 / 2

theorem halfSquared_eq_squared (F : ReversibleMetric n) (x : Sphere n) (w : Model n) :
    halfSquared F x w = (1 / 2 : ℝ) * squared F x w := by
  unfold halfSquared squared
  ring

theorem halfSquared_smoothAt (F : ReversibleMetric n) (x : Sphere n) {w : Model n}
    (hw : w ≠ 0) : ContDiffAt ℝ ∞ (halfSquared F x) w :=
  (squared_smoothAt F x hw).div_const 2

theorem halfSquared_hasFDerivAt (F : ReversibleMetric n) (x : Sphere n) (w : Model n) :
    HasFDerivAt (halfSquared F x) ((1 / 2 : ℝ) • fderiv ℝ (squared F x) w) w := by
  have h := ((squared_differentiable F x) w).hasFDerivAt.const_mul (1 / 2 : ℝ)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v =>
    halfSquared_eq_squared F x v)

theorem halfSquared_fderiv (F : ReversibleMetric n) (x : Sphere n) (w : Model n) :
    fderiv ℝ (halfSquared F x) w = (1 / 2 : ℝ) • fderiv ℝ (squared F x) w :=
  (halfSquared_hasFDerivAt F x w).fderiv

theorem halfSquared_differentiable (F : ReversibleMetric n) (x : Sphere n) :
    Differentiable ℝ (halfSquared F x) := fun w =>
  (halfSquared_hasFDerivAt F x w).differentiableAt

theorem halfSquared_fderiv_zero (F : ReversibleMetric n) (x : Sphere n) :
    fderiv ℝ (halfSquared F x) 0 = 0 := by
  rw [halfSquared_fderiv, squared_fderiv_zero, smul_zero]

theorem halfSquared_nonneg (F : ReversibleMetric n) (x : Sphere n) (w : Model n) :
    0 ≤ halfSquared F x w :=
  div_nonneg (sq_nonneg _) (by norm_num)

theorem halfSquared_eq_zero (F : ReversibleMetric n) (x : Sphere n) {w : Model n}
    (h : halfSquared F x w = 0) : w = 0 := by
  have hv : F.value ⟨x, w⟩ = 0 := by
    unfold halfSquared at h
    have h2 : F.value ⟨x, w⟩ ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.mp h2
  exact (value_eq_zero_iff F x (w : Fiber n x)).mp hv

theorem halfSquared_smul (F : ReversibleMetric n) (x : Sphere n) (r : ℝ) (w : Model n) :
    halfSquared F x (r • w) = r ^ 2 * halfSquared F x w := by
  rw [halfSquared_eq_squared, halfSquared_eq_squared, squared_smul]
  ring

theorem halfSquared_euler (F : ReversibleMetric n) (x : Sphere n) (w : Model n) :
    fderiv ℝ (halfSquared F x) w w = 2 * halfSquared F x w := by
  have h := (halfSquared_differentiable F x w).hasFDerivAt.apply_self_eq_nsmul_of_homogeneous
    (k := 2) (fun r v => by simpa only [smul_eq_mul] using halfSquared_smul F x r v)
  simpa only [nsmul_eq_mul, Nat.cast_ofNat] using h

/-- The metric's own strong convexity, read on the model of the fiber. -/
theorem halfSquared_hessian_pos (F : ReversibleMetric n) (x : Sphere n) {z d : Model n}
    (hz : z ≠ 0) (hd : d ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (halfSquared F x)) z d d :=
  F.strongConvex x z d hz hd

theorem halfSquared_fderiv_injective (F : ReversibleMetric n) (x : Sphere n) {v w : Model n}
    (h : fderiv ℝ (halfSquared F x) v = fderiv ℝ (halfSquared F x) w) : v = w :=
  Finsler.HessianMonotone.eq_of_fderiv_eq
    (fun z hz => (halfSquared_smoothAt F x hz).of_le (by simp))
    (fun z hz d hd => halfSquared_hessian_pos F x hz hd) (halfSquared_euler F x)
    (halfSquared_nonneg F x) (fun z hz => halfSquared_eq_zero F x hz)
    (halfSquared_fderiv_zero F x) h

theorem lagrangian_fiber (F : ReversibleMetric n) (x : Sphere n) (w : Model n) :
    lagrangian F ((x : Ambient n), ambientMap x w) = 2 * halfSquared F x w := by
  have h := lagrangian_ambientPair F ⟨x, w⟩
  change lagrangian F (ambientPair ⟨x, w⟩) = _
  rw [h]
  unfold halfSquared
  ring

/-- The ambient velocity differential on tangent vectors is twice the fiber derivative. -/
theorem velocityDifferential_fiber (F : ReversibleMetric n) (x : Sphere n) (w k : Model n) :
    velocityDifferential F ((x : Ambient n), ambientMap x w) (ambientMap x k) =
      2 * fderiv ℝ (halfSquared F x) w k := by
  let D : Model n →L[ℝ] Ambient n := ambientMap x
  have hz : ((x : Ambient n), D w).1 ≠ 0 := ne_zero_of_mem_unit_sphere x
  have hinner : HasFDerivAt (fun h : Model n => ((x : Ambient n), D h))
      ((0 : Model n →L[ℝ] Ambient n).prod D) w :=
    (hasFDerivAt_const (x : Ambient n) w).prodMk D.hasFDerivAt
  have hcomp := (Finsler.AmbientEnergyRegularity.lagrangian_hasFDerivAt F hz).comp w hinner
  have hhalf : HasFDerivAt (fun h : Model n => lagrangian F ((x : Ambient n), D h))
      ((2 : ℝ) • fderiv ℝ (halfSquared F x) w) w :=
    ((halfSquared_differentiable F x w).hasFDerivAt.const_mul (2 : ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun h => lagrangian_fiber F x h)
  have happ := congrArg (fun L : Model n →L[ℝ] ℝ => L k) (hcomp.unique hhalf)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, smul_apply, smul_eq_mul] at happ
  rw [← happ]
  rfl

theorem ambientMap_orthogonal (x : Sphere n) (k : Model n) :
    ⟪(x : Ambient n), ambientMap x k⟫ = 0 := by
  have hk : ambientMap x k ∈ (ℝ ∙ (x : Ambient n))ᗮ := by
    rw [← ambientMap_range x]
    exact LinearMap.mem_range_self _ k
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hk

theorem exists_fiber_of_orthogonal (x : Sphere n) {v : Ambient n}
    (hv : ⟪(x : Ambient n), v⟫ = 0) : ∃ w : Model n, ambientMap x w = v := by
  have hm : v ∈ (ℝ ∙ (x : Ambient n))ᗮ :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
  rw [← ambientMap_range x] at hm
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hm
  exact ⟨w, hw⟩

/-- Legendre injectivity on actual tangent velocities, including zero velocity. -/
theorem tangent_eq_of_velocityDifferential_eq (F : ReversibleMetric n) {q v w : Ambient n}
    (hq : ‖q‖ = 1) (hv : ⟪q, v⟫ = 0) (hw : ⟪q, w⟫ = 0)
    (h : ∀ k : Ambient n, ⟪q, k⟫ = 0 →
      velocityDifferential F (q, v) k = velocityDifferential F (q, w) k) : v = w := by
  let x : Sphere n := ⟨q, by simpa using hq⟩
  obtain ⟨v', rfl⟩ := exists_fiber_of_orthogonal x hv
  obtain ⟨w', rfl⟩ := exists_fiber_of_orthogonal x hw
  have hfd : fderiv ℝ (halfSquared F x) v' = fderiv ℝ (halfSquared F x) w' := by
    ext k
    have hk := h (ambientMap x k) (ambientMap_orthogonal x k)
    change velocityDifferential F ((x : Ambient n), ambientMap x v') (ambientMap x k) =
      velocityDifferential F ((x : Ambient n), ambientMap x w') (ambientMap x k) at hk
    rw [velocityDifferential_fiber F x v' k, velocityDifferential_fiber F x w' k] at hk
    linarith
  rw [halfSquared_fderiv_injective F x hfd]

/-- The velocity differential at zero velocity vanishes on tangent vectors. -/
theorem velocityDifferential_zero_tangent (F : ReversibleMetric n) {q k : Ambient n}
    (hq : ‖q‖ = 1) (hk : ⟪q, k⟫ = 0) : velocityDifferential F (q, 0) k = 0 := by
  let x : Sphere n := ⟨q, by simpa using hq⟩
  obtain ⟨k', rfl⟩ := exists_fiber_of_orthogonal x hk
  have h := velocityDifferential_fiber F x 0 k'
  have hz : ambientMap x (0 : Model n) = 0 := (ambientMap x).map_zero
  rw [hz, halfSquared_fderiv_zero, zero_apply, mul_zero] at h
  exact h

end

end Finsler.FiberLegendre
