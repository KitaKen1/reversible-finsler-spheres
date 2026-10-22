module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! The genuine second derivative of a real function as a self-adjoint Hilbert-space operator.
The regularity assumptions are C2 and C3, not nondegeneracy. In particular the kernel is allowed.
The gradient is the Riesz representative of the actual Frechet derivative. -/

@[expose] public section

namespace Finsler.Hessian

open InnerProductSpace
open scoped Topology ContDiff RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Riesz representative of the actual first derivative. -/
def gradient (f : E → ℝ) (x : E) : E := (toDual ℝ E).symm (fderiv ℝ f x)

/-- The Hessian bilinear form, represented as an actual continuous linear endomorphism. -/
def operator (f : E → ℝ) (x : E) : E →L[ℝ] E :=
  (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (fderiv ℝ (fderiv ℝ f) x)

theorem inner_gradient (f : E → ℝ) (x v : E) :
    ⟪gradient f x, v⟫ = fderiv ℝ f x v := toDual_symm_apply

theorem gradient_eq_zero_iff (f : E → ℝ) (x : E) :
    gradient f x = 0 ↔ fderiv ℝ f x = 0 := by
  constructor
  · intro h
    have h' := congrArg (toDual ℝ E) h
    simpa [gradient] using h'
  · intro h
    simp [gradient, h]

theorem inner_operator (f : E → ℝ) (x v w : E) :
    ⟪operator f x v, w⟫ = fderiv ℝ (fderiv ℝ f) x v w := toDual_symm_apply

/-- C2 regularity makes the actual Hessian symmetric, including at a degenerate point. -/
theorem operator_isSymmetric {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (operator f x).toLinearMap.IsSymmetric := by
  intro v w
  change ⟪operator f x v, w⟫ = ⟪v, operator f x w⟫
  rw [inner_operator, real_inner_comm (operator f x w) v, inner_operator]
  exact hf.isSymmSndFDerivAt (by simp) v w

theorem gradient_hasFDerivAt {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    HasFDerivAt (gradient f) (operator f x) x := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
    hD.hasFDerivAt

/-- The Hessian is the genuine derivative of the gradient, rather than a postulated operator. -/
theorem fderiv_gradient {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    fderiv ℝ (gradient f) x = operator f x := (gradient_hasFDerivAt hf).fderiv

theorem gradient_contDiffAt {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) :
    ContDiffAt ℝ 2 (gradient f) x :=
  (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp x
    (hf.fderiv_right (m := 2) (by norm_num))

/-- The operator vanishes on a direction exactly when the bilinear second derivative does. -/
theorem operator_apply_eq_zero_iff (f : E → ℝ) (x v : E) :
    operator f x v = 0 ↔ ∀ w, fderiv ℝ (fderiv ℝ f) x v w = 0 := by
  constructor
  · intro h w
    rw [← inner_operator, h, inner_zero_left]
  · intro h
    have hv : ⟪operator f x v, operator f x v⟫ = 0 := by
      rw [inner_operator, h]
    exact inner_self_eq_zero.mp hv

end

end Finsler.Hessian
