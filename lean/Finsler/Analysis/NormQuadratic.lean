module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The actual Hessian of a Euclidean norm pulled back by a continuous
linear injection. This is used to verify strong convexity of the round metric. -/

@[expose] public section

namespace Finsler.NormQuadratic

open scoped RealInnerProductSpace

noncomputable section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def energy (L : V →L[ℝ] E) (v : V) : ℝ := ‖L v‖ ^ 2 / 2

def gradient (L : V →L[ℝ] E) : V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ V E ℝ).flip L).comp ((innerSL ℝ).comp L)

theorem gradient_apply (L : V →L[ℝ] E) (v w : V) :
    gradient L v w = ⟪L v, L w⟫ := rfl

theorem energy_hasFDerivAt (L : V →L[ℝ] E) (v : V) :
    HasFDerivAt (energy L) (gradient L v) v := by
  have h := (L.hasFDerivAt (x := v)).norm_sq.const_mul (1 / 2 : ℝ)
  convert h using 1
  · ext u
    simp [energy, div_eq_mul_inv, mul_comm]
  · ext w
    simp [gradient, ContinuousLinearMap.comp_apply]

theorem energy_fderiv (L : V →L[ℝ] E) :
    fderiv ℝ (energy L) = gradient L := by
  funext v
  exact (energy_hasFDerivAt L v).fderiv

theorem energy_hessian (L : V →L[ℝ] E) (v : V) :
    fderiv ℝ (fderiv ℝ (energy L)) v = gradient L := by
  rw [energy_fderiv]
  exact (gradient L).hasFDerivAt.fderiv

theorem energy_hessian_apply (L : V →L[ℝ] E) (v w u : V) :
    fderiv ℝ (fderiv ℝ (energy L)) v w u = ⟪L w, L u⟫ := by
  rw [energy_hessian, gradient_apply]

theorem energy_hessian_diagonal (L : V →L[ℝ] E) (v w : V) :
    fderiv ℝ (fderiv ℝ (energy L)) v w w = ‖L w‖ ^ 2 := by
  rw [energy_hessian_apply, real_inner_self_eq_norm_sq]

theorem energy_hessian_pos (L : V →L[ℝ] E) (hL : Function.Injective L)
    (v : V) {w : V} (hw : w ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (energy L)) v w w := by
  rw [energy_hessian_diagonal]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro h
  exact hw (hL (h.trans (map_zero L).symm))

end

end Finsler.NormQuadratic
