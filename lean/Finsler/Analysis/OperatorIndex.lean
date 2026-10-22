module

public import Finsler.Analysis.HessianSplitting
public import Mathlib.LinearAlgebra.QuadraticForm.Signature
public import Mathlib.LinearAlgebra.QuadraticForm.Real

/-! The index of a symmetric operator as the negative index of inertia of its quadratic form.
For a symmetric operator T on a finite-dimensional real inner product space, the quadratic form
v ↦ ⟪T v, v⟫ is diagonal in an orthonormal basis of eigenvectors with the eigenvalues as
weights. By Sylvester's law of inertia its negative index of inertia (the maximal dimension of
a subspace on which the form is negative definite) is the number of negative eigenvalues, that
is, the dimension of the negative spectral part. -/

@[expose] public section

namespace Finsler.OperatorIndex

open Module QuadraticMap
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bilinear form (v, w) ↦ ⟪T v, w⟫. -/
def bilin (T : E →L[ℝ] E) : LinearMap.BilinForm ℝ E := (innerₗ E).comp T.toLinearMap

theorem bilin_apply (T : E →L[ℝ] E) (v w : E) : bilin T v w = ⟪T v, w⟫ := rfl

/-- The quadratic form v ↦ ⟪T v, v⟫. -/
def quad (T : E →L[ℝ] E) : QuadraticForm ℝ E := (bilin T).toQuadraticMap

theorem quad_apply (T : E →L[ℝ] E) (v : E) : quad T v = ⟪T v, v⟫ := rfl

/-- For a symmetric operator the associated bilinear form of the quadratic form is the form
of the operator. -/
theorem associated_quad {T : E →L[ℝ] E} (hT : T.toLinearMap.IsSymmetric) :
    QuadraticMap.associated (R := ℝ) (quad T) = bilin T := by
  have hsymm : (bilin T).IsSymm := ⟨fun v w => by
    change ⟪T v, w⟫ = ⟪T w, v⟫
    rw [real_inner_comm]
    exact (hT w v).symm⟩
  exact QuadraticMap.associated_left_inverse (S := ℝ) hsymm.eq

variable [FiniteDimensional ℝ E]

/-- **The negative index of inertia counts the negative eigenvalues.** -/
theorem sigNeg_quad {T : E →L[ℝ] E} (hT : T.toLinearMap.IsSymmetric) :
    sigNeg (quad T) = {i | hT.eigenvalues rfl i < 0}.ncard := by
  let b := hT.eigenvectorBasis rfl
  have heigen : ∀ i, T (b i) = (hT.eigenvalues rfl i : ℝ) • b i := fun i =>
    hT.apply_eigenvectorBasis rfl i
  have horth : (QuadraticMap.associated (R := ℝ) (quad T)).IsOrthoᵢ b := by
    rw [LinearMap.isOrthoᵢ_def]
    intro i j hij
    rw [associated_quad hT, bilin_apply, heigen, real_inner_smul_left,
      orthonormal_iff_ite.mp b.orthonormal i j]
    simp [hij]
  have hequiv : QuadraticMap.Equivalent (quad T)
      (QuadraticMap.weightedSumSquares ℝ fun i ↦ quad T (b i)) :=
    ⟨QuadraticForm.isometryEquivWeightedSumSquares (quad T) b.toBasis horth⟩
  have hweights : (fun i ↦ quad T (b i)) = hT.eigenvalues rfl := by
    funext i
    rw [quad_apply, heigen, real_inner_smul_left, orthonormal_iff_ite.mp b.orthonormal i i]
    simp
  rw [hweights] at hequiv
  exact QuadraticForm.sigNeg_of_equiv_weightedSumSquares hequiv

/-- The dimension of the negative spectral part is the negative index of inertia. -/
theorem finrank_negative (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) :
    finrank ℝ (HessianSplitting.negative T hT) = sigNeg (quad T) := by
  rw [HessianSplitting.finrank_negative, sigNeg_quad hT]

end

end Finsler.OperatorIndex
