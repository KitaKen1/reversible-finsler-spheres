module

public import Finsler.Analysis.OperatorIndex
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-! The index of a symmetric operator along an invariant subspace. If a symmetric operator T on
a finite-dimensional real inner product space preserves a subspace K, its quadratic form is the
orthogonal sum of its restrictions to K and to the orthogonal complement of K, so the negative
index of inertia is the sum of the negative indices of the two restrictions. If K is the image
of an injective linear map L with ⟪T (L w), L w⟫ = c ⟪T₀ w, w⟫ for a positive constant c, the
restriction to K has the negative index of T₀. This is the linear algebra of the index of an
iterated closed geodesic along the iterated variations and their normal space. -/

@[expose] public section

namespace Finsler.InvariantIndex

open Module QuadraticMap Finsler.OperatorIndex
open scoped RealInnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {T : E →L[ℝ] E}

section Invariant

variable (hT : T.toLinearMap.IsSymmetric) {K : Submodule ℝ E} (hK : ∀ v ∈ K, T v ∈ K)

omit [FiniteDimensional ℝ E] in
include hT hK in
/-- The quadratic form splits orthogonally along an invariant subspace. -/
theorem quad_add {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) :
    quad T (u + v) = quad T u + quad T v := by
  have h1 : ⟪T u, v⟫ = 0 := Submodule.inner_right_of_mem_orthogonal (hK u hu) hv
  have h2 : ⟪T v, u⟫ = 0 := by
    have h : ⟪T v, u⟫ = ⟪v, T u⟫ := hT v u
    rw [h]
    exact Submodule.inner_left_of_mem_orthogonal (hK u hu) hv
  rw [quad_apply, quad_apply, quad_apply, map_add, inner_add_left, inner_add_right,
    inner_add_right, h1, h2]
  ring

include hT hK in
/-- **The index is additive along an invariant subspace and its orthogonal complement.** -/
theorem sigNeg_quad_eq_add :
    sigNeg (quad T) = sigNeg ((quad T).restrict K) + sigNeg ((quad T).restrict Kᗮ) := by
  have hc : IsCompl K Kᗮ := Submodule.isCompl_orthogonal K
  have hequiv : QuadraticMap.Equivalent
      (((quad T).restrict K).prod ((quad T).restrict Kᗮ)) (quad T) :=
    ⟨⟨Submodule.prodEquivOfIsCompl K Kᗮ hc, fun x => by
      change quad T (Submodule.prodEquivOfIsCompl K Kᗮ hc x) = _
      rw [Submodule.coe_prodEquivOfIsCompl', quad_add hT hK x.1.2 x.2.2,
        QuadraticMap.prod_apply, restrict_apply, restrict_apply]⟩⟩
  rw [← hequiv.sigNeg_eq, QuadraticForm.sigNeg_prod]

include hT hK in
/-- The index of the restriction to an invariant subspace is at most the index. -/
theorem sigNeg_restrict_le : sigNeg ((quad T).restrict K) ≤ sigNeg (quad T) := by
  rw [sigNeg_quad_eq_add hT hK]
  exact Nat.le_add_right _ _

end Invariant

omit [FiniteDimensional ℝ E] in
/-- The restriction of the quadratic form to the image of an injective linear map which
multiplies the quadratic form of another operator by a positive constant has the negative index
of that operator. -/
theorem sigNeg_restrict_range {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]
    [FiniteDimensional ℝ E₀] (T₀ : E₀ →L[ℝ] E₀) (L : E₀ →ₗ[ℝ] E) (hL : Function.Injective L)
    {c : ℝ} (hc : 0 < c) (h : ∀ w, quad T (L w) = c * quad T₀ w) :
    sigNeg ((quad T).restrict (LinearMap.range L)) = sigNeg (quad T₀) := by
  have hequiv : QuadraticMap.Equivalent (c • quad T₀) ((quad T).restrict (LinearMap.range L)) :=
    ⟨⟨LinearEquiv.ofInjective L hL, fun w => by
      change quad T (L w) = c • quad T₀ w
      rw [h, smul_eq_mul]⟩⟩
  rw [← hequiv.sigNeg_eq, QuadraticForm.sigNeg_smul_of_pos _ hc]

end

end Finsler.InvariantIndex
