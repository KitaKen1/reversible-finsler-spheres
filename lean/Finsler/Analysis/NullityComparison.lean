module

public import Finsler.Analysis.IndexComparison

/-! Comparison of the nullities of two symmetric operators related by an isometric section and a
form-decreasing retraction. For a symmetric operator T on a finite-dimensional real inner
product space, the dimension of the kernel plus the positive and negative indices of inertia of
the quadratic form v ↦ ⟪T v, v⟫ is the dimension of the space, and the largest dimension of a
subspace on which the form is nonpositive is the negative index plus the nullity. Let T₁, T₂ be
symmetric, L a linear map with ⟪T₂ L v, L v⟫ = ⟪T₁ v, v⟫, and π a linear map with π L = 1 and
⟪T₁ π u, π u⟫ ≤ ⟪T₂ u, u⟫. Then the negative indices agree. If moreover the form of T₂ is
positive on the nonzero vectors of the kernel of π, the nullities agree. This is the linear
algebra of the invariance of the nullity of a polygon under refinement. -/

@[expose] public section

namespace Finsler.NullityComparison

open Module QuadraticMap Finsler.OperatorIndex
open scoped RealInnerProductSpace

noncomputable section

section One

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The positive index of inertia counts the positive eigenvalues. -/
theorem sigPos_quad {T : E →L[ℝ] E} (hT : T.toLinearMap.IsSymmetric) :
    sigPos (quad T) = {i | 0 < hT.eigenvalues rfl i}.ncard := by
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
  exact QuadraticForm.sigPos_of_equiv_weightedSumSquares hequiv

/-- The nullity and the two indices of inertia add up to the dimension. -/
theorem finrank_ker_add (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) :
    finrank ℝ (LinearMap.ker T.toLinearMap) + sigPos (quad T) + sigNeg (quad T) =
      finrank ℝ E := by
  have h := HessianSplitting.finrank_three_parts T hT
  rw [HessianSplitting.finrank_negative, HessianSplitting.finrank_positive] at h
  rw [sigPos_quad hT, sigNeg_quad hT]
  omega

/-- A subspace on which the form is nonpositive has dimension at most the negative index plus
the nullity. -/
theorem finrank_le_of_nonpos (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric)
    (V : Submodule ℝ E) (hV : ∀ x ∈ V, quad T x ≤ 0) :
    finrank ℝ V ≤ sigNeg (quad T) + finrank ℝ (LinearMap.ker T.toLinearMap) := by
  have h1 := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := quad T) hV
  have h2 := finrank_ker_add T hT
  omega

/-- There is a subspace of dimension the negative index plus the nullity on which the form is
nonpositive. -/
theorem exists_nonpos (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) :
    ∃ V : Submodule ℝ E,
      finrank ℝ V = sigNeg (quad T) + finrank ℝ (LinearMap.ker T.toLinearMap) ∧
      ∀ x ∈ V, quad T x ≤ 0 := by
  obtain ⟨U, hU, hneg⟩ := exists_finrank_eq_sigNeg_and_negDef (quad T)
  have hUneg : ∀ a : E, a ∈ U → a ≠ 0 → quad T a < 0 := by
    intro a ha ha0
    have hpos := hneg ⟨a, ha⟩ (fun h0 => ha0 (congrArg Subtype.val h0))
    rw [restrict_apply, neg_apply] at hpos
    linarith
  have hdisj : U ⊓ LinearMap.ker T.toLinearMap = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxU, hxK⟩
    by_contra hx0
    have h1 := hUneg x hxU hx0
    have hTx : T x = 0 := LinearMap.mem_ker.mp hxK
    rw [quad_apply, hTx, inner_zero_left] at h1
    exact lt_irrefl _ h1
  refine ⟨U ⊔ LinearMap.ker T.toLinearMap, ?_, ?_⟩
  · have h := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker T.toLinearMap)
    rw [hdisj, finrank_bot, add_zero] at h
    rw [h, hU]
  · intro x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
    have hTc : T c = 0 := LinearMap.mem_ker.mp hc
    have hsym : ⟪T a, c⟫ = ⟪a, T c⟫ := hT a c
    have e : quad T (a + c) = quad T a := by
      rw [quad_apply, quad_apply, map_add, hTc, add_zero, inner_add_right, hsym, hTc,
        inner_zero_right, add_zero]
    rw [e]
    by_cases ha0 : a = 0
    · rw [ha0, quad_apply, map_zero, inner_zero_left]
    · exact (hUneg a ha ha0).le

end One

section Two

variable {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {T₁ : E₁ →L[ℝ] E₁} {T₂ : E₂ →L[ℝ] E₂}

/-- **Equality of the nullities.** -/
theorem finrank_ker_eq_of_retraction (h₁ : T₁.toLinearMap.IsSymmetric)
    (h₂ : T₂.toLinearMap.IsSymmetric) (L : E₁ →ₗ[ℝ] E₂) (π : E₂ →ₗ[ℝ] E₁)
    (hL : ∀ v, quad T₂ (L v) = quad T₁ v) (hπ : ∀ u, quad T₁ (π u) ≤ quad T₂ u)
    (hπL : ∀ v, π (L v) = v) (hpos : ∀ u, π u = 0 → u ≠ 0 → 0 < quad T₂ u) :
    finrank ℝ (LinearMap.ker T₂.toLinearMap) = finrank ℝ (LinearMap.ker T₁.toLinearMap) := by
  have hsig : sigNeg (quad T₁) = sigNeg (quad T₂) :=
    le_antisymm (IndexComparison.sigNeg_le_of_le _ _ L fun v => (hL v).le)
      (IndexComparison.sigNeg_le_of_le _ _ π hπ)
  have hLinj : Function.Injective L := Function.LeftInverse.injective hπL
  -- the nonpositive subspace of T₁ is carried into a nonpositive subspace of T₂
  obtain ⟨V₁, hV₁, hn₁⟩ := exists_nonpos T₁ h₁
  have hA : finrank ℝ V₁ ≤ sigNeg (quad T₂) + finrank ℝ (LinearMap.ker T₂.toLinearMap) := by
    rw [LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L hLinj V₁)]
    refine finrank_le_of_nonpos T₂ h₂ (V₁.map L) ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [hL]
    exact hn₁ v hv
  -- the nonpositive subspace of T₂ is carried injectively into a nonpositive subspace of T₁
  obtain ⟨V₂, hV₂, hn₂⟩ := exists_nonpos T₂ h₂
  have hinj : Function.Injective (π.domRestrict V₂) := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    by_contra hne
    have hu0 : (u : E₂) ≠ 0 := fun h0 => hne (Subtype.ext h0)
    have h3 := hpos (u : E₂) hu hu0
    have h4 := hn₂ (u : E₂) u.2
    linarith
  have hB : finrank ℝ V₂ ≤ sigNeg (quad T₁) + finrank ℝ (LinearMap.ker T₁.toLinearMap) := by
    have hrank : finrank ℝ (V₂.map π) = finrank ℝ V₂ := by
      rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
    rw [← hrank]
    refine finrank_le_of_nonpos T₁ h₁ (V₂.map π) ?_
    rintro _ ⟨u, hu, rfl⟩
    exact (hπ u).trans (hn₂ u hu)
  omega

end Two

end

end Finsler.NullityComparison
