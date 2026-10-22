module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Comparison of the kernels of two symmetric bilinear functions related by a section and a
retraction. Let β₁ and β₂ be symmetric bilinear functions on real vector spaces E₁ and E₂, L a
linear map from E₁ to E₂ with β₂(L v, L v) = β₁(v, v), and π a linear map from E₂ to E₁ with
π L = 1 and β₁(π u, π u) ≤ β₂(u, u). Then β₂(L v, L w) = β₁(v, w); L maps the kernel of β₁ into
the kernel of β₂, and π maps the kernel of β₂ into the kernel of β₁: both follow from the fact
that a real affine function which is nonnegative everywhere is constant. If moreover β₂ is
positive at the nonzero vectors of the kernel of π, the two kernels have the same dimension.
This is the linear algebra of the nullity of a function which is the partial minimum of another
one, for bilinear functions on spaces without an inner product. -/

@[expose] public section

namespace Finsler.KernelComparison

open Module

noncomputable section

/-- A real affine function which is nonnegative everywhere has slope zero. -/
theorem eq_zero_of_affine_nonneg {a c : ℝ} (h : ∀ t : ℝ, 0 ≤ a + t * c) : c = 0 := by
  by_contra hc
  have h1 := h (-(a + 1) / c)
  rw [div_mul_cancel₀ _ hc] at h1
  linarith

variable {E₁ E₂ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [AddCommGroup E₂] [Module ℝ E₂]
  {β₁ : E₁ →ₗ[ℝ] E₁ →ₗ[ℝ] ℝ} {β₂ : E₂ →ₗ[ℝ] E₂ →ₗ[ℝ] ℝ} {L : E₁ →ₗ[ℝ] E₂} {π : E₂ →ₗ[ℝ] E₁}

/-- The section preserves the bilinear functions if it preserves the quadratic forms. -/
theorem form_comp_eq (hs₁ : ∀ v w, β₁ v w = β₁ w v) (hs₂ : ∀ v w, β₂ v w = β₂ w v)
    (hL : ∀ v, β₂ (L v) (L v) = β₁ v v) (v w : E₁) : β₂ (L v) (L w) = β₁ v w := by
  have h := hL (v + w)
  simp only [map_add, LinearMap.add_apply] at h
  rw [hL v, hL w, hs₂ (L w) (L v), hs₁ w v] at h
  linarith

/-- The section maps the kernel of β₁ into the kernel of β₂. -/
theorem ker_map (hs₁ : ∀ v w, β₁ v w = β₁ w v) (hs₂ : ∀ v w, β₂ v w = β₂ w v)
    (hπL : ∀ v, π (L v) = v) (hL : ∀ v, β₂ (L v) (L v) = β₁ v v)
    (hπ : ∀ u, β₁ (π u) (π u) ≤ β₂ u u) {v : E₁} (hv : ∀ w, β₁ v w = 0) (u : E₂) :
    β₂ (L v) u = 0 := by
  have h1 : β₂ (L v) (L (π u)) = 0 := by
    rw [form_comp_eq hs₁ hs₂ hL]
    exact hv _
  have hr : π (u - L (π u)) = 0 := by rw [map_sub, hπL, sub_self]
  have h2 : 2 * β₂ (u - L (π u)) (L v) = 0 := by
    refine eq_zero_of_affine_nonneg (a := β₂ (u - L (π u)) (u - L (π u))) fun t => ?_
    have h3 := hπ (u - L (π u) + t • L v)
    have h4 : π (u - L (π u) + t • L v) = t • v := by
      rw [map_add, hr, zero_add, map_smul, hπL]
    have h5 : β₁ (t • v) (t • v) = 0 := by
      simp only [map_smul, LinearMap.smul_apply, hv, smul_zero]
    have h6 : β₂ (u - L (π u) + t • L v) (u - L (π u) + t • L v) =
        β₂ (u - L (π u)) (u - L (π u)) + t * (2 * β₂ (u - L (π u)) (L v)) := by
      have h7 : β₂ (L v) (L v) = 0 := by rw [hL]; exact hv v
      have h8 : β₂ (L v) (u - L (π u)) = β₂ (u - L (π u)) (L v) := hs₂ _ _
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h7,
        h8]
      ring
    rw [h4, h5, h6] at h3
    exact h3
  have h9 : β₂ (L v) (u - L (π u)) = 0 := by
    rw [hs₂]
    linarith
  have h10 : u = (u - L (π u)) + L (π u) := by abel
  rw [h10, map_add, h9, h1, add_zero]

/-- The retraction maps the kernel of β₂ into the kernel of β₁. -/
theorem ker_comap (hs₁ : ∀ v w, β₁ v w = β₁ w v) (hs₂ : ∀ v w, β₂ v w = β₂ w v)
    (hπL : ∀ v, π (L v) = v) (hL : ∀ v, β₂ (L v) (L v) = β₁ v v)
    (hπ : ∀ u, β₁ (π u) (π u) ≤ β₂ u u) {u : E₂} (hu : ∀ x, β₂ u x = 0) (w : E₁) :
    β₁ (π u) w = 0 := by
  have h2 : -(2 * β₁ (π u) w) = 0 := by
    refine eq_zero_of_affine_nonneg (a := -β₁ (π u) (π u)) fun t => ?_
    have h3 := hπ (u + t • L w)
    have h4 : π (u + t • L w) = π u + t • w := by rw [map_add, map_smul, hπL]
    have h5 : β₂ (u + t • L w) (u + t • L w) = t ^ 2 * β₁ w w := by
      have h6 : β₂ (L w) u = 0 := by rw [hs₂]; exact hu _
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hu,
        h6, hL]
      ring
    have h7 : β₁ (π u + t • w) (π u + t • w) =
        β₁ (π u) (π u) + t * (2 * β₁ (π u) w) + t ^ 2 * β₁ w w := by
      have h8 : β₁ w (π u) = β₁ (π u) w := hs₁ _ _
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h8]
      ring
    rw [h4, h5, h7] at h3
    linarith
  linarith

variable [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]

/-- If the second function is positive at the nonzero vectors of the kernel of the retraction,
the kernels of the two bilinear functions have the same dimension. -/
theorem finrank_ker_eq (hs₁ : ∀ v w, β₁ v w = β₁ w v) (hs₂ : ∀ v w, β₂ v w = β₂ w v)
    (hπL : ∀ v, π (L v) = v) (hL : ∀ v, β₂ (L v) (L v) = β₁ v v)
    (hπ : ∀ u, β₁ (π u) (π u) ≤ β₂ u u) (hpos : ∀ u, π u = 0 → u ≠ 0 → 0 < β₂ u u) :
    finrank ℝ (LinearMap.ker β₂) = finrank ℝ (LinearMap.ker β₁) := by
  have hLinj : Function.Injective L := fun v w h => by rw [← hπL v, ← hπL w, h]
  refine le_antisymm ?_ ?_
  · -- the retraction is injective on the kernel of β₂
    have hmap : (LinearMap.ker β₂).map π ≤ LinearMap.ker β₁ := by
      rintro _ ⟨u, hu, rfl⟩
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun w => ?_
      have hu' : ∀ x, β₂ u x = 0 := fun x => by
        rw [LinearMap.mem_ker.mp hu]
        rfl
      exact ker_comap hs₁ hs₂ hπL hL hπ hu' w
    have hinj : Function.Injective (π.domRestrict (LinearMap.ker β₂)) := by
      rw [injective_iff_map_eq_zero]
      intro u hu
      by_contra hne
      have hne' : (u : E₂) ≠ 0 := fun h => hne (Subtype.ext h)
      have h1 := hpos (u : E₂) hu hne'
      have h2 : β₂ (u : E₂) (u : E₂) = 0 := by
        rw [LinearMap.mem_ker.mp u.2]
        rfl
      linarith
    have h3 : finrank ℝ (LinearMap.ker β₂) ≤ finrank ℝ ((LinearMap.ker β₂).map π) := by
      have h4 := LinearMap.finrank_range_of_inj hinj
      rw [LinearMap.range_domRestrict] at h4
      exact h4.ge
    exact h3.trans (Submodule.finrank_mono hmap)
  · have hmap : (LinearMap.ker β₁).map L ≤ LinearMap.ker β₂ := by
      rintro _ ⟨v, hv, rfl⟩
      rw [LinearMap.mem_ker]
      refine LinearMap.ext fun u => ?_
      have hv' : ∀ w, β₁ v w = 0 := fun w => by
        rw [LinearMap.mem_ker.mp hv]
        rfl
      exact ker_map hs₁ hs₂ hπL hL hπ hv' u
    have hinj : Function.Injective (L.domRestrict (LinearMap.ker β₁)) :=
      fun v w h => Subtype.ext (hLinj h)
    have h3 : finrank ℝ (LinearMap.ker β₁) ≤ finrank ℝ ((LinearMap.ker β₁).map L) := by
      have h4 := LinearMap.finrank_range_of_inj hinj
      rw [LinearMap.range_domRestrict] at h4
      exact h4.ge
    exact h3.trans (Submodule.finrank_mono hmap)

end

end Finsler.KernelComparison
