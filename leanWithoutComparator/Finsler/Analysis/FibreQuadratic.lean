module

public import Finsler.Analysis.NormalExpansion

/-! Quadratic growth along the fibres of a product near a compact set of the zero section. Let Ψ
be C² on an open set 𝒪 of a product E₀ × X, X finite dimensional, K₀ a compact subset of E₀
with K₀ × {0} ⊂ 𝒪, and suppose that the fibre derivative of Ψ vanishes on the zero section.
Then there are R > 0 and C ≥ 0 with |Ψ(z, x) − Ψ(z, 0)| ≤ C ‖x‖² for z ∈ K₀ and ‖x‖ ≤ R: the
fibre derivative at (z, x) is the second fibre derivative at (z, 0) applied to x up to ‖x‖ times
a small constant (fibre expansion), the second derivative is bounded on the compact set
K₀ × {0}, and the mean value inequality along the segment from (z, 0) to (z, x) gives the bound.
-/

@[expose] public section

namespace Finsler.FibreQuadratic

open Set Metric Finsler.NormalExpansion
open scoped Topology ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {E₀ X : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [NormedAddCommGroup X]
  [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- **Quadratic growth along the fibres.** -/
theorem exists_fibre_quadratic {Ψ : E₀ × X → ℝ} {𝒪 : Set (E₀ × X)} (h𝒪 : IsOpen 𝒪)
    (hΨ : ContDiffOn ℝ 2 Ψ 𝒪) {K₀ : Set E₀} (hK : IsCompact K₀)
    (hsub : ∀ z ∈ K₀, (z, (0 : X)) ∈ 𝒪)
    (hcrit : ∀ z ∈ K₀, ∀ w : X, fderiv ℝ Ψ (z, 0) (0, w) = 0) :
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧ ∀ z ∈ K₀, ∀ x : X, ‖x‖ ≤ R →
      (z, x) ∈ 𝒪 ∧ |Ψ (z, x) - Ψ (z, 0)| ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨R, hR, hexp⟩ := exists_fibre_expansion h𝒪 hΨ hK hsub hcrit one_pos
  have h1 : ContDiffOn ℝ 1 (fderiv ℝ Ψ) 𝒪 := hΨ.fderiv_of_isOpen h𝒪 (by norm_num)
  have h2 : ContinuousOn (fderiv ℝ (fderiv ℝ Ψ)) 𝒪 :=
    (h1.fderiv_of_isOpen h𝒪 (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).continuousOn
  have h3 : ContinuousOn (fun z : E₀ => fderiv ℝ (fderiv ℝ Ψ) (z, (0 : X))) K₀ :=
    h2.comp (continuous_id.prodMk continuous_const).continuousOn fun z hz => hsub z hz
  obtain ⟨C₂, hC₂⟩ := hK.exists_bound_of_continuousOn h3
  set C : ℝ := max C₂ 0 + 1 with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨R, C, hR, hC0, fun z hz x hx => ⟨(hexp z hz x hx).1, ?_⟩⟩
  -- the fibre derivative along the segment
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ‖t • x‖ ≤ R := by
    intro t ht
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans hx
  have hbd : ∀ t ∈ Icc (0 : ℝ) 1, |fderiv ℝ Ψ (z, t • x) (0, x)| ≤ C * ‖x‖ ^ 2 := by
    intro t ht
    have htx : ‖t • x‖ ≤ ‖x‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg x) ht.2
    have he := (hexp z hz (t • x) (hseg t ht)).2 x
    have hq : |fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, t • x) (0, x)| ≤ max C₂ 0 * ‖t • x‖ * ‖x‖ := by
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, t • x) (0, x)‖
          ≤ ‖fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, t • x)‖ * ‖((0 : E₀), x)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖fderiv ℝ (fderiv ℝ Ψ) (z, 0)‖ * ‖((0 : E₀), t • x)‖) * ‖((0 : E₀), x)‖ :=
            mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ (max C₂ 0 * ‖t • x‖) * ‖x‖ := by
            rw [norm_zero_prod, norm_zero_prod]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right ((hC₂ z hz).trans (le_max_left _ _)) (norm_nonneg _))
              (norm_nonneg _)
    have habs : |fderiv ℝ Ψ (z, t • x) (0, x)| ≤
        |fderiv ℝ Ψ (z, t • x) (0, x) - fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, t • x) (0, x)| +
          |fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, t • x) (0, x)| := by
      have := abs_add_le (fderiv ℝ Ψ (z, t • x) (0, x) -
        fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, t • x) (0, x))
        (fderiv ℝ (fderiv ℝ Ψ) (z, 0) (0, t • x) (0, x))
      rwa [sub_add_cancel] at this
    have hM0 : 0 ≤ max C₂ 0 := le_max_right _ _
    have e1 : 1 * ‖t • x‖ * ‖x‖ ≤ 1 * ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htx zero_le_one) (norm_nonneg _)
    have e2 : max C₂ 0 * ‖t • x‖ * ‖x‖ ≤ max C₂ 0 * ‖x‖ * ‖x‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htx hM0) (norm_nonneg _)
    have e3 : C * ‖x‖ ^ 2 = 1 * ‖x‖ * ‖x‖ + max C₂ 0 * ‖x‖ * ‖x‖ := by
      rw [hCdef]
      ring
    rw [e3]
    linarith
  -- the mean value inequality along the segment
  have hder : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun s : ℝ => Ψ (z, s • x))
      (fderiv ℝ Ψ (z, t • x) (0, x)) (Icc 0 1) t := by
    intro t ht
    have hmem : (z, t • x) ∈ 𝒪 := (hexp z hz (t • x) (hseg t ht)).1
    have hd : HasFDerivAt Ψ (fderiv ℝ Ψ (z, t • x)) (z, t • x) :=
      (((hΨ.differentiableOn (by norm_num)) _ hmem).differentiableAt
        (h𝒪.mem_nhds hmem)).hasFDerivAt
    exact (hasDerivAt_segment z x t hd).hasDerivWithinAt
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment_01' hder
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact hbd t ⟨ht.1, ht.2.le⟩)
  rw [one_smul, zero_smul, Real.norm_eq_abs] at hmv
  exact hmv

end

end Finsler.FibreQuadratic
