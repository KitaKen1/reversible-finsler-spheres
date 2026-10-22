module

public import Finsler.Geometry.RotationNatural
public import Finsler.Geometry.LabelDeform

/-! Signed coordinate changes preserve the coefficient norms, quadratic terms and invariant cutoffs. -/

@[expose] public section

namespace Finsler.LabelSignNorms

open Finsler.RotationNatural Finsler.LabelDeform
open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonIterate
open Finsler.AmbientSymmetry

noncomputable section

variable {b p : ℕ}

theorem norm_sign (d : ℝ) (hd : d * d = 1) : ‖d‖ = 1 := by
  have h : ‖d‖ * ‖d‖ = 1 := by rw [← norm_mul, hd, norm_one]
  nlinarith [norm_nonneg d]

/-- The diagonal coefficient action preserves the product norm. -/
theorem norm_diagonal (d : Fin b → ℝ) (hd : ∀ i, d i * d i = 1) (x : Fin b → ℝ) :
    ‖diagonal d x‖ = ‖x‖ := by
  have hle : ∀ y : Fin b → ℝ, ‖diagonal d y‖ ≤ ‖y‖ := by
    intro y
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr
    intro i
    rw [diagonal_apply, norm_mul, norm_sign (d i) (hd i), one_mul]
    exact norm_le_pi_norm y i
  apply le_antisymm (hle x)
  have h := hle (diagonal d x)
  rwa [diagonal_involutive d hd] at h

theorem norm_coeffD (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : ‖coeffD d₁ d₂ ξ‖ = ‖ξ‖ := by
  change max ‖diagonal d₁ ξ.1‖ ‖diagonal d₂ ξ.2‖ = max ‖ξ.1‖ ‖ξ.2‖
  rw [norm_diagonal d₁ hd₁, norm_diagonal d₂ hd₂]

/-- The Euclidean negative square is also invariant. -/
theorem sqX_coeffD (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    sqX (coeffD d₁ d₂ ξ) = sqX ξ := by
  simp only [sqX, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change ‖d₁ i * ξ.1 i‖ ^ 2 = ‖ξ.1 i‖ ^ 2
  rw [norm_mul, norm_sign (d₁ i) (hd₁ i), one_mul]

theorem sqY_coeffD (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₂ : ∀ i, d₂ i * d₂ i = 1) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    sqY (coeffD d₁ d₂ ξ) = sqY ξ := by
  simp only [sqY, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  change ‖d₂ i * ξ.2 i‖ ^ 2 = ‖ξ.2 i‖ ^ 2
  rw [norm_mul, norm_sign (d₂ i) (hd₂ i), one_mul]

theorem sqE_coeffD (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) : sqE (coeffD d₁ d₂ ξ) = sqE ξ := by
  rw [sqE, sqE, sqX_coeffD d₁ d₂ hd₁, sqY_coeffD d₁ d₂ hd₂]

/-- An invariant root cutoff gives an invariant actual deformation cutoff. -/
theorem cutoff_chartR {n m N : ℕ} (s : ZMod (m * N))
    (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (χ₀ : (ZMod N → Ambient n) → ℝ)
    (hχ : ∀ z, χ₀ (rotA N (red m N s) z) = χ₀ z) (r lam : ℝ)
    (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) :
    cutoff χ₀ r lam (chartR m N s d₁ d₂ q) = cutoff χ₀ r lam q := by
  change χ₀ (rotA N (red m N s) q.1) * Finsler.LogCutoff.logCut r lam (sqE (coeffD d₁ d₂ q.2)) = _
  rw [hχ, sqE_coeffD d₁ d₂ hd₁ hd₂]
  rfl

end

end Finsler.LabelSignNorms
