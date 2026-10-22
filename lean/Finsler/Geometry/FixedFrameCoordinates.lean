module

public import Finsler.Geometry.RotationNatural

/-! characterize fixed points in
the actual signed frame coordinates using their known inverse. The fixed diagonal coefficient
space is explicitly the space of coordinates whose sign is +1. -/

@[expose] public section

namespace Finsler.FixedFrameCoordinates

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientSymmetry
open Finsler.AmbientNormalIndex Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.RotationNatural Finsler.PolygonIterate Finsler.SymmetricBlocks Finsler.NormalFamily

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem diagonal_fixed_iff {b : ℕ} (d : Fin b → ℝ) (x : Fin b → ℝ) :
    diagonal d x = x ↔ ∀ i, d i ≠ 1 → x i = 0 := by
  constructor
  · intro h i hi
    have hmul : (d i - 1) * x i = 0 := by
      have h' := congrFun h i
      change d i * x i = x i at h'
      linarith
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hi)
  · intro h
    funext i
    by_cases hi : d i = 1
    · simp only [diagonal_apply, hi, one_mul]
    · rw [diagonal_apply, h i hi, mul_zero]

theorem coeffD_fixed_iff {b p : ℕ} (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    coeffD d₁ d₂ ξ = ξ ↔
      (∀ i, d₁ i ≠ 1 → ξ.1 i = 0) ∧ (∀ i, d₂ i ≠ 1 → ξ.2 i = 0) := by
  change (diagonal d₁ ξ.1, diagonal d₂ ξ.2) = ξ ↔ _
  rw [Prod.mk.injEq, diagonal_fixed_iff, diagonal_fixed_iff]

def fixedCoeff {b : ℕ} (d : Fin b → ℝ) : Submodule ℝ (Fin b → ℝ) where
  carrier := {x | diagonal d x = x}
  zero_mem' := map_zero _
  add_mem' {x y} hx hy := by
    change diagonal d x = x at hx
    change diagonal d y = y at hy
    change diagonal d (x + y) = x + y
    rw [map_add, hx, hy]
  smul_mem' c x hx := by
    change diagonal d x = x at hx
    change diagonal d (c • x) = c • x
    rw [map_smul, hx]

def fixedCoeffEquiv {b : ℕ} (d : Fin b → ℝ) :
    fixedCoeff d ≃ₗ[ℝ] ({i : Fin b // d i = 1} → ℝ) where
  toFun x i := x.1 i.1
  invFun y := ⟨fun i => if h : d i = 1 then y ⟨i, h⟩ else 0, by
    change diagonal d (fun i => if h : d i = 1 then y ⟨i, h⟩ else 0) = _
    exact (diagonal_fixed_iff d _).mpr (fun i hi => dite_eq_right hi)⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    change (if h : d i = 1 then x.1 i else 0) = x.1 i
    by_cases hi : d i = 1
    · exact dite_eq_left hi
    · have hx := x.2
      change diagonal d x.1 = x.1 at hx
      rw [dite_eq_right hi, (diagonal_fixed_iff d x.1).mp hx i hi]
  right_inv y := by
    funext i
    change (if h : d i.1 = 1 then y ⟨i.1, h⟩ else 0) = y i
    exact dite_eq_left i.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_fixedCoeff {b : ℕ} (d : Fin b → ℝ) :
    Module.finrank ℝ (fixedCoeff d) = Fintype.card {i : Fin b // d i = 1} := by
  classical
  rw [(fixedCoeffEquiv d).finrank_eq]
  simp

variable {n m N b p : ℕ} [NeZero m] [NeZero N]
variable (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
variable (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
variable (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))

/-- The known inverse of the same signed chart gives its fixed-point condition. -/
theorem fixed_iff (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    {Q : ZMod (m * N) → Ambient n}
    (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)))
    (h₁ : ∀ i, G₁ (rotA N (red m N s) (zOf m N Q)) i =
      d₁ i • rotV m N s (G₁ (zOf m N Q) i))
    (h₂ : ∀ i, G₂ (rotA N (red m N s) (zOf m N Q)) i =
      d₂ i • rotV m N s (G₂ (zOf m N Q) i)) :
    rotA (m * N) s Q = Q ↔
      rotA N (red m N s) (zOf m N Q) = zOf m N Q ∧
        coeffD d₁ d₂ (xiOf m N G₁ G₂ ψ Q) = xiOf m N G₁ G₂ ψ Q := by
  constructor
  · intro hfix
    have hz := zOf_rotA m N s Q
    rw [hfix] at hz
    have hQ' : IsUnit (matA m N G₁ G₂ ψ (rotA N (red m N s) (zOf m N Q))) := by
      rw [hz.symm]
      exact hQ
    have hξ := xiOf_rotA m N G₁ G₂ ψ s d₁ d₂ hd₁ hd₂ hQ hQ' h₁ h₂
    rw [hfix] at hξ
    exact ⟨hz.symm, hξ.symm⟩
  · rintro ⟨hz, hξ⟩
    have hc := coord_chartR m N G₁ G₂ s d₁ d₂ hd₁ hd₂ (zOf m N Q) h₁ h₂
      (xiOf m N G₁ G₂ ψ Q)
    change coord m N G₁ G₂ (rotA N (red m N s) (zOf m N Q),
      coeffD d₁ d₂ (xiOf m N G₁ G₂ ψ Q)) = _ at hc
    rw [hz, hξ, coord_inverse m N G₁ G₂ ψ hQ] at hc
    exact hc.symm

end

end Finsler.FixedFrameCoordinates

