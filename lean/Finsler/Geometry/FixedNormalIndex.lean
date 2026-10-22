module

public import Finsler.Analysis.SignedFrameIndex

/-! Fixed signed-coordinate, energy, flow and index comparison. -/

@[expose] public section

namespace Finsler.FixedNormalIndex

open Module QuadraticMap Set Finsler.SphereGeometry Finsler.Geometry
open Finsler.AmbientNormalIndex Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.RotationNatural Finsler.PolygonIterate Finsler.SymmetricBlocks
open Finsler.NormalFamily Finsler.DefiniteFrames Finsler.AmbientSymmetry
open Finsler.InvolutionIndex

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n m N b p : ℕ} [NeZero m] [NeZero N]
variable (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
variable (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
variable (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
variable (z : ZMod N → Ambient n)

def normalFrameL : ((Fin b → ℝ) × (Fin p → ℝ)) →ₗ[ℝ] normal (rotL (n := n) m N) m :=
  (fibreL m N G₁ G₂ z).toLinearMap.codRestrict _ (fibreL_mem m N G₁ G₂ z)

theorem normalFrameL_eq_comb (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    normalFrameL G₁ G₂ z ξ = comb (G₁ z) ξ.1 + comb (G₂ z) ξ.2 := by
  apply Subtype.ext
  exact fibreL_apply m N G₁ G₂ z ξ

theorem bijective_normalFrameL (hz : IsUnit (matA m N G₁ G₂ ψ z)) :
    Function.Bijective (normalFrameL G₁ G₂ z) := by
  have hM : Function.Bijective (matA m N G₁ G₂ ψ z) := by
    obtain ⟨u, hu⟩ := hz
    rw [← hu]
    exact ((ContinuousLinearEquiv.unitsEquiv ℝ _) u).bijective
  have hc : ∀ ξ, ψ (normalFrameL G₁ G₂ z ξ) = matA m N G₁ G₂ ψ z ξ := by
    intro ξ
    exact (matA_apply m N G₁ G₂ ψ z ξ).symm
  constructor
  · intro ξ η h
    apply hM.1
    rw [← hc, ← hc, h]
  · intro v
    obtain ⟨ξ, hξ⟩ := hM.2 (ψ v)
    exact ⟨ξ, ψ.injective ((hc ξ).trans hξ)⟩

def normalFrameEquiv (hz : IsUnit (matA m N G₁ G₂ ψ z)) :
    ((Fin b → ℝ) × (Fin p → ℝ)) ≃ₗ[ℝ] normal (rotL (n := n) m N) m :=
  LinearEquiv.ofBijective (normalFrameL G₁ G₂ z) (bijective_normalFrameL G₁ G₂ ψ z hz)

theorem normalFrameEquiv_eq_comb (hz : IsUnit (matA m N G₁ G₂ ψ z))
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    normalFrameEquiv G₁ G₂ ψ z hz ξ = comb (G₁ z) ξ.1 + comb (G₂ z) ξ.2 :=
  normalFrameL_eq_comb G₁ G₂ z ξ

theorem normalFrameEquiv_signed (hz : IsUnit (matA m N G₁ G₂ ψ z))
    (s : ZMod (m * N)) (hfix : rotA N (red m N s) z = z)
    (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    rotV m N s (normalFrameEquiv G₁ G₂ ψ z hz ξ) =
      normalFrameEquiv G₁ G₂ ψ z hz (coeffD d₁ d₂ ξ) := by
  rw [normalFrameEquiv_eq_comb, map_add, normalFrameEquiv_eq_comb]
  apply congrArg₂ (fun x y => x + y)
  · have h := comb_rotV m N G₁ s d₁ z h₁ (diagonal d₁ ξ.1)
    rw [hfix, diagonal_involutive d₁ hd₁] at h
    exact h.symm
  · have h := comb_rotV m N G₂ s d₂ z h₂ (diagonal d₂ ξ.2)
    rw [hfix, diagonal_involutive d₂ hd₂] at h
    exact h.symm

include ψ in
theorem sigNeg_fixed_normal
    (β : normal (rotL (n := n) m N) m →ₗ[ℝ] normal (rotL (n := n) m N) m →ₗ[ℝ] ℝ)
    (hneg : Neg β (G₁ z)) (hpos : Neg (-β) (G₂ z))
    (s : ZMod (m * N)) (hfix : rotA N (red m N s) z = z)
    (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i)) :
    sigNeg (LinearMap.BilinMap.toQuadraticMap
      (eigenForm (rotV m N s).toLinearMap 1 β)) = Fintype.card {i : Fin b // d₁ i = 1} := by
  let hz := isUnit_matA m N G₁ G₂ ψ hneg hpos
  apply SignedFrameIndex.sigNeg_fixed (rotV m N s).toLinearMap
    (normalFrameEquiv G₁ G₂ ψ z hz) d₁ d₂
    (normalFrameEquiv_signed G₁ G₂ ψ z hz s hfix d₁ d₂ hd₁ hd₂ h₁ h₂) β
  · intro x hx
    have h0 : comb (G₂ z) (0 : Fin p → ℝ) = 0 := by simp [comb]
    rw [normalFrameEquiv_eq_comb, h0, add_zero]
    exact hneg x hx
  · intro y hy
    have h0 : comb (G₁ z) (0 : Fin b → ℝ) = 0 := by simp [comb]
    rw [normalFrameEquiv_eq_comb, h0, zero_add]
    have h := hpos y hy
    change -(β (comb (G₂ z) y) (comb (G₂ z) y)) < 0 at h
    linarith

end

end Finsler.FixedNormalIndex
