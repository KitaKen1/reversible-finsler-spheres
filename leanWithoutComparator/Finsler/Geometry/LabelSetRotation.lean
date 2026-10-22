module

public import Finsler.Geometry.CircleLabelFields
public import Finsler.Geometry.LabelTransport

/-! The actual label sets are invariant under the involutive rotation for adapted signed frames and invariant root and ambient regions. -/

@[expose] public section

namespace Finsler.LabelSetRotation

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonIterate
open Finsler.AmbientPenalty Finsler.AmbientSymmetry Finsler.NormalFamily Finsler.SymmetricBlocks
open Finsler.AmbientNormalIndex Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.RotationNatural Finsler.LabelSignNorms Finsler.LabelDeform Finsler.LabelTransport

noncomputable section
set_option maxSynthPendingDepth 3

variable {b p : ℕ}

theorem norm_eucX_coeffD (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    ‖eucX (coeffD d₁ d₂ ξ)‖ = ‖eucX ξ‖ := by
  have h := sqX_coeffD d₁ d₂ hd₁ ξ
  change ‖eucX (coeffD d₁ d₂ ξ)‖ ^ 2 = ‖eucX ξ‖ ^ 2 at h
  nlinarith [norm_nonneg (eucX (coeffD d₁ d₂ ξ)), norm_nonneg (eucX ξ)]

theorem norm_eucY_coeffD (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₂ : ∀ i, d₂ i * d₂ i = 1) (ξ : (Fin b → ℝ) × (Fin p → ℝ)) :
    ‖eucY (coeffD d₁ d₂ ξ)‖ = ‖eucY ξ‖ := by
  have h := sqY_coeffD d₁ d₂ hd₂ ξ
  change ‖eucY (coeffD d₁ d₂ ξ)‖ ^ 2 = ‖eucY ξ‖ ^ 2 at h
  nlinarith [norm_nonneg (eucY (coeffD d₁ d₂ ξ)), norm_nonneg (eucY ξ)]

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N]

def rotOm (a : ZMod (m * N)) (Q : Om n (m * N)) : Om n (m * N) :=
  ⟨rotA (m * N) a Q.1, fun j => Q.2 (j + a)⟩

variable
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (a : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
  (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
  (h₁ : ∀ z i, G₁ (rotA N (red m N a) z) i = d₁ i • rotV m N a (G₁ z i))
  (h₂ : ∀ z i, G₂ (rotA N (red m N a) z) i = d₂ i • rotV m N a (G₂ z i))

include hd₁ hd₂ h₁ h₂

theorem labelSetA_rotA_mem
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    {Z : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}
    (hZ : ∀ z ∈ Z, rotA N (red m N a) z ∈ Z)
    (hU : ∀ Q ∈ U, rotA (m * N) a Q ∈ U)
    (hu : ∀ z ∈ Z, IsUnit (matA m N G₁ G₂ ψ z))
    {Q : Om n (m * N)} (hQ : Q ∈ labelSetA m N G₁ G₂ ψ Z U ρ) :
    rotOm m N a Q ∈ labelSetA m N G₁ G₂ ψ Z U ρ := by
  obtain ⟨hqu, hqz, hqx, hqy, hqU⟩ := hQ
  have hqu' := hu _ (hZ _ hqz)
  have hξ := xiOf_rotA m N G₁ G₂ ψ a d₁ d₂ hd₁ hd₂ hqu hqu' (h₁ _) (h₂ _)
  refine ⟨?_, ?_, ?_, ?_, hU _ hqU⟩
  · change IsUnit (matA m N G₁ G₂ ψ (zOf m N (rotA (m * N) a Q.1)))
    rw [zOf_rotA]
    exact hqu'
  · change zOf m N (rotA (m * N) a Q.1) ∈ Z
    rw [zOf_rotA]
    exact hZ _ hqz
  · change ‖eucX (xiOf m N G₁ G₂ ψ (rotA (m * N) a Q.1))‖ < ρ
    rw [hξ, norm_eucX_coeffD d₁ d₂ hd₁]
    exact hqx
  · change ‖eucY (xiOf m N G₁ G₂ ψ (rotA (m * N) a Q.1))‖ < ρ
    rw [hξ, norm_eucY_coeffD d₁ d₂ hd₂]
    exact hqy

theorem labelSetA_half_iff
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (ha : a + a = 0) {Z : Set (ZMod N → Ambient n)}
    {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}
    (hZ : ∀ z ∈ Z, rotA N (red m N a) z ∈ Z)
    (hU : ∀ Q ∈ U, rotA (m * N) a Q ∈ U)
    (hu : ∀ z ∈ Z, IsUnit (matA m N G₁ G₂ ψ z)) (Q : Om n (m * N)) :
    rotOm m N a Q ∈ labelSetA m N G₁ G₂ ψ Z U ρ ↔ Q ∈ labelSetA m N G₁ G₂ ψ Z U ρ := by
  constructor
  · intro h
    have ht := labelSetA_rotA_mem m N G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ ψ hZ hU hu h
    have he : rotOm m N a (rotOm m N a Q) = Q := by
      apply Subtype.ext
      change rotA (m * N) a (rotA (m * N) a Q.1) = Q.1
      rw [rotA_rotA, ha, rotA_zero]
    rwa [he] at ht
  · exact labelSetA_rotA_mem m N G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ ψ hZ hU hu

end

end Finsler.LabelSetRotation
