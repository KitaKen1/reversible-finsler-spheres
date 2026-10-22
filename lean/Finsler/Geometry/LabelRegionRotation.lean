module

public import Finsler.Geometry.CircleLabelFields
public import Finsler.Geometry.LabelRegions

/-! Rotation-invariant label cylinders and compact tubes from adapted signed frames. -/

@[expose] public section

namespace Finsler.LabelRegionRotation

open Set Metric Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonIterate
open Finsler.AmbientNormalIndex Finsler.AmbientSymmetry Finsler.NormalFamily Finsler.SymmetricBlocks
open Finsler.FrameCoordinates Finsler.FrameInverse Finsler.RotationNatural
open Finsler.LabelSignNorms Finsler.LabelRegions

noncomputable section
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 600000

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (a : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
  (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
  (h₁ : ∀ z i, G₁ (rotA N (red m N a) z) i = d₁ i • rotV m N a (G₁ z i))
  (h₂ : ∀ z i, G₂ (rotA N (red m N a) z) i = d₂ i • rotV m N a (G₂ z i))

omit [NeZero m] [NeZero N] in
theorem closure_rotA {Z : Set (ZMod N → Ambient n)}
    (hZ : ∀ z ∈ Z, rotA N (red m N a) z ∈ Z)
    {z : ZMod N → Ambient n} (hz : z ∈ closure Z) :
    rotA N (red m N a) z ∈ closure Z := by
  have hs : Z ⊆ (rotA N (red m N a)) ⁻¹' closure Z :=
    fun x hx => subset_closure (hZ x hx)
  exact closure_minimal hs (isClosed_closure.preimage (rotA N (red m N a)).continuous) hz

include hd₁ hd₂ h₁ h₂

theorem region_rotA_mem
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    {Z : Set (ZMod N → Ambient n)} {ρ : ℝ}
    (hZ : ∀ z ∈ Z, rotA N (red m N a) z ∈ Z)
    (hu : ∀ z ∈ Z, IsUnit (matA m N G₁ G₂ ψ z))
    {Q : ZMod (m * N) → Ambient n} (hQ : Q ∈ region m N G₁ G₂ ψ Z ρ) :
    rotA (m * N) a Q ∈ region m N G₁ G₂ ψ Z ρ := by
  obtain ⟨hqu, hqz, hqξ, hqn⟩ := hQ
  have hqu' := hu _ (hZ _ hqz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [zOf_rotA]
    exact hqu'
  · rw [zOf_rotA]
    exact hZ _ hqz
  · rw [xiOf_rotA m N G₁ G₂ ψ a d₁ d₂ hd₁ hd₂ hqu hqu' (h₁ _) (h₂ _),
      norm_coeffD d₁ d₂ hd₁ hd₂]
    exact hqξ
  · intro j
    exact hqn (j + a)

theorem tube_rotA_mem {Z : Set (ZMod N → Ambient n)} {ρ : ℝ}
    (hZ : ∀ z ∈ Z, rotA N (red m N a) z ∈ Z)
    {Q : ZMod (m * N) → Ambient n} (hQ : Q ∈ tube m N G₁ G₂ Z ρ) :
    rotA (m * N) a Q ∈ tube m N G₁ G₂ Z ρ := by
  obtain ⟨⟨z, ξ⟩, ⟨hz, hξ⟩, rfl⟩ := hQ
  refine ⟨chartR m N a d₁ d₂ (z, ξ), ⟨closure_rotA m N a hZ hz, ?_⟩, ?_⟩
  · change coeffD d₁ d₂ ξ ∈ closedBall 0 ρ
    rw [mem_closedBall_zero_iff, norm_coeffD d₁ d₂ hd₁ hd₂]
    exact mem_closedBall_zero_iff.mp hξ
  · exact coord_chartR m N G₁ G₂ a d₁ d₂ hd₁ hd₂ z (h₁ z) (h₂ z) ξ

theorem region_half_iff
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (ha : a + a = 0) {Z : Set (ZMod N → Ambient n)} {ρ : ℝ}
    (hZ : ∀ z ∈ Z, rotA N (red m N a) z ∈ Z)
    (hu : ∀ z ∈ Z, IsUnit (matA m N G₁ G₂ ψ z))
    (Q : ZMod (m * N) → Ambient n) :
    rotA (m * N) a Q ∈ region m N G₁ G₂ ψ Z ρ ↔ Q ∈ region m N G₁ G₂ ψ Z ρ := by
  constructor
  · intro h
    have ht := region_rotA_mem m N G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ ψ hZ hu h
    rwa [rotA_rotA, ha, rotA_zero] at ht
  · exact region_rotA_mem m N G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ ψ hZ hu

theorem tube_half_iff (ha : a + a = 0) {Z : Set (ZMod N → Ambient n)} {ρ : ℝ}
    (hZ : ∀ z ∈ Z, rotA N (red m N a) z ∈ Z)
    (Q : ZMod (m * N) → Ambient n) :
    rotA (m * N) a Q ∈ tube m N G₁ G₂ Z ρ ↔ Q ∈ tube m N G₁ G₂ Z ρ := by
  constructor
  · intro h
    have ht := tube_rotA_mem m N G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ hZ h
    rwa [rotA_rotA, ha, rotA_zero] at ht
  · exact tube_rotA_mem m N G₁ G₂ a d₁ d₂ hd₁ hd₂ h₁ h₂ hZ

end

end Finsler.LabelRegionRotation
