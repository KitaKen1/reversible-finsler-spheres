module

public import Finsler.Geometry.CircleFixedShift
public import Finsler.Topology.PacketSupport

/-! The actual signed fixed shift centers a product support interval at the half-iterate index.
Actual label/model and trapping comparisons are still needed to apply this to label groups. -/

@[expose] public section

namespace Finsler.CircleFixedWindow

open Set Finsler.Geometry Finsler.GeodesicFrames Finsler.CircleFrameField
open Finsler.SphereGeometry Finsler.PolygonIterate Finsler.SymmetricBlocks
open Finsler.CurveEquivFrames Finsler.AmbientNormalIndex Finsler.CircleHalfRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem exists_window {n : ℕ} {F : ReversibleMetric n}
    (g : Finsler.Geodesics.ClosedGeodesic F) (m s j : ℕ) [NeZero m] [NeZero s] [NeZero j]
    (hms : m * s = 2 * j) (A : ℕ) (hA : (iterData g).I s ≤ A) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N] {b p : ℕ}
      (S₁ : SignedFrameField g s m N 1 b) (_S₂ : SignedFrameField g s m N (-1) p)
      (_ψ : normal (rotL (n := n) m (s * (2 * N))) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ)),
      ∀ D q : ℕ, D ≤ A → (A : ℝ) < |(q : ℝ) - (iterData g).I j| →
        q < Fintype.card {i : Fin b // S₁.d i = 1} ∨
          Fintype.card {i : Fin b // S₁.d i = 1} + D ≤ q := by
  obtain ⟨N₀, hN₀⟩ := Finsler.CircleFixedShift.exists_shift_bounds g m s j hms
  refine ⟨N₀, fun N hN _ b p S₁ S₂ ψ D q hD hq => ?_⟩
  obtain ⟨hlo, hhi⟩ := hN₀ N hN S₁ S₂ ψ
  let k := Fintype.card {i : Fin b // S₁.d i = 1}
  have hk : k = (iterData g).I j - ((iterData g).I j - k) := by
    dsimp [k]
    omega
  have hR : (iterData g).I j - k ≤ A := by
    dsimp [k]
    omega
  exact Finsler.PacketSupport.outside_shifted_interval hk hR hD hq

end

end Finsler.CircleFixedWindow

