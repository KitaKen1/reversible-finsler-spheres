module

public import Finsler.Geometry.LabelTransport

/-! The actual deformed energy equals the signed product model on a small label.
All coordinates are fixed explicitly before applying the cutoff identity. -/

@[expose] public section

namespace Finsler.LabelModelAgreement

open Set Finsler.Geometry Finsler.SphereGeometry Finsler.AmbientPenalty
open Finsler.PolygonIterate Finsler.SymmetricBlocks Finsler.AmbientNormalIndex
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.LabelDeform Finsler.LabelAmbient Finsler.LabelTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem on_label {n m N b p : ℕ} [NeZero m] [NeZero N]
    (F : ReversibleMetric n)
    (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
    (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (χ : (ZMod N → Ambient n) → ℝ) {r lam ρ : ℝ} (hr : r ≠ 0) (hlam : 0 < lam)
    {Z : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)}
    (hχ : ∀ z ∈ Z, χ z = 1) (hρr : 2 * ρ ^ 2 ≤ r ^ 2) :
    ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z U ρ,
      gDef m N F G₁ G₂ ψ χ r lam Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1) := by
  rintro Q ⟨hu, hz, hx, hy, _⟩
  apply gDef_of_cutoff_eq_one m N F G₁ G₂ ψ hu
  apply cutoff_eq_one (χ₀ := χ) (q := cOf m N G₁ G₂ ψ Q.1) hr hlam
  · exact hχ _ hz
  · change ‖eucX (xiOf m N G₁ G₂ ψ Q.1)‖ ^ 2 +
      ‖eucY (xiOf m N G₁ G₂ ψ Q.1)‖ ^ 2 ≤ r ^ 2
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hx.le 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hy.le 2
    linarith

end

end Finsler.LabelModelAgreement
