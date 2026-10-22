module

public import Finsler.Geometry.LabelSignNorms
public import Finsler.Geometry.LabelAmbient

/-! Conditional rotation naturality of label charts, deformation and ambient label functions. -/

@[expose] public section

namespace Finsler.LabelRotation

open Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonIterate
open Finsler.AmbientPenalty Finsler.AmbientSymmetry Finsler.NormalFamily
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.FrameCoordinates
open Finsler.FrameInverse Finsler.RotationNatural Finsler.LabelDeform Finsler.LabelAmbient
open Finsler.LabelSignNorms

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
  (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
  (h₁ : ∀ z i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
  (h₂ : ∀ z i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))

include hd₁ hd₂ h₁ h₂

theorem psi_chartR (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) :
    psi m N F G₁ G₂ (chartR m N s d₁ d₂ q) = psi m N F G₁ G₂ q := by
  change pen F (m * N) 1 (coord m N G₁ G₂ (chartR m N s d₁ d₂ q)) = _
  rw [coord_chartR m N G₁ G₂ s d₁ d₂ hd₁ hd₂ q.1 (h₁ q.1) (h₂ q.1) q.2,
    pen_rotA]
  rfl

theorem model_chartR (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) :
    model m N F G₁ G₂ (chartR m N s d₁ d₂ q) = model m N F G₁ G₂ q := by
  have hbase : psi m N F G₁ G₂ (rotA N (red m N s) q.1, 0) =
      psi m N F G₁ G₂ (q.1, 0) := by
    simpa only [chartR, ContinuousLinearMap.coe_prodMap', Prod.map_apply, map_zero] using
      psi_chartR m N F G₁ G₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ (q.1, 0)
  change psi m N F G₁ G₂ (rotA N (red m N s) q.1, 0) - sqX (coeffD d₁ d₂ q.2) +
    sqY (coeffD d₁ d₂ q.2) = _
  rw [hbase, sqX_coeffD d₁ d₂ hd₁, sqY_coeffD d₁ d₂ hd₂]
  rfl

theorem deformG_chartR (χ₀ : (ZMod N → Ambient n) → ℝ)
    (hχ : ∀ z, χ₀ (rotA N (red m N s) z) = χ₀ z) (r lam : ℝ)
    (q : (ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) :
    deformG m N F G₁ G₂ χ₀ r lam (chartR m N s d₁ d₂ q) =
      deformG m N F G₁ G₂ χ₀ r lam q := by
  unfold deformG
  rw [psi_chartR m N F G₁ G₂ s d₁ d₂ hd₁ hd₂ h₁ h₂,
    cutoff_chartR s d₁ d₂ hd₁ hd₂ χ₀ hχ,
    model_chartR m N F G₁ G₂ s d₁ d₂ hd₁ hd₂ h₁ h₂]

variable (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  {Q : ZMod (m * N) → Ambient n}
  (hQ : IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)))
  (hQ' : IsUnit (matA m N G₁ G₂ ψ (rotA N (red m N s) (zOf m N Q))))

include hQ hQ'

theorem cOf_rotA : cOf m N G₁ G₂ ψ (rotA (m * N) s Q) =
    chartR m N s d₁ d₂ (cOf m N G₁ G₂ ψ Q) := by
  apply Prod.ext
  · exact zOf_rotA m N s Q
  · exact xiOf_rotA m N G₁ G₂ ψ s d₁ d₂ hd₁ hd₂ hQ hQ' (h₁ _) (h₂ _)

theorem beta_rotA (χ₀ : (ZMod N → Ambient n) → ℝ)
    (hχ : ∀ z, χ₀ (rotA N (red m N s) z) = χ₀ z) (r lam : ℝ) :
    beta m N F G₁ G₂ ψ χ₀ r lam (rotA (m * N) s Q) = beta m N F G₁ G₂ ψ χ₀ r lam Q := by
  simp only [beta, cOf_rotA m N G₁ G₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ ψ hQ hQ']
  rw [cutoff_chartR s d₁ d₂ hd₁ hd₂ χ₀ hχ,
    model_chartR m N F G₁ G₂ s d₁ d₂ hd₁ hd₂ h₁ h₂,
    psi_chartR m N F G₁ G₂ s d₁ d₂ hd₁ hd₂ h₁ h₂]

theorem gDef_rotA (χ₀ : (ZMod N → Ambient n) → ℝ)
    (hχ : ∀ z, χ₀ (rotA N (red m N s) z) = χ₀ z) (r lam : ℝ) :
    gDef m N F G₁ G₂ ψ χ₀ r lam (rotA (m * N) s Q) = gDef m N F G₁ G₂ ψ χ₀ r lam Q := by
  rw [gDef, gDef, pen_rotA, beta_rotA m N F G₁ G₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ ψ hQ hQ' χ₀ hχ]

end

end Finsler.LabelRotation
