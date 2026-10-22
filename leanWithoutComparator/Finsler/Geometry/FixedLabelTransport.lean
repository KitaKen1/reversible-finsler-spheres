module

public import Finsler.Geometry.FixedCoefficientModel
public import Finsler.Geometry.LabelTransport
public import Finsler.Geometry.FixedProductRegion

/-! Fixed signed-coordinate, energy, flow and index comparison. -/

@[expose] public section

namespace Finsler.FixedLabelTransport

open Set Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientSymmetry
open Finsler.AmbientNormalIndex Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.RotationNatural Finsler.PolygonIterate Finsler.SymmetricBlocks Finsler.NormalFamily
open Finsler.LabelTransport Finsler.LabelDeform Finsler.FixedCoefficientModel
open Finsler.AmbientPenalty
open Finsler.AmbientSplitField
open scoped ContDiff NNReal

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
variable {Z₀ : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}

def modelFixed (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (w : (Om n N) × EuclideanSpace ℝ (Fin b) × EuclideanSpace ℝ (Fin p)) : Prop :=
  rotA N (red m N s) w.1.1 = w.1.1 ∧ w.2.1 ∈ eucFixed d₁ ∧ w.2.2 ∈ eucFixed d₂

theorem label_fixed_iff (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ Z₀, ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z ∈ Z₀, ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    (Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ) :
    rotA (m * N) s Q.1.1 = Q.1.1 ↔
      modelFixed s d₁ d₂ (toModel m N G₁ G₂ ψ hZ₀ Q).1 := by
  rw [FixedFrameCoordinates.fixed_iff G₁ G₂ ψ s d₁ d₂ hd₁ hd₂ Q.2.1
    (h₁ _ Q.2.2.1) (h₂ _ Q.2.2.1)]
  change (_ ∧ (diagonal d₁ (xiOf m N G₁ G₂ ψ Q.1.1).1,
      diagonal d₂ (xiOf m N G₁ G₂ ψ Q.1.1).2) = xiOf m N G₁ G₂ ψ Q.1.1) ↔
    (_ ∧ diagonal d₁ (xiOf m N G₁ G₂ ψ Q.1.1).1 = (xiOf m N G₁ G₂ ψ Q.1.1).1 ∧
      diagonal d₂ (xiOf m N G₁ G₂ ψ Q.1.1).2 = (xiOf m N G₁ G₂ ψ Q.1.1).2)
  rw [Prod.mk.injEq]
  rfl

def fixedLabelHomeo (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ Z₀, ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z ∈ Z₀, ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0) :
    {Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ // rotA (m * N) s Q.1.1 = Q.1.1} ≃ₜ
      {w : labelSetM m N G₁ G₂ ψ Z₀ U ρ // modelFixed s d₁ d₂ w.1} :=
  (labelHomeo m N G₁ G₂ ψ hG₁ hG₂ hZ₀).subtype
    (label_fixed_iff G₁ G₂ ψ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀)

theorem fixed_energy (F : ReversibleMetric n) (hG₁ : ContDiff ℝ ∞ G₁)
    (hG₂ : ContDiff ℝ ∞ G₂)
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ Z₀, ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z ∈ Z₀, ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    {g : (ZMod (m * N) → Ambient n) → ℝ}
    (hg : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ,
      g Q.1 = model m N F G₁ G₂ (Finsler.LabelAmbient.cOf m N G₁ G₂ ψ Q.1))
    (Q : {Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ // rotA (m * N) s Q.1.1 = Q.1.1}) :
    let w := (fixedLabelHomeo G₁ G₂ ψ hG₁ hG₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀ Q).1.1
    (m : ℝ) ^ 2 * Finsler.AmbientPenalty.pen F N (1 / m) w.1.1 - ‖w.2.1‖ ^ 2 +
      ‖w.2.2‖ ^ 2 = g Q.1.1.1 := by
  dsimp only
  rw [hg _ Q.1.2]
  unfold model sqX sqY
  rw [psi_zero]
  rfl

def standardLabelHomeo (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ Z₀, ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z ∈ Z₀, ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0) :
    {Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ // rotA (m * N) s Q.1.1 = Q.1.1} ≃ₜ
      FixedProductRegion.standardRegion
        (fun z : Om n N => rotA N (red m N s) z.1 = z.1) d₁ d₂
        (labelSetM m N G₁ G₂ ψ Z₀ U ρ) :=
  (fixedLabelHomeo G₁ G₂ ψ hG₁ hG₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀).trans
    (FixedProductRegion.standardRegionHomeo
      (fun z : Om n N => rotA N (red m N s) z.1 = z.1) d₁ d₂
      (labelSetM m N G₁ G₂ ψ Z₀ U ρ))

theorem standard_base (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ Z₀, ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z ∈ Z₀, ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    (Q : {Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ // rotA (m * N) s Q.1.1 = Q.1.1}) :
    (standardLabelHomeo G₁ G₂ ψ hG₁ hG₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀ Q).1.1.1.1 =
      zOf m N Q.1.1.1 := rfl

theorem standard_energy (F : ReversibleMetric n) (hG₁ : ContDiff ℝ ∞ G₁)
    (hG₂ : ContDiff ℝ ∞ G₂)
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ Z₀, ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z ∈ Z₀, ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    {g : (ZMod (m * N) → Ambient n) → ℝ}
    (hg : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ,
      g Q.1 = model m N F G₁ G₂ (Finsler.LabelAmbient.cOf m N G₁ G₂ ψ Q.1))
    (Q : {Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ // rotA (m * N) s Q.1.1 = Q.1.1}) :
    let w := (standardLabelHomeo G₁ G₂ ψ hG₁ hG₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀ Q).1
    (m : ℝ) ^ 2 * pen F N (1 / m) w.1.1.1 - ‖w.2.1‖ ^ 2 + ‖w.2.2‖ ^ 2 = g Q.1.1.1 := by
  dsimp only
  exact (FixedProductRegion.standard_energy
    (fun z : Om n N => rotA N (red m N s) z.1 = z.1) d₁ d₂
    (labelSetM m N G₁ G₂ ψ Z₀ U ρ)
    (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)
    (fixedLabelHomeo G₁ G₂ ψ hG₁ hG₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀ Q)).trans
    (fixed_energy G₁ G₂ ψ F hG₁ hG₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀ hg Q)

theorem standard_flow (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ Z₀, ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z ∈ Z₀, ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n)
    {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n}
    {K K₀ : ℝ≥0} (hV : LipschitzWith K V) (hV₀ : LipschitzWith K₀ V₀)
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) {T : ℝ}
    (Q Q' : {Q : labelSetA m N G₁ G₂ ψ Z₀ U ρ // rotA (m * N) s Q.1.1 = Q.1.1})
    (hT : 0 ≤ T)
    (hin : ∀ t ∈ Icc 0 T, ODE.globalSolution V hV Q.1.1.1 t ∈ U ∧
      IsUnit (matA m N G₁ G₂ ψ (zOf m N (ODE.globalSolution V hV Q.1.1.1 t))))
    (hQ' : Q'.1.1.1 = ODE.globalSolution V hV Q.1.1.1 T) :
    let w := (standardLabelHomeo G₁ G₂ ψ hG₁ hG₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀ Q).1
    let w' := (standardLabelHomeo G₁ G₂ ψ hG₁ hG₂ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀ Q').1
    (w'.1.1.1, w'.2.1, w'.2.2) =
      (ODE.globalSolution V₀ hV₀ w.1.1.1 T,
        Real.exp T • w.2.1, Real.exp (-T) • w.2.2) := by
  have hc := cOf_globalSolution m N G₁ G₂ ψ V₀ hG₁ hG₂ hV hU hV₀ Q.1.1.1 hin T ⟨hT, le_rfl⟩
  rw [← hQ'] at hc
  have hz := congrArg Prod.fst hc
  have hξ := congrArg Prod.snd hc
  change xiOf m N G₁ G₂ ψ Q'.1.1.1 =
    (Real.exp T • (xiOf m N G₁ G₂ ψ Q.1.1.1).1,
      Real.exp (-T) • (xiOf m N G₁ G₂ ψ Q.1.1.1).2) at hξ
  dsimp only
  refine Prod.ext ?_ ?_
  · exact hz
  · apply Prod.ext
    · change modelEquiv d₁ _ = Real.exp T • modelEquiv d₁ _
      rw [← (modelEquiv d₁).map_smul]
      apply congrArg (modelEquiv d₁)
      apply Subtype.ext
      change eucX (xiOf m N G₁ G₂ ψ Q'.1.1.1) =
      Real.exp T • eucX (xiOf m N G₁ G₂ ψ Q.1.1.1)
      rw [hξ]
      rfl
    · change modelEquiv d₂ _ = Real.exp (-T) • modelEquiv d₂ _
      rw [← (modelEquiv d₂).map_smul]
      apply congrArg (modelEquiv d₂)
      apply Subtype.ext
      change eucY (xiOf m N G₁ G₂ ψ Q'.1.1.1) =
      Real.exp (-T) • eucY (xiOf m N G₁ G₂ ψ Q.1.1.1)
      rw [hξ]
      rfl

end

end Finsler.FixedLabelTransport
