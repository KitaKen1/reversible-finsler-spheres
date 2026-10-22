module

public import Finsler.Geometry.FixedLabelTransport
public import Finsler.Topology.FixedLensTransport

/-! The actual fixed label lens and the fixed signed-coordinate product lens are isomorphic
under the original same-flow trapping hypotheses. No new descent-independence is assumed. -/

@[expose] public section

namespace Finsler.FixedLabelLens

open Module Filter Set Metric
open Finsler.RotationNatural Finsler.NormalFamily
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LabelAmbient
open scoped Topology ContDiff NNReal

open CategoryTheory Finsler.FlowLens Finsler.ProductModel Finsler.AmbientDescent
open Finsler.LabelDeform Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop
open Finsler.PairTriple Finsler.LensContinuation Finsler.LabelTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n)

variable (F : ReversibleMetric n)
  {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n} {K : ℝ≥0} (hL : LipschitzWith K V)
  (hV0 : ∀ P : ZMod (m * N) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
  {g : (ZMod (m * N) → Ambient n) → ℝ} {O : Set (ZMod (m * N) → Ambient n)}
  (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
  (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0)
  {K₀ : ℝ≥0} (hL₀ : LipschitzWith K₀ V₀) (hV00 : ∀ z : ZMod N → Ambient n, V₀ z ≠ 0 → ∀ j, z j ≠ 0)
  {O₀ : Set (ZMod N → Ambient n)}
  (hg₀ : ∀ z ∈ O₀, DifferentiableAt ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z)
  (hsupp₀ : ∀ z, V₀ z ≠ 0 → z ∈ O₀)
  (hle₀ : ∀ z ∈ O₀, fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z (V₀ z) ≤ 0)
  (hh : Continuous fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)

theorem nonempty_equiv (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₀ : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ Z₀, ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z ∈ Z₀, ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hmodel : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ,
      g Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1))
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) {a c T : ℝ} (hT : 0 ≤ T)
    (hS₁ : ∀ w, w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ → g w.1 < c →
      a ≤ g ((descentOf hL hV0 hg hsupp hle).flow T w).1 → ∀ s, 0 ≤ s → s ≤ T →
      (descentOf hL hV0 hg hsupp hle).flow s w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ)
    (hS₂ : ∀ w, w ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ →
      (cone b (EuclideanSpace ℝ (Fin p)) hh).energy w < c →
      a ≤ (cone b (EuclideanSpace ℝ (Fin p)) hh).energy
        ((descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow T w) →
      ∀ s, 0 ≤ s → s ≤ T →
        (descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh).flow s w ∈
          labelSetM m N G₁ G₂ ψ Z₀ U ρ) (q : ℕ) :
    Nonempty (
      H (triv (pairOf (inter_subset_inter_left
        {Q : Om n (m * N) | rotA (m * N) s Q.1 = Q.1}
        (partY_sub_partU (fun Q : Om n (m * N) => g Q.1)
          (descentOf hL hV0 hg hsupp hle) (labelSetA m N G₁ G₂ ψ Z₀ U ρ) a c T)))) q ≃ₗ[ZMod 2]
      H (triv (pairOf (X := Model (Om n N) b (EuclideanSpace ℝ (Fin p))) (inter_subset_inter_left
        {w | Finsler.FixedLabelTransport.modelFixed s d₁ d₂ w}
        (partY_sub_partU (cone b (EuclideanSpace ℝ (Fin p)) hh).energy
          (descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh)
          (labelSetM m N G₁ G₂ ψ Z₀ U ρ) a c T)))) q) := by
  let ξ : labelSetA m N G₁ G₂ ψ Z₀ U ρ ≃ₜ labelSetM m N G₁ G₂ ψ Z₀ U ρ :=
    labelHomeo m N G₁ G₂ ψ hG₁ hG₂ hZ₀
  have henergy := fun w => energy_toModel m N G₁ G₂ ψ F hh hZ₀ hmodel w
  have hA₁ := fun w hw => flow_corr_amb m N G₁ G₂ ψ V₀ F hL hV0 hg hsupp hle hL₀ hV00
    hg₀ hsupp₀ hle₀ hh hG₁ hG₂ hZ₀ hmodel hU hT w hw
  have hA₂ := fun w hw => flow_corr_model m N G₁ G₂ ψ V₀ F hL hV0 hg hsupp hle hL₀ hV00
    hg₀ hsupp₀ hle₀ hh hG₁ hG₂ hZ₀ hmodel hU hT w hw
  have hlens := Finsler.LensTransport.lens_iff (descentOf hL hV0 hg hsupp hle)
    (descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh)
    ξ henergy hS₁ hS₂ hA₁ hA₂
  exact Finsler.FixedLensTransport.nonempty_equiv (descentOf hL hV0 hg hsupp hle)
    (descent b (EuclideanSpace ℝ (Fin p)) (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh)
    ξ henergy
    (fun Q => Finsler.FixedLabelTransport.label_fixed_iff G₁ G₂ ψ s d₁ d₂ hd₁ hd₂ h₁ h₂ hZ₀ Q)
    hlens q

end

end Finsler.FixedLabelLens

