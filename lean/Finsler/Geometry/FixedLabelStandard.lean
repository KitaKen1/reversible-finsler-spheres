module

public import Finsler.Geometry.FixedLabelTransport
public import Finsler.Topology.FixedProductFlow
public import Finsler.Topology.FixedProductCore
public import Finsler.Geometry.FixedLabelLens

/-! The actual fixed ambient label lens is the standard product lens over the reduced-action
fixed root. Existing actual flow correspondence and trapping are retained. -/

@[expose] public section

namespace Finsler.FixedLabelStandard

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
open Finsler.PairTriple Finsler.LensContinuation Finsler.LabelTransport Finsler.LensFamily

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
    (hroot : ∀ t (z : Om n N), 0 ≤ t → rotA N (red m N s) z.1 = z.1 →
      rotA N (red m N s) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow t z).1 =
        ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow t z).1)
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
      lensH (Finsler.FixedProductFlow.standardDescent
        {z : Om n N | rotA N (red m N s) z.1 = z.1} d₁ d₂
        (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh hroot)
        (Finsler.FixedProductRegion.standardRegion
        (fun z : Om n N => rotA N (red m N s) z.1 = z.1) d₁ d₂
        (labelSetM m N G₁ G₂ ψ Z₀ U ρ)) a c T q) := by
  obtain ⟨e₁⟩ := Finsler.FixedLabelLens.nonempty_equiv m N G₁ G₂ ψ V₀ F hL hV0 hg hsupp hle
    hL₀ hV00 hg₀ hsupp₀ hle₀ hh hG₁ hG₂ hZ₀ s d₁ d₂ hd₁ hd₂ h₁ h₂ hmodel hU hT hS₁ hS₂ q
  obtain ⟨e₂⟩ := Finsler.FixedProductFlow.nonempty_lens_equiv
    {z : Om n N | rotA N (red m N s) z.1 = z.1} d₁ d₂
    (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh hroot
    (labelSetM m N G₁ G₂ ψ Z₀ U ρ) a c T hT q
  exact ⟨e₁.trans e₂⟩

theorem full_product_equiv (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₀ : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}
    (hZ₀ : ∀ z ∈ Z₀, ∀ j, z j ≠ 0)
    (s : ZMod (m * N)) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ Z₀, ∀ i, G₁ (rotA N (red m N s) z) i = d₁ i • rotV m N s (G₁ z i))
    (h₂ : ∀ z ∈ Z₀, ∀ i, G₂ (rotA N (red m N s) z) i = d₂ i • rotV m N s (G₂ z i))
    (hroot : ∀ t (z : Om n N), 0 ≤ t → rotA N (red m N s) z.1 = z.1 →
      rotA N (red m N s) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow t z).1 =
        ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow t z).1)
    (hmodel : ∀ Q ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ,
      g Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1))
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) {a c T : ℝ} (hT : 1 ≤ T)
    (hS₁ : ∀ w, w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ → g w.1 < c →
      a ≤ g ((descentOf hL hV0 hg hsupp hle).flow T w).1 → ∀ s, 0 ≤ s → s ≤ T →
      (descentOf hL hV0 hg hsupp hle).flow s w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ)
    (hρ : 0 < ρ)
    (hZρ : ∀ z ∈ Z₀, ∀ (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)), ‖u‖ < ρ →
      ‖y‖ < ρ → IsUnit (matA m N G₁ G₂ ψ z) ∧ coord m N G₁ G₂ (z, unE u y) ∈ U ∧
        ∀ j, coord m N G₁ G₂ (z, unE u y) j ≠ 0)
    (hw : 4 * (c - a) < ρ ^ 2)
    (hbase : ∀ z : Om n N, z.1 ∈ Z₀ →
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 < c + (c - a) / (Real.exp (2 * T) - 1) →
      a - (c - a) / (Real.exp (2 * T) - 1) ≤
        (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow T z).1 →
      ∀ t, 0 ≤ t → t ≤ T → ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow t z).1 ∈ Z₀) (q : ℕ) :
    Nonempty (
      H (triv (pairOf (inter_subset_inter_left
        {Q : Om n (m * N) | rotA (m * N) s Q.1 = Q.1}
        (partY_sub_partU (fun Q : Om n (m * N) => g Q.1)
          (descentOf hL hV0 hg hsupp hle) (labelSetA m N G₁ G₂ ψ Z₀ U ρ) a c T)))) q ≃ₗ[ZMod 2]
      lensH (Finsler.FixedProductFlow.standardDescent
        {z : Om n N | rotA N (red m N s) z.1 = z.1} d₁ d₂
        (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh hroot)
        (over (Fintype.card {i : Fin b // d₁ i = 1})
          (EuclideanSpace ℝ (Fin (Fintype.card {i : Fin p // d₂ i = 1})))
          (Subtype.val ⁻¹' {z : Om n N | z.1 ∈ Z₀})) a c T q) := by
  have hS : ∀ w : Model (Om n N) b (EuclideanSpace ℝ (Fin p)), w.1.1 ∈ Z₀ →
      ‖w.2.1‖ < ρ → ‖w.2.2‖ < ρ → w ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ := by
    intro w hz hu hy
    obtain ⟨h1, h2, h3⟩ := hZρ w.1.1 hz w.2.1 w.2.2 hu hy
    exact ⟨h1, hz, hu, hy, h2, h3⟩
  have hS' : ∀ w ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ, w.1.1 ∈ Z₀ ∧ ‖w.2.2‖ < ρ :=
    fun w hw => ⟨hw.2.1, hw.2.2.2.1⟩
  have hS₂ := fun w (hwS : w ∈ labelSetM m N G₁ G₂ ψ Z₀ U ρ) hwc hwa t ht htT =>
    Finsler.ModelTrap.orbit_stay b (EuclideanSpace ℝ (Fin p))
      (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh hS hS' hT (by nlinarith [sq_nonneg ρ]) hbase w hwS hwc hwa t ht htT
  obtain ⟨e₁⟩ := nonempty_equiv m N G₁ G₂ ψ V₀ F hL hV0 hg hsupp hle hL₀ hV00
    hg₀ hsupp₀ hle₀ hh hG₁ hG₂ hZ₀ s d₁ d₂ hd₁ hd₂ h₁ h₂ hroot hmodel hU
    (zero_le_one.trans hT) hS₁ hS₂ q
  let a' := a - (ρ ^ 2 - 4 * (c - a)) / 4
  have ha' : a' < a := by dsimp [a']; linarith
  have hw' : 2 * (c - a') < ρ ^ 2 := by dsimp [a']; nlinarith [sq_pos_of_pos hρ]
  obtain ⟨e₂⟩ := Finsler.FixedProductCore.nonempty_core_equiv
    (U := labelSetM m N G₁ G₂ ψ Z₀ U ρ) (W := {z : Om n N | z.1 ∈ Z₀})
    {z : Om n N | rotA N (red m N s) z.1 = z.1} d₁ d₂
    (descentOf hL₀ hV00 hg₀ hsupp₀ hle₀) hh hroot hS hS' hρ ha' hT hw' q
  exact ⟨e₁.trans e₂⟩

end

end Finsler.FixedLabelStandard
