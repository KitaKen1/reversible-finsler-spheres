module

public import Finsler.Geometry.FixedLabelTransport
public import Finsler.Topology.FixedProductFlow
public import Finsler.Topology.FixedProductCore
public import Finsler.Geometry.FixedLabelSupport
public import Finsler.Topology.ProductRootSupport
public import Finsler.Geometry.RootTrap
public import Finsler.Geometry.AmbientTrap

/-! Actual fixed-label support with both whole-orbit traps constructed from compact bands,
strict descent, a bounded root field and nested root/coordinate margins. -/

@[expose] public section

namespace Finsler.FixedLabelTrapped

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
set_option maxHeartbeats 2000000
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

include hh in
theorem exists_support (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
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
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q)
    (hρ : 0 < ρ)
    (hZρ : ∀ z ∈ Z₀, ∀ (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)), ‖u‖ < ρ →
      ‖y‖ < ρ → IsUnit (matA m N G₁ G₂ ψ z) ∧ coord m N G₁ G₂ (z, unE u y) ∈ U ∧
        ∀ j, coord m N G₁ G₂ (z, unE u y) j ≠ 0)
    {a₀ b₀ c₀ : ℝ} (ha₀ : a₀ < c₀) (hb₀ : c₀ < b₀) (hab₀ : a₀ ≤ b₀)
    (hsel : IsOpen {z : Om n N | z.1 ∈ Z₀}) {R : Set (Om n N)} (hR : IsOpen R)
    (hdis : Disjoint {z : Om n N | z.1 ∈ Z₀} R)
    (hK : IsCompact {z : Om n N | a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ∧
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀})
    {κ : ℝ} (hκ : ∀ z, ‖V₀ z‖ ≤ κ) {Z : Set (ZMod N → Ambient n)}
    (hZopen : IsOpen Z) (hZZ : Z ⊆ Z₀)
    (hmargin : ∀ z ∈ Z, ∀ z', ‖z' - z‖ ≤ κ → z' ∈ Z₀)
    (hsmall : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → z ∉ {z : Om n N | z.1 ∈ Z} ∪ R →
      (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1)
    (hval : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≠ c₀ →
      (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf hL₀ hV00 hg₀ hsupp₀ hle₀).flow 1 z).1 <
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1)
    (hUopen : IsOpen U) {Ra : Set (Om n (m * N))} (hRa : IsOpen Ra)
    (hAdis : Disjoint (labelSetA m N G₁ G₂ ψ Z₀ U ρ) Ra)
    (hgc : Continuous fun Q : Om n (m * N) => g Q.1)
    (hKa : IsCompact {Q : Om n (m * N) | a₀ ≤ g Q.1 ∧ g Q.1 ≤ b₀})
    (hstricta : ∀ Q : Om n (m * N), a₀ ≤ g Q.1 → g Q.1 ≤ b₀ →
      Q ∉ labelSetA m N G₁ G₂ ψ Z U (ρ / Real.exp 1) ∪ Ra →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1)
    (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH
      (fun z : TopCat.of {z : Om n N | rotA N (red m N s) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1.1) hab₀ q))
    (hz : ∀ q, A ≤ q → ∀ z : crossH
      (fun z : TopCat.of {z : Om n N | rotA N (red m N s) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1.1) hab₀ q, z = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c T : ℝ, 1 ≤ T → a < c₀ → c₀ < c →
      a₀ ≤ a - (c - a) / (Real.exp (2 * T) - 1) →
      c + (c - a) / (Real.exp (2 * T) - 1) ≤ b₀ →
      (c + (c - a) / (Real.exp (2 * T) - 1)) - (a - (c - a) / (Real.exp (2 * T) - 1)) < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (inter_subset_inter_left
          {Q : Om n (m * N) | rotA (m * N) s Q.1 = Q.1}
          (partY_sub_partU (fun Q : Om n (m * N) => g Q.1)
            (descentOf hL hV0 hg hsupp hle) (labelSetA m N G₁ G₂ ψ Z₀ U ρ) a c T)))) q)) ∧
        ∀ q, q < Fintype.card {i : Fin b // d₁ i = 1} ∨
          Fintype.card {i : Fin b // d₁ i = 1} + A ≤ q → ∀ z :
          H (triv (pairOf (inter_subset_inter_left
            {Q : Om n (m * N) | rotA (m * N) s Q.1 = Q.1}
            (partY_sub_partU (fun Q : Om n (m * N) => g Q.1)
              (descentOf hL hV0 hg hsupp hle) (labelSetA m N G₁ G₂ ψ Z₀ U ρ) a c T)))) q, z = 0 := by
  have hZo : IsOpen {z : Om n N | z.1 ∈ Z} := hZopen.preimage continuous_subtype_val
  obtain ⟨dp, hdp, hp⟩ := Finsler.FixedLabelSupport.exists_support m N G₁ G₂ ψ V₀ F
    hL hV0 hg hsupp hle hL₀ hV00 hg₀ hsupp₀ hle₀ hh hG₁ hG₂ hZ₀ s d₁ d₂ hd₁ hd₂
    h₁ h₂ hroot hmodel hU hρ hZρ ha₀ hb₀ hab₀ hsel hR hdis hK hκ hZo hZZ hmargin
    hsmall hval A hf hz
  have hexp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp (by norm_num)
  have hρρ : ρ / Real.exp 1 ≤ ρ := by
    exact (div_le_iff₀ (Real.exp_pos _)).mpr (by nlinarith)
  have hρexp : (ρ / Real.exp 1) * Real.exp 1 ≤ ρ := by
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.exp_pos _))]
  obtain ⟨da, hda, ha⟩ := Finsler.AmbientTrap.exists_ambient_trap m N G₁ G₂ ψ V₀
    hL hV0 hg hsupp hle hL₀ hG₁ hG₂ hZopen hUopen hZZ hρρ hZρ hU hκ hmargin hρexp
    hRa hAdis hgc hKa hstricta
  refine ⟨min dp da, lt_min hdp hda, fun a c T hT hac hcc hlo hhi hw => ?_⟩
  have hε := Finsler.ProductShift.eps_nonneg (hac.trans hcc).le hT
  apply hp a c T hT hac hcc hlo hhi (hw.trans_le (min_le_left _ _))
  apply ha a c T (by linarith) (by linarith) (by
    have := hw.trans_le (min_le_right dp da)
    linarith) hT

end

end Finsler.FixedLabelTrapped
