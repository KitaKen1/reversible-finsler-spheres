module

public import Finsler.Geometry.LabelPackRootReidx
public import Finsler.Geometry.LabelPackBands
public import Finsler.Geometry.LabelRootSupport
public import Finsler.Geometry.FixedLabelTrapped

/-! The fixed-label support theorem for the actual ambient vertex count after equality reindexing. -/

@[expose] public section

namespace Finsler.LabelPackBandsReidx

open Module Set Finsler.Geometry Finsler.SphereGeometry Finsler.AmbientPenalty
open Finsler.AmbientSymmetry Finsler.PolygonIterate Finsler.SymmetricBlocks
open Finsler.AmbientNormalIndex Finsler.CircleFrameField Finsler.FrameCoordinates
open Finsler.FrameInverse Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform
open Finsler.LensContinuation Finsler.LabelTransport Finsler.AmbientDescent Finsler.FlowLens Finsler.LensFamily
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LabelRootData Finsler.LabelPackRoot Finsler.LabelPackRootReidx Finsler.LabelPack
open scoped NNReal ContDiff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n m N b p K : ℕ} [NeZero m] [NeZero N]
  [NeZero K] (hK : m * N = K)
  (F : ReversibleMetric n) (hn : 1 ≤ n)
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (a : ZMod (m * N)) (Γ : Set (ZMod N → Ambient n)) (R : Set (Om n N))
  (a₀ b₀ c₀ : ℝ) (𝒰 : Set (ZMod K → Ambient n))
  (U : Set (ZMod K → Ambient n))
  (W : (ZMod K → Ambient n) → ZMod K → Ambient n)
  (β : (ZMod K → Ambient n) → ℝ) (T₀ : Set (ZMod K → Ambient n))
  (𝒲 𝒲' : Set (Om n K)) (Z₀ : Set (ZMod N → Ambient n))
  (ψ₀ : Descent (Om n N) (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1))
  (hshare : SharedRootAt F (G₁ := G₁) (G₂ := G₂) hK ψ a Γ R a₀ b₀ c₀ 𝒰 U W β T₀ 𝒲 𝒲' Z₀ ψ₀)
  (hab₀ : a₀ ≤ b₀)

include hn hshare in
theorem exists_fixed_support (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z i, G₁ (rotA N (red m N a) z) i = d₁ i • Finsler.NormalFamily.rotV m N a (G₁ z i))
    (h₂ : ∀ z i, G₂ (rotA N (red m N a) z) i = d₂ i • Finsler.NormalFamily.rotV m N a (G₂ z i))
    {V : (ZMod K → Ambient n) → ZMod K → Ambient n} {KL : ℝ≥0}
    (hL : LipschitzWith KL V) (hV0 : ∀ Q, V Q ≠ 0 → ∀ j, Q j ≠ 0)
    {g : (ZMod K → Ambient n) → ℝ} {O : Set (ZMod K → Ambient n)}
    (hg : ∀ Q ∈ O, DifferentiableAt ℝ g Q) (hsupp : ∀ Q, V Q ≠ 0 → Q ∈ O)
    (hle : ∀ Q ∈ O, fderiv ℝ g Q (V Q) ≤ 0)
    (hVT : ∀ Q ∈ T₀, V Q = W Q)
    (hgT : ∀ Q ∈ T₀, g Q = pen F K 1 Q + β Q)
    {a₀a b₀a : ℝ} (ha₀a : a₀a < c₀) (hb₀a : c₀ < b₀a)
    {Ra : Set (Om n K)} (hRa : IsOpen Ra)
    (hAdis : Disjoint (𝒲) Ra)
    (hgc : Continuous fun Q : Om n K => g Q.1)
    (hKa : IsCompact {Q : Om n K | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a})
    (hstricta : ∀ Q : Om n K, a₀a ≤ g Q.1 → g Q.1 ≤ b₀a →
      Q ∉ 𝒲' ∪ Ra →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1)
    (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH
      (fun z : TopCat.of {z : Om n N | rotA N (red m N a) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1.1) hab₀ q))
    (hz : ∀ q, A ≤ q → ∀ z : crossH
      (fun z : TopCat.of {z : Om n N | rotA N (red m N a) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1.1) hab₀ q, z = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ l u T : ℝ, 1 ≤ T → l < c₀ → c₀ < u →
      a₀ ≤ l - (u - l) / (Real.exp (2 * T) - 1) →
      u + (u - l) / (Real.exp (2 * T) - 1) ≤ b₀ →
      (u + (u - l) / (Real.exp (2 * T) - 1)) - (l - (u - l) / (Real.exp (2 * T) - 1)) < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (inter_subset_inter_left
          {Q : Om n K | rotA K (reidxShift hK a) Q.1 = Q.1}
          (partY_sub_partU (fun Q : Om n K => g Q.1)
            (descentOf hL hV0 hg hsupp hle) (𝒲) l u T)))) q)) ∧
        ∀ q, q < Fintype.card {i : Fin b // d₁ i = 1} ∨
          Fintype.card {i : Fin b // d₁ i = 1} + A ≤ q → ∀ z :
          H (triv (pairOf (inter_subset_inter_left
            {Q : Om n K | rotA K (reidxShift hK a) Q.1 = Q.1}
            (partY_sub_partU (fun Q : Om n K => g Q.1)
              (descentOf hL hV0 hg hsupp hle) (𝒲) l u T)))) q, z = 0 := by
  subst hK
  exact Finsler.LabelPackBands.exists_fixed_support F hn G₁ G₂ ψ a Γ R a₀ b₀ c₀ 𝒰
    U W β T₀ 𝒲 𝒲' Z₀ ψ₀ hshare hab₀ hG₁ hG₂ d₁ d₂ hd₁ hd₂ h₁ h₂ hL hV0 hg hsupp hle
    hVT hgT ha₀a hb₀a hRa hAdis hgc hKa hstricta A hf hz

end

end Finsler.LabelPackBandsReidx

