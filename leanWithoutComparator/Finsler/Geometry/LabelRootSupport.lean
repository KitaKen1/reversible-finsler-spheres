module

public import Finsler.Geometry.RootTubeData
public import Finsler.Geometry.FixedLabelTrapped

/-! Use retained root/tube witnesses to discharge the root-side inputs of fixed-label support. -/

@[expose] public section

namespace Finsler.LabelRootSupport

open Module Set Finsler.Geometry Finsler.SphereGeometry Finsler.AmbientPenalty
open Finsler.AmbientSymmetry Finsler.PolygonIterate Finsler.SymmetricBlocks
open Finsler.AmbientNormalIndex Finsler.CircleFrameField Finsler.FrameCoordinates
open Finsler.FrameInverse Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform
open Finsler.LensContinuation Finsler.LabelTransport Finsler.AmbientDescent Finsler.FlowLens Finsler.LensFamily
open Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LabelRootData
open scoped NNReal ContDiff

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {n m N b p : ℕ} [NeZero m] [NeZero N]
  (F : ReversibleMetric n) (hn : 1 ≤ n)
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (a : ZMod (m * N)) (Γ : Set (ZMod N → Ambient n)) (R : Set (Om n N))
  (a₀ b₀ c₀ : ℝ) (𝒰 : Set (ZMod (m * N) → Ambient n))
  (B : RootTubeData F (G₁ := G₁) (G₂ := G₂) ψ a Γ R a₀ b₀ c₀ 𝒰)

include hn in
theorem exists_fixed_support (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z ∈ B.Z₀, ∀ i, G₁ (rotA N (red m N a) z) i = d₁ i • Finsler.NormalFamily.rotV m N a (G₁ z i))
    (h₂ : ∀ z ∈ B.Z₀, ∀ i, G₂ (rotA N (red m N a) z) i = d₂ i • Finsler.NormalFamily.rotV m N a (G₂ z i))
    {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n} {K : ℝ≥0}
    (hL : LipschitzWith K V) (hV0 : ∀ Q, V Q ≠ 0 → ∀ j, Q j ≠ 0)
    {g : (ZMod (m * N) → Ambient n) → ℝ} {O : Set (ZMod (m * N) → Ambient n)}
    (hg : ∀ Q ∈ O, DifferentiableAt ℝ g Q) (hsupp : ∀ Q, V Q ≠ 0 → Q ∈ O)
    (hle : ∀ Q ∈ O, fderiv ℝ g Q (V Q) ≤ 0)
    (hmodel : ∀ Q ∈ labelSetA m N G₁ G₂ ψ B.Z₀ B.U B.ρ,
      g Q.1 = model m N F G₁ G₂ (cOf m N G₁ G₂ ψ Q.1))
    (hU : ∀ Q ∈ B.U, V Q = splitW m N G₁ G₂ ψ B.V Q)
    {Ra : Set (Om n (m * N))} (hRa : IsOpen Ra)
    (hAdis : Disjoint (labelSetA m N G₁ G₂ ψ B.Z₀ B.U B.ρ) Ra)
    (hgc : Continuous fun Q : Om n (m * N) => g Q.1)
    (hKa : IsCompact {Q : Om n (m * N) | a₀ ≤ g Q.1 ∧ g Q.1 ≤ b₀})
    (hstricta : ∀ Q : Om n (m * N), a₀ ≤ g Q.1 → g Q.1 ≤ b₀ →
      Q ∉ labelSetA m N G₁ G₂ ψ B.Z B.U (B.ρ / Real.exp 1) ∪ Ra →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1)
    (A : ℕ)
    (hf : ∀ q, Module.Finite (ZMod 2) (crossH
      (fun z : TopCat.of {z : Om n N | rotA N (red m N a) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1.1) (B.lower.le.trans B.upper.le) q))
    (hz : ∀ q, A ≤ q → ∀ z : crossH
      (fun z : TopCat.of {z : Om n N | rotA N (red m N a) z.1 = z.1} =>
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1.1) (B.lower.le.trans B.upper.le) q, z = 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ l u T : ℝ, 1 ≤ T → l < c₀ → c₀ < u →
      a₀ ≤ l - (u - l) / (Real.exp (2 * T) - 1) →
      u + (u - l) / (Real.exp (2 * T) - 1) ≤ b₀ →
      (u + (u - l) / (Real.exp (2 * T) - 1)) - (l - (u - l) / (Real.exp (2 * T) - 1)) < d →
      (∀ q, Module.Finite (ZMod 2)
        (H (triv (pairOf (inter_subset_inter_left
          {Q : Om n (m * N) | rotA (m * N) a Q.1 = Q.1}
          (partY_sub_partU (fun Q : Om n (m * N) => g Q.1)
            (descentOf hL hV0 hg hsupp hle) (labelSetA m N G₁ G₂ ψ B.Z₀ B.U B.ρ) l u T)))) q)) ∧
        ∀ q, q < Fintype.card {i : Fin b // d₁ i = 1} ∨
          Fintype.card {i : Fin b // d₁ i = 1} + A ≤ q → ∀ z :
          H (triv (pairOf (inter_subset_inter_left
            {Q : Om n (m * N) | rotA (m * N) a Q.1 = Q.1}
            (partY_sub_partU (fun Q : Om n (m * N) => g Q.1)
              (descentOf hL hV0 hg hsupp hle) (labelSetA m N G₁ G₂ ψ B.Z₀ B.U B.ρ) l u T)))) q, z = 0 := by
  have hh : Continuous fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1 :=
    continuous_const.mul (penW_continuous F hn (1 / m))
  exact Finsler.FixedLabelTrapped.exists_support m N G₁ G₂ ψ B.V F hL hV0 hg hsupp hle
    B.lipschitz B.nonzero B.diff B.supp B.nonpos hh hG₁ hG₂ B.root_nonzero a d₁ d₂ hd₁ hd₂
    h₁ h₂ B.fixed hmodel hU B.ρ_pos B.tube B.lower B.upper (B.lower.le.trans B.upper.le)
    (B.Z₀_open.preimage continuous_subtype_val) B.rest_open B.disjoint B.compact_band B.bound
    B.Z_open B.subset B.margin B.small_strict B.value_strict B.U_open hRa hAdis hgc hKa hstricta A hf hz

end

end Finsler.LabelRootSupport
