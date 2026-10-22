module

public import Finsler.Geometry.LabelPackBase
public import Finsler.Geometry.LabelPackRoot
public import Finsler.Geometry.RootField
public import Finsler.Geometry.InvariantLabelChoice
public import Finsler.Geometry.LabelRegionRotation
public import Finsler.Geometry.LabelSetRotation
public import Finsler.Geometry.RootFieldRotation

/-! Keep the shared actual root witnesses through equality reindexing of ambient vertices. -/

@[expose] public section

namespace Finsler.LabelPackRootReidx

open Finsler.LabelPack Finsler.LabelPackRoot
open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.NormalFamily
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform Finsler.LabelTransport
open Finsler.LabelRegions Finsler.LabelData Finsler.LabelLevel Finsler.LevelField
open Finsler.LabelRegion Finsler.AmbientDescent Finsler.FlowLens Finsler.LogCutoff
open CategoryTheory Finsler.BorelCochain Finsler.BorelPair Finsler.BorelLoop Finsler.PairTriple
open Finsler.LensContinuation Finsler.ProductModel
open scoped Topology ContDiff NNReal

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} {m N : ℕ} [NeZero m] [NeZero N] (F : ReversibleMetric n) {b p : ℕ}
  {G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m}
  {G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m}


def SharedRootAt {K : ℕ} (hK : m * N = K)
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (a : ZMod (m * N)) (Γ : Set (ZMod N → Ambient n)) (Wrest : Set (Om n N))
    (a₀ b₀ c₀ : ℝ) (𝒰 : Set (ZMod K → Ambient n))
    (U : Set (ZMod K → Ambient n)) (W : (ZMod K → Ambient n) → ZMod K → Ambient n)
    (β : (ZMod K → Ambient n) → ℝ) (T : Set (ZMod K → Ambient n))
    (𝒲 𝒲' : Set (Om n K)) (Z₀ : Set (ZMod N → Ambient n))
    (ψ₀ : Descent (Om n N) (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)) : Prop := by
  subst K
  exact SharedRoot F (G₁ := G₁) (G₂ := G₂) ψ a Γ Wrest a₀ b₀ c₀ 𝒰 U W β T 𝒲 𝒲' Z₀ ψ₀

set_option maxHeartbeats 2000000 in
theorem label_pack_half_root_reidx {K : ℕ} [NeZero K] (hK : m * N = K) (hn : 1 ≤ n) (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (a : ZMod (m * N)) (ha : a + a = 0) (d₁ : Fin b → ℝ) (d₂ : Fin p → ℝ)
    (hd₁ : ∀ i, d₁ i * d₁ i = 1) (hd₂ : ∀ i, d₂ i * d₂ i = 1)
    (h₁ : ∀ z i, G₁ (rotA N (red m N a) z) i = d₁ i • rotV m N a (G₁ z i))
    (h₂ : ∀ z i, G₂ (rotA N (red m N a) z) i = d₂ i • rotV m N a (G₂ z i))
    {𝒪 : Set (ZMod N → Ambient n)} (h𝒪 : IsOpen 𝒪) (h𝒪s : 𝒪 ⊆ smoothSet m N F)
    (hneg : ∀ z ∈ 𝒪, Neg (normalForm m N F z) (G₁ z) ∧ Neg (-normalForm m N F z) (G₂ z))
    (h𝒪nz : ∀ z ∈ 𝒪, ∀ j, z j ≠ 0)
    {Γ : Set (ZMod N → Ambient n)} (hΓ : IsCompact Γ) (hΓ𝒪 : Γ ⊆ 𝒪)
    (hΓτ : ∀ z ∈ Γ, rotA N (red m N a) z ∈ Γ)
    (hiso : ∀ z ∈ 𝒪, fderiv ℝ (pen F N (1 / m)) z = 0 → z ∈ Γ)
    {a₀ b₀ : ℝ}
    (hΓval : ∀ z ∈ Γ, a₀ < (m : ℝ) ^ 2 * pen F N (1 / m) z ∧ (m : ℝ) ^ 2 * pen F N (1 / m) z < b₀)
    (hroot : ∀ κ : ℝ, 0 < κ → ∃ V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n,
      ContDiff ℝ ∞ V₀ ∧ HasCompactSupport V₀ ∧ tsupport V₀ ⊆ regSet F N (1 / m) ∧
      (∀ z, ‖V₀ z‖ ≤ κ) ∧
      (∀ z ∈ regSet F N (1 / m), fderiv ℝ (pen F N (1 / m)) z (V₀ z) ≤ 0) ∧
      ∀ z ∈ regSet F N (1 / m), a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z →
        (m : ℝ) ^ 2 * pen F N (1 / m) z ≤ b₀ → fderiv ℝ (pen F N (1 / m)) z ≠ 0 →
        fderiv ℝ (pen F N (1 / m)) z (V₀ z) < 0)
    (hKr : IsCompact {z : Om n N | a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ∧
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀})
    (hbandreg : ∀ Q : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 ≤ b₀ → Q.1 ∈ regSet F N (1 / m))
    {Wrest : Set (Om n N)} (hWrest : IsOpen Wrest) {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hWΓ : ∀ Q ∈ Wrest, Q.1 ∉ thickening δ₁ Γ)
    (hrcrit : ∀ Q : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 ≤ b₀ → fderiv ℝ (pen F N (1 / m)) Q.1 = 0 →
        Q.1 ∈ Γ ∨ Q ∈ Wrest)
    {𝒰 : Set (ZMod K → Ambient n)} (h𝒰 : IsOpen 𝒰) (hΓ𝒰 : ∀ z ∈ Γ, reidx hK (iterA m N z) ∈ 𝒰)
    {c₀ : ℝ} (ha₀c₀ : a₀ < c₀) (hc₀b₀ : c₀ < b₀)
    (hΓc₀ : ∀ z ∈ Γ, (m : ℝ) ^ 2 * pen F N (1 / m) z = c₀)
    (hrval : ∀ Q : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 →
      (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 ≤ b₀ → fderiv ℝ (pen F N (1 / m)) Q.1 = 0 →
        (m : ℝ) ^ 2 * pen F N (1 / m) Q.1 = c₀)
    {η : ℝ} (hη : 0 < η) :
    ∃ (U : Set (ZMod K → Ambient n))
      (W : (ZMod K → Ambient n) → ZMod K → Ambient n)
      (β : (ZMod K → Ambient n) → ℝ) (C T : Set (ZMod K → Ambient n))
      (𝒲 𝒲' : Set (Om n K)) (Z₀ : Set (ZMod N → Ambient n))
      (ψ₀ : Descent (Om n N) (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)),
      SharedRootAt F (G₁ := G₁) (G₂ := G₂) hK ψ a Γ Wrest a₀ b₀ c₀ 𝒰 U W β T 𝒲 𝒲' Z₀ ψ₀ ∧
      (∀ y, rotA K (reidxShift hK a) y ∈ U ↔ y ∈ U) ∧
      (∀ y, rotA K (reidxShift hK a) y ∈ T ↔ y ∈ T) ∧
      (∀ y ∈ U, W (rotA K (reidxShift hK a) y) = rotA K (reidxShift hK a) (W y)) ∧
      (∀ y, β (rotA K (reidxShift hK a) y) = β y) ∧
      (∀ Q, (⟨rotA K (reidxShift hK a) Q.1, Finsler.AmbientSymmetry.rotA_ne_zero K _ Q.2⟩ : Om n K) ∈ 𝒲 ↔ Q ∈ 𝒲) ∧
      (∀ Q, (⟨rotA K (reidxShift hK a) Q.1, Finsler.AmbientSymmetry.rotA_ne_zero K _ Q.2⟩ : Om n K) ∈ 𝒲' ↔ Q ∈ 𝒲') ∧
      (∀ z, rotA N (red m N a) z ∈ Z₀ ↔ z ∈ Z₀) ∧
      IsOpen U ∧ U ⊆ 𝒰 ∧ U ⊆ regSet F K 1 ∧ ContDiffOn ℝ ∞ W U ∧
      (∀ y ∈ U, fderiv ℝ (pen F K 1) y (W y) ≤ 0) ∧
      (∀ y ∈ U, y ∉ C → fderiv ℝ (pen F K 1) y (W y) < 0) ∧
      IsCompact T ∧ T ⊆ U ∧ tsupport β ⊆ T ∧ (∀ y, DifferentiableAt ℝ β y) ∧ (∀ y, |β y| ≤ η) ∧
      (∀ y ∈ tsupport β, fderiv ℝ (fun y => pen F K 1 y + β y) y (W y) ≤ 0) ∧
      (∀ y ∈ tsupport β, y ∉ C → fderiv ℝ (fun y => pen F K 1 y + β y) y (W y) < 0) ∧
      IsOpen 𝒲 ∧ IsOpen 𝒲' ∧ 𝒲' ⊆ 𝒲 ∧ (∀ Q ∈ 𝒲, Q.1 ∈ T) ∧
      (∀ Q : Om n K, Q.1 ∈ C → Q ∈ 𝒲') ∧ (∀ z ∈ Γ, reidx hK (iterA m N z) ∈ T) ∧
      (∀ y ∈ C, pen F K 1 y = c₀ ∧ β y = 0) ∧
      IsOpen {z : Om n N | z.1 ∈ Z₀} ∧ Disjoint {z : Om n N | z.1 ∈ Z₀} Wrest ∧
      (∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → z ∉ {z : Om n N | z.1 ∈ Z₀} ∪ Wrest →
        (m : ℝ) ^ 2 * pen F N (1 / m) (ψ₀.flow 1 z).1 < (m : ℝ) ^ 2 * pen F N (1 / m) z.1) ∧
      (∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
        (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≠ c₀ →
        (m : ℝ) ^ 2 * pen F N (1 / m) (ψ₀.flow 1 z).1 < (m : ℝ) ^ 2 * pen F N (1 / m) z.1) ∧
      ∀ {V : (ZMod K → Ambient n) → ZMod K → Ambient n} {KL : ℝ≥0}
        (hL : LipschitzWith KL V) (hV0 : ∀ P : ZMod K → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
        {g : (ZMod K → Ambient n) → ℝ} {O : Set (ZMod K → Ambient n)}
        (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
        (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0),
        (∀ y ∈ T, V y = W y) → (∀ y ∈ T, g y = pen F K 1 y + β y) →
        ∀ {a₀a b₀a : ℝ}, a₀a < c₀ → c₀ < b₀a → Continuous (fun Q : Om n K => g Q.1) →
        IsCompact {Q : Om n K | a₀a ≤ g Q.1 ∧ g Q.1 ≤ b₀a} →
        ∀ {R : Set (Om n K)}, IsOpen R → Disjoint 𝒲 R →
        (∀ Q : Om n K, a₀a ≤ g Q.1 → g Q.1 ≤ b₀a → Q ∉ 𝒲' ∪ R →
          g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) →
        ∃ d : ℝ, 0 < d ∧ ∀ a c T : ℝ, 1 ≤ T → a < c₀ → c₀ < c → c - a < d →
          (∀ k : ℕ, Module.finrank (ZMod 2) (H (triv (pairOf (partY_sub_partU
              (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) 𝒲 a c T))) (k + b)) =
            Module.finrank (ZMod 2) (H (triv (pairOf (inter_subset_left :
              baseP (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1) {z : Om n N | z.1 ∈ Z₀} c ∩
                baseO ψ₀ a T ⊆
              baseP (fun z : Om n N => (m : ℝ) ^ 2 * pen F N (1 / m) z.1)
                {z : Om n N | z.1 ∈ Z₀} c))) k)) ∧
          (∀ k : ℕ, k < b → ∀ x : H (triv (pairOf (partY_sub_partU
              (fun Q : Om n K => g Q.1) (descentOf hL hV0 hg hsupp hle) 𝒲 a c T))) k,
            x = 0) := by
  subst hK
  exact Finsler.LabelPackRoot.label_pack_half_root F hn hG₁ hG₂ ψ a ha d₁ d₂ hd₁ hd₂ h₁ h₂ h𝒪 h𝒪s hneg h𝒪nz
    hΓ hΓ𝒪 hΓτ hiso hΓval hroot hKr hbandreg hWrest hδ₁ hWΓ hrcrit h𝒰 hΓ𝒰
    ha₀c₀ hc₀b₀ hΓc₀ hrval hη

end

end Finsler.LabelPackRootReidx

