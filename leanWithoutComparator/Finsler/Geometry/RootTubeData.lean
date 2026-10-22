module

public import Finsler.Geometry.LabelFull
public import Finsler.Geometry.RootFlowFixed
public import Finsler.Geometry.RootField
public import Finsler.Geometry.InvariantLabelChoice
public import Finsler.Geometry.LabelRegionRotation
public import Finsler.Geometry.LabelSetRotation
public import Finsler.Geometry.RootFieldRotation

/-! Retain the actual bounded equivariant root ODE, nested margins and label tube witnesses. -/

@[expose] public section

namespace Finsler.LabelRootData

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


structure RootTubeData (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
    (a : ZMod (m * N)) (Γ : Set (ZMod N → Ambient n)) (Wrest : Set (Om n N))
    (a₀ b₀ c₀ : ℝ) (𝒰 : Set (ZMod (m * N) → Ambient n)) where
  lower : a₀ < c₀
  upper : c₀ < b₀
  circle_value : ∀ z ∈ Γ, (m : ℝ) ^ 2 * pen F N (1 / m) z = c₀
  rest_open : IsOpen Wrest
  compact_band : IsCompact {z : Om n N | a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ∧
    (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀}
  V : (ZMod N → Ambient n) → ZMod N → Ambient n
  K : ℝ≥0
  lipschitz : LipschitzWith K V
  nonzero : ∀ z, V z ≠ 0 → ∀ j, z j ≠ 0
  diff : ∀ z ∈ regSet F N (1 / m),
    DifferentiableAt ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z
  supp : ∀ z, V z ≠ 0 → z ∈ regSet F N (1 / m)
  nonpos : ∀ z ∈ regSet F N (1 / m),
    fderiv ℝ (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) z (V z) ≤ 0
  κ : ℝ
  ρ : ℝ
  κ_pos : 0 < κ
  ρ_pos : 0 < ρ
  bound : ∀ z, ‖V z‖ ≤ κ
  Z : Set (ZMod N → Ambient n)
  Z₀ : Set (ZMod N → Ambient n)
  Z_open : IsOpen Z
  Z₀_open : IsOpen Z₀
  circle_mem : Γ ⊆ Z
  subset : Z ⊆ Z₀
  Z_invariant : ∀ z, rotA N (red m N a) z ∈ Z ↔ z ∈ Z
  Z₀_invariant : ∀ z, rotA N (red m N a) z ∈ Z₀ ↔ z ∈ Z₀
  margin : ∀ z ∈ Z, ∀ z', ‖z' - z‖ ≤ κ → z' ∈ Z₀
  root_nonzero : ∀ z ∈ Z₀, ∀ j, z j ≠ 0
  U : Set (ZMod (m * N) → Ambient n)
  U_open : IsOpen U
  U_subset : U ⊆ 𝒰
  tube : ∀ z ∈ Z₀, ∀ (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)),
    ‖u‖ < ρ → ‖y‖ < ρ → IsUnit (matA m N G₁ G₂ ψ z) ∧
      coord m N G₁ G₂ (z, unE u y) ∈ U ∧ ∀ j, coord m N G₁ G₂ (z, unE u y) j ≠ 0
  disjoint : Disjoint {z : Om n N | z.1 ∈ Z₀} Wrest
  fixed : ∀ t (z : Om n N), 0 ≤ t → rotA N (red m N a) z.1 = z.1 →
    rotA N (red m N a) ((descentOf lipschitz nonzero diff supp nonpos).flow t z).1 =
      ((descentOf lipschitz nonzero diff supp nonpos).flow t z).1
  small_strict : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
    (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → z ∉ {z : Om n N | z.1 ∈ Z} ∪ Wrest →
    (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf lipschitz nonzero diff supp nonpos).flow 1 z).1 <
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1
  value_strict : ∀ z : Om n N, a₀ ≤ (m : ℝ) ^ 2 * pen F N (1 / m) z.1 →
    (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≤ b₀ → (m : ℝ) ^ 2 * pen F N (1 / m) z.1 ≠ c₀ →
    (m : ℝ) ^ 2 * pen F N (1 / m) ((descentOf lipschitz nonzero diff supp nonpos).flow 1 z).1 <
      (m : ℝ) ^ 2 * pen F N (1 / m) z.1

end

end Finsler.LabelRootData
