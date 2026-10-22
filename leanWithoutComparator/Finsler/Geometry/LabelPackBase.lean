module

public import Finsler.Geometry.LabelFull
public import Finsler.Geometry.RootField
public import Finsler.Geometry.InvariantLabelChoice
public import Finsler.Geometry.LabelRegionRotation
public import Finsler.Geometry.LabelSetRotation
public import Finsler.Geometry.RootFieldRotation

/-! Root thickenings and equality reindexing used by the shared label construction. -/

@[expose] public section

namespace Finsler.LabelPack

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

/-- **The thickenings of a compact set.** If Z' ⊆ thickening ε Γ and κ + ε ≤ ε', every point at
distance at most κ from Z' lies in thickening ε' Γ. -/
theorem margin_thickening {E : Type*} [PseudoMetricSpace E] {Γ : Set E} {ε ε' κ : ℝ}
    (hκ : κ + ε < ε') {z z' : E} (hz : z ∈ thickening ε Γ) (hz' : dist z' z ≤ κ) :
    z' ∈ thickening ε' Γ := by
  obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.mp hz
  exact mem_thickening_iff.mpr ⟨y, hy, by linarith [dist_triangle z' z y]⟩

omit [NeZero m] in
/-- **The open band set around the root circle.** -/
theorem exists_band_thickening {𝒪 : Set (ZMod N → Ambient n)} (h𝒪 : IsOpen 𝒪)
    (h𝒪r : 𝒪 ⊆ regSet F N (1 / m)) {Γ : Set (ZMod N → Ambient n)}
    (hΓ𝒪 : Γ ⊆ 𝒪) {a₀ b₀ : ℝ}
    (hΓval : ∀ z ∈ Γ, a₀ < (m : ℝ) ^ 2 * pen F N (1 / m) z ∧ (m : ℝ) ^ 2 * pen F N (1 / m) z < b₀)
    {𝒰 : Set (ZMod (m * N) → Ambient n)} (h𝒰 : IsOpen 𝒰) (hΓ𝒰 : ∀ z ∈ Γ, iterA m N z ∈ 𝒰) :
    ∃ 𝒪' : Set (ZMod N → Ambient n), IsOpen 𝒪' ∧ Γ ⊆ 𝒪' ∧ 𝒪' ⊆ 𝒪 ∧
      (∀ z ∈ 𝒪', a₀ < (m : ℝ) ^ 2 * pen F N (1 / m) z ∧ (m : ℝ) ^ 2 * pen F N (1 / m) z < b₀) ∧
      ∀ z ∈ 𝒪', iterA m N z ∈ 𝒰 := by
  have hc : ContinuousOn (fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) 𝒪 := fun z hz =>
    ((h𝒪r hz).2.continuousAt.const_mul _).continuousWithinAt
  set 𝒪' := 𝒪 ∩ ((fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) ⁻¹' Ioo a₀ b₀) ∩
    (iterA (n := n) m N) ⁻¹' 𝒰 with h𝒪'def
  have h1 : IsOpen (𝒪 ∩ ((fun z => (m : ℝ) ^ 2 * pen F N (1 / m) z) ⁻¹' Ioo a₀ b₀)) :=
    hc.isOpen_inter_preimage h𝒪 isOpen_Ioo
  refine ⟨𝒪', h1.inter (h𝒰.preimage (iterA (n := n) m N).continuous), fun z hz =>
    ⟨⟨hΓ𝒪 hz, hΓval z hz⟩, hΓ𝒰 z hz⟩, fun z hz => hz.1.1, fun z hz => hz.1.2, fun z hz => hz.2⟩

/-- Reindexing ambient polygons along an equality of vertex numbers. -/
def reidx {K : ℕ} (h : m * N = K) (Q : ZMod (m * N) → Ambient n) : ZMod K → Ambient n :=
  cast (congrArg (fun k => ZMod k → Ambient n) h) Q

omit [NeZero m] [NeZero N] in
theorem reidx_rfl (Q : ZMod (m * N) → Ambient n) : reidx (rfl : m * N = m * N) Q = Q := rfl

/-- Transport a rotation index along an equality of vertex counts. -/
def reidxShift {K : ℕ} (h : m * N = K) (a : ZMod (m * N)) : ZMod K :=
  cast (congrArg ZMod h) a


end

end Finsler.LabelPack
