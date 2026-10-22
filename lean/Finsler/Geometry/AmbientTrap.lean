module

public import Finsler.Geometry.LabelTransport
public import Finsler.Topology.OrbitTrap

/-! Trapping of whole orbits in the ambient label sets. The ambient label set of (Z₀, ρ) is open
if Z₀ and U are open (the frame coordinates are continuous where they are invertible). With the
margin of the small label set (Z₀', ρ') inside the large one (Z₀, ρ) up to the time one (v0.120),
the trapping of whole orbits of v0.118 applies: on a compact band of the deformed energy on
which the time-one map decreases it strictly outside the small label set and an open set R
disjoint from the large one, whole orbits of points of the large label set below b which are
not taken below a in time T ≥ 1 stay in it up to the time T, for all sufficiently tight cuts.
This is the trapping hypothesis of the transport of a label to the product model. -/

@[expose] public section

namespace Finsler.AmbientTrap

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform Finsler.LabelTransport
open Finsler.AmbientDescent Finsler.FlowLens Finsler.OrbitTrap
open scoped Topology ContDiff NNReal

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))
  (V₀ : (ZMod N → Ambient n) → ZMod N → Ambient n)

/-- **The ambient label sets are open.** -/
theorem labelSetA_isOpen (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₀ : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ : ℝ}
    (hZ₀ : IsOpen Z₀) (hU : IsOpen U) : IsOpen (labelSetA m N G₁ G₂ ψ Z₀ U ρ) := by
  have hA : IsOpen {Q : ZMod (m * N) → Ambient n | IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)) ∧
      zOf m N Q ∈ Z₀ ∧ ‖eucX (xiOf m N G₁ G₂ ψ Q)‖ < ρ ∧ ‖eucY (xiOf m N G₁ G₂ ψ Q)‖ < ρ ∧
      Q ∈ U} := by
    rw [isOpen_iff_mem_nhds]
    rintro Q ⟨hu, hz, hx, hy, hQ⟩
    have hxi : ContinuousAt (xiOf m N G₁ G₂ ψ) Q :=
      (xiOf_contDiffAt m N G₁ G₂ ψ hG₁ hG₂ hu).continuousAt
    have h1 : ∀ᶠ Q' in 𝓝 Q, IsUnit (matA m N G₁ G₂ ψ (zOf m N Q')) :=
      (isOpen_isUnit m N G₁ G₂ ψ hG₁ hG₂).mem_nhds hu
    have h2 : ∀ᶠ Q' in 𝓝 Q, zOf m N Q' ∈ Z₀ :=
      (zOf (n := n) m N).continuous.continuousAt.preimage_mem_nhds (hZ₀.mem_nhds hz)
    have h3 : ∀ᶠ Q' in 𝓝 Q, ‖eucX (xiOf m N G₁ G₂ ψ Q')‖ < ρ :=
      ((continuous_norm.comp eucX.continuous).continuousAt.comp hxi).eventually (gt_mem_nhds hx)
    have h4 : ∀ᶠ Q' in 𝓝 Q, ‖eucY (xiOf m N G₁ G₂ ψ Q')‖ < ρ :=
      ((continuous_norm.comp eucY.continuous).continuousAt.comp hxi).eventually (gt_mem_nhds hy)
    have h5 : ∀ᶠ Q' in 𝓝 Q, Q' ∈ U := hU.mem_nhds hQ
    filter_upwards [h1, h2, h3, h4, h5] with Q' a1 a2 a3 a4 a5
    exact ⟨a1, a2, a3, a4, a5⟩
  exact hA.preimage continuous_subtype_val

variable (F : ReversibleMetric n)
  {V : (ZMod (m * N) → Ambient n) → ZMod (m * N) → Ambient n} {K : ℝ≥0} (hL : LipschitzWith K V)
  (hV0 : ∀ P : ZMod (m * N) → Ambient n, V P ≠ 0 → ∀ j, P j ≠ 0)
  {g : (ZMod (m * N) → Ambient n) → ℝ} {O : Set (ZMod (m * N) → Ambient n)}
  (hg : ∀ P ∈ O, DifferentiableAt ℝ g P) (hsupp : ∀ P, V P ≠ 0 → P ∈ O)
  (hle : ∀ P ∈ O, fderiv ℝ g P (V P) ≤ 0)
  {K₀ : ℝ≥0} (hL₀ : LipschitzWith K₀ V₀)

include hL₀ in
/-- **Trapping in the ambient label set.** -/
theorem exists_ambient_trap (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z₀ Z₀' : Set (ZMod N → Ambient n)} {U : Set (ZMod (m * N) → Ambient n)} {ρ ρ' κ : ℝ}
    (hZ₀' : IsOpen Z₀') (hUo : IsOpen U) (hZZ : Z₀' ⊆ Z₀) (hρρ : ρ' ≤ ρ)
    (hZρ : ∀ z ∈ Z₀, ∀ (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)), ‖u‖ < ρ →
      ‖y‖ < ρ → IsUnit (matA m N G₁ G₂ ψ z) ∧ coord m N G₁ G₂ (z, unE u y) ∈ U ∧
        ∀ j, coord m N G₁ G₂ (z, unE u y) j ≠ 0)
    (hU : ∀ Q ∈ U, V Q = splitW m N G₁ G₂ ψ V₀ Q) (hκ : ∀ z, ‖V₀ z‖ ≤ κ)
    (hZ : ∀ z ∈ Z₀', ∀ z', ‖z' - z‖ ≤ κ → z' ∈ Z₀) (hρ : ρ' * Real.exp 1 ≤ ρ)
    {R : Set (Om n (m * N))} (hR : IsOpen R)
    (hdis : Disjoint (labelSetA m N G₁ G₂ ψ Z₀ U ρ) R)
    (hgc : Continuous fun Q : Om n (m * N) => g Q.1) {a₀ b₀ : ℝ}
    (hK : IsCompact {Q : Om n (m * N) | a₀ ≤ g Q.1 ∧ g Q.1 ≤ b₀})
    (hstrict : ∀ Q : Om n (m * N), a₀ ≤ g Q.1 → g Q.1 ≤ b₀ →
      Q ∉ labelSetA m N G₁ G₂ ψ Z₀' U ρ' ∪ R →
      g ((descentOf hL hV0 hg hsupp hle).flow 1 Q).1 < g Q.1) :
    ∃ d : ℝ, 0 < d ∧ ∀ a c T : ℝ, a₀ ≤ a → c ≤ b₀ → c - a < d → 1 ≤ T →
      ∀ w, w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ → g w.1 < c →
        a ≤ g ((descentOf hL hV0 hg hsupp hle).flow T w).1 → ∀ s, 0 ≤ s → s ≤ T →
          (descentOf hL hV0 hg hsupp hle).flow s w ∈ labelSetA m N G₁ G₂ ψ Z₀ U ρ := by
  have hsub : labelSetA m N G₁ G₂ ψ Z₀' U ρ' ⊆ labelSetA m N G₁ G₂ ψ Z₀ U ρ := by
    rintro Q ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, hZZ h2, lt_of_lt_of_le h3 hρρ, lt_of_lt_of_le h4 hρρ, h5⟩
  obtain ⟨d, hd, htrap⟩ := exists_orbit_trap (descentOf hL hV0 hg hsupp hle) hgc
    (labelSetA_isOpen m N G₁ G₂ ψ hG₁ hG₂ hZ₀' hUo) hR hsub hdis hK hstrict
    (fun Q hQ s hs hs1 => ambient_margin m N G₁ G₂ ψ V₀ hL hV0 hg hsupp hle hL₀ hG₁ hG₂ hZρ hU
      hκ hZ hρ Q hQ s hs hs1)
  exact ⟨d, hd, fun a c T ha hc hac hT w hw hwc hwa s hs hsT =>
    htrap a c T ha hc hac hT w hw hwc hwa s hs hsT⟩

end

end Finsler.AmbientTrap
