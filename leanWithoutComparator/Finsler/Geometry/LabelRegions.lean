module

public import Finsler.Geometry.LabelTransport
public import Finsler.Analysis.NormalExpansion

/-! The regions of a label. The cylinder region R(Z, ρ) of a set Z of root polygons consists of
the ambient polygons with nonzero vertices whose frame coordinates are invertible, with root
polygon in Z and coefficients of norm below ρ; it is open if Z is. Its points are frame
coordinates of points of Z × ball ρ, so it lies in the compact image of closure Z × closedBall ρ,
and this image lies in the region of a larger set and radius when the frame coordinates are
invertible and the vertices are nonzero there. By the tube lemma the vertices of coord(z, ξ)
are nonzero for z in a compact set of root polygons with nonzero vertices and ξ small. Euclidean
coefficients of norm below ρ have sup norm below ρ, so the label sets of v0.120 over a subset of
Z with radius at most ρ satisfy the regularity hypothesis of the label shift. -/

@[expose] public section

namespace Finsler.LabelRegions

open Module Filter Set Metric
open Finsler.SphereGeometry Finsler.Geometry
open Finsler.PolygonIterate Finsler.AmbientPenalty Finsler.AmbientSymmetry
open Finsler.SymmetricBlocks Finsler.AmbientNormalIndex Finsler.DefiniteFrames
open Finsler.CircleFrameField Finsler.FrameCoordinates Finsler.FrameInverse
open Finsler.AmbientSplitField Finsler.LabelAmbient Finsler.LabelDeform Finsler.LabelTransport
open Finsler.NormalExpansion
open scoped Topology ContDiff NNReal

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} (m N : ℕ) [NeZero m] [NeZero N] {b p : ℕ}
  (G₁ : (ZMod N → Ambient n) → Fin b → normal (rotL (n := n) m N) m)
  (G₂ : (ZMod N → Ambient n) → Fin p → normal (rotL (n := n) m N) m)
  (ψ : normal (rotL (n := n) m N) m ≃L[ℝ] (Fin b → ℝ) × (Fin p → ℝ))

/-- The cylinder region of a set of root polygons. -/
def region (Z : Set (ZMod N → Ambient n)) (ρ : ℝ) : Set (ZMod (m * N) → Ambient n) :=
  {Q | IsUnit (matA m N G₁ G₂ ψ (zOf m N Q)) ∧ zOf m N Q ∈ Z ∧ ‖xiOf m N G₁ G₂ ψ Q‖ < ρ ∧
    ∀ j, Q j ≠ 0}

/-- The compact image of closure Z × closedBall ρ under the frame coordinates. -/
def tube (Z : Set (ZMod N → Ambient n)) (ρ : ℝ) : Set (ZMod (m * N) → Ambient n) :=
  coord m N G₁ G₂ '' (closure Z ×ˢ closedBall (0 : (Fin b → ℝ) × (Fin p → ℝ)) ρ)

variable {G₁ G₂}

theorem region_isOpen (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z : Set (ZMod N → Ambient n)} (hZ : IsOpen Z) (ρ : ℝ) :
    IsOpen (region m N G₁ G₂ ψ Z ρ) := by
  rw [isOpen_iff_mem_nhds]
  rintro Q ⟨hu, hz, hx, hnz⟩
  have hxi : ContinuousAt (xiOf m N G₁ G₂ ψ) Q :=
    (xiOf_contDiffAt m N G₁ G₂ ψ hG₁ hG₂ hu).continuousAt
  have h1 : ∀ᶠ Q' in 𝓝 Q, IsUnit (matA m N G₁ G₂ ψ (zOf m N Q')) :=
    (isOpen_isUnit m N G₁ G₂ ψ hG₁ hG₂).mem_nhds hu
  have h2 : ∀ᶠ Q' in 𝓝 Q, zOf m N Q' ∈ Z :=
    (zOf (n := n) m N).continuous.continuousAt.preimage_mem_nhds (hZ.mem_nhds hz)
  have h3 : ∀ᶠ Q' in 𝓝 Q, ‖xiOf m N G₁ G₂ ψ Q'‖ < ρ :=
    (continuous_norm.continuousAt.comp hxi).eventually (gt_mem_nhds hx)
  have h4 : ∀ᶠ Q' in 𝓝 Q, ∀ j, Q' j ≠ 0 := by
    have hO : IsOpen {Q : ZMod (m * N) → Ambient n | ∀ j, Q j ≠ 0} := by
      have he : {Q : ZMod (m * N) → Ambient n | ∀ j, Q j ≠ 0} =
          ⋂ j, (fun Q : ZMod (m * N) → Ambient n => Q j) ⁻¹' {y | y ≠ 0} := by
        ext Q
        simp
      rw [he]
      exact isOpen_iInter_of_finite fun j => isOpen_ne.preimage (continuous_apply j)
    exact hO.mem_nhds hnz
  filter_upwards [h1, h2, h3, h4] with Q' a1 a2 a3 a4
  exact ⟨a1, a2, a3, a4⟩

theorem region_subset_tube {Z : Set (ZMod N → Ambient n)} {ρ : ℝ} :
    region m N G₁ G₂ ψ Z ρ ⊆ tube m N G₁ G₂ Z ρ := by
  rintro Q ⟨hu, hz, hx, -⟩
  exact ⟨(zOf m N Q, xiOf m N G₁ G₂ ψ Q), ⟨subset_closure hz,
    mem_closedBall_zero_iff.mpr hx.le⟩, coord_inverse m N G₁ G₂ ψ hu⟩

theorem tube_isCompact (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {Z : Set (ZMod N → Ambient n)} (hZ : Bornology.IsBounded Z) (ρ : ℝ) :
    IsCompact (tube m N G₁ G₂ Z ρ) :=
  ((hZ.isCompact_closure).prod (isCompact_closedBall _ _)).image
    (coord_contDiff m N G₁ G₂ hG₁ hG₂).continuous

/-- The tube lies in the region of a larger set and radius. -/
theorem tube_subset_region {Z Z' : Set (ZMod N → Ambient n)} {ρ ρ' : ℝ}
    (hZZ : closure Z ⊆ Z') (hρ : ρ < ρ')
    (hu : ∀ z ∈ closure Z, IsUnit (matA m N G₁ G₂ ψ z))
    (hnz : ∀ z ∈ closure Z, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ ρ →
      ∀ j, coord m N G₁ G₂ (z, ξ) j ≠ 0) :
    tube m N G₁ G₂ Z ρ ⊆ region m N G₁ G₂ ψ Z' ρ' := by
  rintro _ ⟨⟨z, ξ⟩, ⟨hz, hξ⟩, rfl⟩
  obtain ⟨h1, h2⟩ := inverse_coord m N G₁ G₂ ψ (hu z hz) ξ
  have hξ' : ‖ξ‖ ≤ ρ := mem_closedBall_zero_iff.mp hξ
  refine ⟨?_, ?_, ?_, hnz z hz ξ hξ'⟩
  · rw [h1]
    exact hu z hz
  · rw [h1]
    exact hZZ hz
  · rw [h2]
    exact lt_of_le_of_lt hξ' hρ

/-- **The tube lemma for nonzero vertices.** -/
theorem exists_nonzero_tube (hG₁ : ContDiff ℝ ∞ G₁) (hG₂ : ContDiff ℝ ∞ G₂)
    {K : Set (ZMod N → Ambient n)} (hK : IsCompact K) (hKnz : ∀ z ∈ K, ∀ j, z j ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ ≤ R →
      ∀ j, coord m N G₁ G₂ (z, ξ) j ≠ 0 := by
  set 𝒪 : Set ((ZMod N → Ambient n) × ((Fin b → ℝ) × (Fin p → ℝ))) :=
    coord m N G₁ G₂ ⁻¹' {Q | ∀ j, Q j ≠ 0} with h𝒪def
  have hO : IsOpen {Q : ZMod (m * N) → Ambient n | ∀ j, Q j ≠ 0} := by
    have he : {Q : ZMod (m * N) → Ambient n | ∀ j, Q j ≠ 0} =
        ⋂ j, (fun Q : ZMod (m * N) → Ambient n => Q j) ⁻¹' {y | y ≠ 0} := by
      ext Q
      simp
    rw [he]
    exact isOpen_iInter_of_finite fun j => isOpen_ne.preimage (continuous_apply j)
  have h𝒪 : IsOpen 𝒪 := hO.preimage (coord_contDiff m N G₁ G₂ hG₁ hG₂).continuous
  have hsub : ∀ z ∈ K, (z, (0 : (Fin b → ℝ) × (Fin p → ℝ))) ∈ 𝒪 := by
    intro z hz j
    rw [coord_zero]
    exact hKnz z hz _
  obtain ⟨R, hR, htube⟩ := exists_tube h𝒪 hK hsub
  exact ⟨R, hR, fun z hz ξ hξ => htube z hz ξ hξ⟩

omit [NeZero m] [NeZero N] in
/-- Euclidean coefficients below ρ have sup norm below ρ. -/
theorem norm_unE_lt {u : EuclideanSpace ℝ (Fin b)} {y : EuclideanSpace ℝ (Fin p)} {ρ : ℝ}
    (hu : ‖u‖ < ρ) (hy : ‖y‖ < ρ) : ‖unE u y‖ < ρ := by
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hu
  have h1 : ‖(EuclideanSpace.equiv (Fin b) ℝ) u‖ ≤ ‖u‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    exact PiLp.norm_apply_le u i
  have h2 : ‖(EuclideanSpace.equiv (Fin p) ℝ) y‖ ≤ ‖y‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
    exact PiLp.norm_apply_le y i
  unfold unE
  rw [Prod.norm_def]
  exact max_lt (lt_of_le_of_lt h1 hu) (lt_of_le_of_lt h2 hy)

/-- **Regularity of the label sets over a region.** -/
theorem label_regular {Z Z₀ : Set (ZMod N → Ambient n)} {ρ ρ₁ : ℝ} (hZ₀ : Z₀ ⊆ Z)
    (hρ : ρ ≤ ρ₁) (hu : ∀ z ∈ Z, IsUnit (matA m N G₁ G₂ ψ z))
    (hnz : ∀ z ∈ Z, ∀ ξ : (Fin b → ℝ) × (Fin p → ℝ), ‖ξ‖ < ρ₁ →
      ∀ j, coord m N G₁ G₂ (z, ξ) j ≠ 0) :
    ∀ z ∈ Z₀, ∀ (u : EuclideanSpace ℝ (Fin b)) (y : EuclideanSpace ℝ (Fin p)), ‖u‖ < ρ →
      ‖y‖ < ρ → IsUnit (matA m N G₁ G₂ ψ z) ∧
        coord m N G₁ G₂ (z, unE u y) ∈ region m N G₁ G₂ ψ Z ρ₁ ∧
        ∀ j, coord m N G₁ G₂ (z, unE u y) j ≠ 0 := by
  intro z hz u y hu' hy'
  have hξ : ‖unE u y‖ < ρ₁ := lt_of_lt_of_le (norm_unE_lt hu' hy') hρ
  have hzZ := hZ₀ hz
  obtain ⟨h1, h2⟩ := inverse_coord m N G₁ G₂ ψ (hu z hzZ) (unE u y)
  have hnz' := hnz z hzZ (unE u y) hξ
  refine ⟨hu z hzZ, ⟨?_, ?_, ?_, hnz'⟩, hnz'⟩
  · rw [h1]
    exact hu z hzZ
  · rw [h1]
    exact hzZ
  · rw [h2]
    exact hξ

end

end Finsler.LabelRegions
