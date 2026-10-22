module

public import Finsler.Geometry.CircleLabelFields

/-! Invariant smooth cutoffs and common definite neighbourhoods of the entire actual sampled critical circle. -/

@[expose] public section

namespace Finsler.CircleRootCutoff

open Set Topology Finsler.SphereGeometry Finsler.Geometry Finsler.PolygonIterate
open Finsler.PolygonDescent
open Finsler.AmbientSymmetry Finsler.AmbientNormalIndex Finsler.SymmetricBlocks
open Finsler.CircleHalfRotation Finsler.CircleFrameField Finsler.GeodesicFrames
open scoped ContDiff

noncomputable section
set_option maxSynthPendingDepth 3

variable {n : ℕ} {F : ReversibleMetric n} (g : Finsler.Geodesics.ClosedGeodesic F)
  (s N : ℕ) [NeZero s] [NeZero N]

def rootCircle : Set (ZMod (s * (2 * N)) → Ambient n) :=
  (fun a => amb (rootFamily g s N a)) '' Icc (0 : ℝ) 1

omit [NeZero s] [NeZero N] in
theorem rootCircle_mem (a : ℝ) : amb (rootFamily g s N a) ∈ rootCircle g s N := by
  refine ⟨Int.fract a, ⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩, ?_⟩
  rw [rootFamily_fract]

theorem rootCircle_compact : IsCompact (rootCircle g s N) :=
  isCompact_Icc.image (rootFamily_continuous g s N)

theorem rootCircle_half (m : ℕ) {z : ZMod (s * (2 * N)) → Ambient n}
    (hz : z ∈ rootCircle g s N) :
    rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z ∈ rootCircle g s N := by
  obtain ⟨a, -, rfl⟩ := hz
  rw [← root_half_phase g m s N a]
  exact rootCircle_mem g s N _

variable {g s N} {m b p : ℕ} [NeZero m]
  (G₁ : SignedFrameField g s m N 1 b) (G₂ : SignedFrameField g s m N (-1) p)

theorem common_neighbourhood : IsOpen (G₁.U ∩ G₂.U) ∧ rootCircle g s N ⊆ G₁.U ∩ G₂.U ∧
    G₁.U ∩ G₂.U ⊆ smoothSet m (s * (2 * N)) F ∧
    (∀ z, rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z ∈ G₁.U ∩ G₂.U ↔
      z ∈ G₁.U ∩ G₂.U) ∧
    ∀ z ∈ G₁.U ∩ G₂.U,
      Finsler.DefiniteFrames.Neg (normalForm m (s * (2 * N)) F z) (G₁.G z) ∧
      Finsler.DefiniteFrames.Neg (-normalForm m (s * (2 * N)) F z) (G₂.G z) := by
  refine ⟨G₁.isOpen.inter G₂.isOpen, ?_, fun _ hz => G₁.subset_smooth hz.1, ?_, ?_⟩
  · rintro _ ⟨a, -, rfl⟩
    exact ⟨G₁.circle_mem a, G₂.circle_mem a⟩
  · intro z
    exact and_congr (G₁.invariant z) (G₂.invariant z)
  · intro z hz
    exact ⟨by simpa only [one_smul] using G₁.definite z hz.1,
      by simpa only [neg_one_smul] using G₂.definite z hz.2⟩

theorem exists_root_cutoff :
    ∃ (χ : (ZMod (s * (2 * N)) → Ambient n) → ℝ)
      (W : Set (ZMod (s * (2 * N)) → Ambient n)),
      ContDiff ℝ ∞ χ ∧ (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ G₁.U ∩ G₂.U ∧
      (∀ z, χ (rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z) = χ z) ∧
      IsOpen W ∧ rootCircle g s N ⊆ W ∧
      (∀ z, rotA (s * (2 * N)) (red m (s * (2 * N)) (halfIndex m s N)) z ∈ W ↔ z ∈ W) ∧
      ∀ z ∈ W, χ z = 1 := by
  obtain ⟨hU, hΓ, -, hUτ, -⟩ := common_neighbourhood G₁ G₂
  exact Finsler.InvariantCutoff.exists_invariant_cutoff _ (root_half_involutive m s N)
    (rootCircle_compact g s N) hU hΓ (fun _ hz => rootCircle_half g s N m hz)
    (fun z hz => (hUτ z).mpr hz)

end

end Finsler.CircleRootCutoff
