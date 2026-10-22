module

public import Finsler.Loop.CompactContinuousLoopSampling
public import Finsler.Loop.ShortPolygonH1Model

/-! Every actual compact ordinary continuous-loop family has genuine
continuous H1 polygon replacements on ONE finite subdivision. Vertices
are exact, and actual constant loops are preserved. No ordinary/H1
homology equivalence or nonzero UNIT pairing is assumed. -/

@[expose] public section
namespace Finsler.CompactContinuousLoopPolygon
open CategoryTheory TopologicalSpace Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.PolygonModel Finsler.PolygonLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000

def toPolygon {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F)
    (K : Compacts (ContinuousLoopModel.space n)) (N : ℕ)
    (hshort : ∀ u : K, ShortPolygon S.δ (CompactContinuousLoopSampling.sample N u.val)) :
    C(K, ShortPolygonH1Model.polygons S N) :=
  ⟨fun u => ⟨CompactContinuousLoopSampling.sample N u.val, hshort u⟩,
    ((CompactContinuousLoopSampling.sample_continuous n N).comp continuous_subtype_val).subtype_mk _⟩

def approximation {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F)
    (K : Compacts (ContinuousLoopModel.space n)) (N : ℕ) [NeZero N]
    (hshort : ∀ u : K, ShortPolygon S.δ (CompactContinuousLoopSampling.sample N u.val)) :
    TopCat.of K ⟶ Loops n :=
  TopCat.ofHom ⟨fun u => ShortPolygonH1Model.broken S N (toPolygon S K N hshort u),
    (ShortPolygonH1Model.broken_continuous S N).comp (toPolygon S K N hshort).continuous⟩

theorem sample_approximation {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F)
    (K : Compacts (ContinuousLoopModel.space n)) (N : ℕ) [NeZero N]
    (hshort : ∀ u : K, ShortPolygon S.δ (CompactContinuousLoopSampling.sample N u.val)) (u : K) :
    PolygonSampling.samplePoly N (approximation S K N hshort u) = CompactContinuousLoopSampling.sample N u.val :=
  ShortPolygonH1Model.sample_broken S N (toPolygon S K N hshort u)

theorem approximation_constant {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F)
    (hconst : ∀ P : Sphere n, ∀ t, S.sc P P t = P)
    (K : Compacts (ContinuousLoopModel.space n)) (N : ℕ) [NeZero N]
    (hshort : ∀ u : K, ShortPolygon S.δ (CompactContinuousLoopSampling.sample N u.val))
    (u : K) (P : Sphere n) (hu : u.val = ContinuousLoopModel.constantMap n P) :
    approximation S K N hshort u = constantSphereLoop P := by
  have hq : toPolygon S K N hshort u = ShortPolygonH1Model.constantPolygon S N P := by
    apply Subtype.ext
    change CompactContinuousLoopSampling.sample N u.val = fun _ => P
    rw [hu]
    rfl
  change ShortPolygonH1Model.broken S N (toPolygon S K N hshort u) = _
  rw [hq]
  exact ShortPolygonH1Model.broken_constant S N hconst P

theorem exists_approximation {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F)
    (hconst : ∀ P : Sphere n, ∀ t, S.sc P P t = P)
    (K : Compacts (ContinuousLoopModel.space n)) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      ∃ e : TopCat.of K ⟶ Loops n,
        (∀ u : K, PolygonSampling.samplePoly N (e u) = CompactContinuousLoopSampling.sample N u.val) ∧
        (∀ (u : K) (P : Sphere n), u.val = ContinuousLoopModel.constantMap n P → e u = constantSphereLoop P) := by
  obtain ⟨N₀, hN₀, hshort⟩ := CompactContinuousLoopSampling.exists_short_samples K S.pos
  refine ⟨N₀, hN₀, fun N hN _ => ⟨approximation S K N (hshort N hN), ?_, ?_⟩⟩
  · exact sample_approximation S K N (hshort N hN)
  · exact approximation_constant S hconst K N (hshort N hN)

end
end Finsler.CompactContinuousLoopPolygon
