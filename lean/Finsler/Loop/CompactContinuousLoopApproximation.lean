module

public import Finsler.Loop.ShortPolygonC0Approximation
public import Finsler.Geometry.RoundMetric

/-! Uniformly approximate EVERY loop of a compact ordinary family by
an actual continuous strong-H1 family on one finite subdivision. The
true sampled vertices and constant loops are retained. -/

@[expose] public section
namespace Finsler.CompactContinuousLoopApproximation
open CategoryTheory TopologicalSpace Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.PolygonModel Finsler.PolygonLoop
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1600000

theorem exists_close_approximation {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F)
    (hconst : ∀ P : Sphere n, ∀ t, S.sc P P t = P)
    (K : Compacts (ContinuousLoopModel.space n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      ∃ e : TopCat.of K ⟶ Loops n,
        (∀ u : K, dist (ContinuousLoopModel.inclusion n (e u)) u.val < ε) ∧
        (∀ u : K, PolygonSampling.samplePoly N (e u) = CompactContinuousLoopSampling.sample N u.val) ∧
        (∀ (u : K) (P : Sphere n), u.val = ContinuousLoopModel.constantMap n P → e u = constantSphereLoop P) := by
  obtain ⟨ρ, hρ, -, hseg⟩ := ContinuousSegmentFamily.exists_uniform_close S hconst (by positivity : 0 < ε / 4)
  obtain ⟨M, hM, hmod⟩ := CompactContinuousLoopSampling.exists_spacing K (lt_min hρ (by positivity : 0 < ε / 4))
  obtain ⟨R, hR, hshort⟩ := CompactContinuousLoopSampling.exists_short_samples K S.pos
  refine ⟨max M R, hM.trans_le (le_max_left _ _), fun N hN _ => ?_⟩
  let hq := hshort N ((le_max_right _ _).trans hN)
  let e := CompactContinuousLoopPolygon.approximation S K N hq
  refine ⟨e, ?_, CompactContinuousLoopPolygon.sample_approximation S K N hq,
    CompactContinuousLoopPolygon.approximation_constant S hconst K N hq⟩
  intro u
  have hb : dist (ContinuousLoopModel.inclusion n (e u)) u.val ≤ ε / 2 := by
    apply (ContinuousMap.dist_le (half_pos hε).le).mpr
    intro x
    have h := ShortPolygonC0Approximation.pointwise_error S N u.val (hq u) hseg
      (hmod N ((le_max_left _ _).trans hN) u) x
    change dist (ContinuousLoopModel.inclusion n (e u) x) (u.val x) < 2 * (ε / 4) at h
    linarith
  exact hb.trans_lt (half_lt_self hε)

theorem exists_close_replacements (n : ℕ) (K : Compacts (ContinuousLoopModel.space n)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ [NeZero N],
      ∃ e : TopCat.of K ⟶ Loops n,
        (∀ u : K, dist (ContinuousLoopModel.inclusion n (e u)) u.val < ε) ∧
        (∀ u : K, PolygonSampling.samplePoly N (e u) = CompactContinuousLoopSampling.sample N u.val) ∧
        (∀ (u : K) (P : Sphere n), u.val = ContinuousLoopModel.constantMap n P → e u = constantSphereLoop P) := by
  obtain ⟨S, hS⟩ := ContinuousSegmentFamily.exists_segmentData_const (roundMetric n)
  exact exists_close_approximation S hS K hε

end
end Finsler.CompactContinuousLoopApproximation
