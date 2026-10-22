module

public import Finsler.Loop.CompactContinuousLoopPolygon

/-! Actual C0 error of the genuine H1 broken-geodesic replacement.
Control both the short segment and the original loop on each sampled
piece, including the final piece through the circle endpoint. -/

@[expose] public section
namespace Finsler.ShortPolygonC0Approximation
open CategoryTheory TopologicalSpace Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.BorelLoop
open Finsler.PolygonModel Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PiecewiseC1
open Finsler.SobolevCircleRepresentative
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000
local notation "Circ" => SobolevCircleRepresentative.Circle

theorem pointwise_error {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) (N : ℕ) [NeZero N]
    (u : ContinuousLoopModel.space n) (hq : ShortPolygon S.δ (CompactContinuousLoopSampling.sample N u))
    {η ε : ℝ}
    (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < η → ∀ t : ClosedInterval, ‖S.sc P Q t - P‖ < ε)
    (hmod : ∀ s t : ClosedInterval, |(t : ℝ) - s| ≤ 1 / N →
      dist (u ((s : ℝ) : Circ)) (u ((t : ℝ) : Circ)) < min η ε) (x : Circ) :
    dist (ContinuousLoopModel.inclusion n
      (ShortPolygonH1Model.broken S N ⟨CompactContinuousLoopSampling.sample N u, hq⟩) x) (u x) < 2 * ε := by
  have hN := Nat.pos_of_neZero N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let τ := circlePoint x
  let k := pieceIdx N τ
  have hk : k < N := pieceIdx_lt hN τ
  let s := sampleTime N (k : ZMod N)
  have hs : (s : ℝ) = (k : ℝ) / N := by
    simp only [s, sampleTime, ZMod.val_natCast_of_lt hk]
  let t : ClosedInterval := ⟨((k : ℝ) + 1) / N, by
    constructor
    · positivity
    · rw [div_le_one hNR]; exact_mod_cast hk⟩
  let P := CompactContinuousLoopSampling.sample N u (k : ZMod N)
  let Q := CompactContinuousLoopSampling.sample N u ((k : ZMod N) + 1)
  have hP : P = u ((s : ℝ) : Circ) := rfl
  have hQ : Q = u ((t : ℝ) : Circ) := CompactContinuousLoopSampling.sample_natCast_succ u hk
  have hst : |(t : ℝ) - s| ≤ 1 / N := by
    rw [hs]
    change |((k : ℝ) + 1) / N - (k : ℝ) / N| ≤ 1 / N
    rw [← sub_div, add_sub_cancel_left, abs_of_pos (by positivity : 0 < 1 / (N : ℝ))]
  have hPQ : ‖(Q : Ambient n) - P‖ < η := by
    rw [hP, hQ]
    have h := (hmod s t hst).trans_le (min_le_left _ _)
    simpa only [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using h
  have hpiece := mem_piece hN τ.property
  have hτ : |(τ : ℝ) - s| ≤ 1 / N := by
    rw [hs, abs_of_nonneg (sub_nonneg.mpr hpiece.1)]
    calc
      (τ : ℝ) - (k : ℝ) / N ≤ ((k : ℝ) + 1) / N - (k : ℝ) / N := sub_le_sub_right hpiece.2 _
      _ = 1 / N := by ring
  have hPx : ‖(P : Ambient n) - u x‖ < ε := by
    have h := (hmod s τ hτ).trans_le (min_le_right _ _)
    rw [show ((τ : ℝ) : Circ) = x from circlePoint_coe x] at h
    rw [hP]
    exact h
  have hc := hseg P Q hPQ ⟨pieceLoc N τ, pieceLoc_mem hN τ.property⟩
  change dist (sphereCircleMap (ShortPolygonH1Model.broken S N
    ⟨CompactContinuousLoopSampling.sample N u, hq⟩) x) (u x) < 2 * ε
  rw [sphereCircleMap_point]
  change ‖continuousRepresentative (polyLoop F S.seg hq) τ - u x‖ < 2 * ε
  rw [representative_polyLoop F S.seg hq τ.property]
  change ‖S.sc P Q (pieceLoc N τ) - u x‖ < 2 * ε
  have ht : ‖S.sc P Q (pieceLoc N τ) - u x‖ ≤
      ‖S.sc P Q (pieceLoc N τ) - P‖ + ‖(P : Ambient n) - u x‖ := by
    simpa only [dist_eq_norm] using dist_triangle (S.sc P Q (pieceLoc N τ)) (P : Ambient n) (u x : Ambient n)
  exact ht.trans_lt (by linarith)

end
end Finsler.ShortPolygonC0Approximation
