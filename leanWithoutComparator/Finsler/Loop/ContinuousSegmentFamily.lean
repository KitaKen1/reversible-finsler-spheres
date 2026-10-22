module

public import Finsler.Geometry.PolygonModel
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.ContinuousMap.Compact

/-! Actual short minimizing segments as a continuous family of C0
curves. The genuine diagonal identity is retained from SegmentCurves,
and compactness gives a uniform endpoint-to-curve closeness radius. -/

@[expose] public section
namespace Finsler.ContinuousSegmentFamily
open TopologicalSpace Topology
open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.PolygonModel
open scoped Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000

theorem exists_segmentData_const {n : ℕ} (F : ReversibleMetric n) :
    ∃ S : SegmentData F, ∀ P : Sphere n, ∀ t, S.sc P P t = P := by
  obtain ⟨δ₁, hδ₁, sc, sv, hseg, hunif, hrev, hconst, hpkg⟩ := SegmentCurves.exists_segment_curves F
  obtain ⟨δ₂, hδ₂, hsm⟩ := EnergySphereSmooth.exists_ambientMinEnergy_contDiffAt F
  refine ⟨SegmentData.mk (min δ₁ δ₂) (lt_min hδ₁ hδ₂) sc sv
    (fun P Q h => hseg P Q (h.trans_le (min_le_left _ _)))
    (fun P Q h => hunif P Q (h.trans_le (min_le_left _ _)))
    (fun P Q h t ht => (hrev P Q (h.trans_le (min_le_left _ _)) t ht).1)
    (fun T P Q hP h hT t ht => hpkg T P Q hP (h.trans_le (min_le_left _ _)) hT t ht)
    (fun P Q hne h => hsm P Q hne (h.trans_le (min_le_right _ _))), hconst⟩

abbrev nearPairs {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) :=
  {z : Sphere n × Sphere n // ‖(z.2 : Ambient n) - z.1‖ < S.δ}

def curve {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) (z : nearPairs S) :
    C(ClosedInterval, Ambient n) :=
  ⟨fun t => S.sc z.val.1 z.val.2 t, by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ((S.seg _ _ z.property).1 t t.property).continuousAt.comp continuous_subtype_val.continuousAt⟩

theorem curve_continuous {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) : Continuous (curve S) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hu := S.unif z₀.val.1 z₀.val.2 z₀.property (ε / 2) (half_pos hε)
  have hz := (continuous_subtype_val.continuousAt (x := z₀)).tendsto.eventually hu
  filter_upwards [hz] with z h
  rw [dist_eq_norm]
  have hb : ‖curve S z - curve S z₀‖ ≤ ε / 2 :=
    (ContinuousMap.norm_le _ (by positivity)).mpr (fun t => (h t t.property).1.le)
  exact hb.trans_lt (half_lt_self hε)

def closedPairs {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) : Set (Sphere n × Sphere n) :=
  {z | ‖(z.2 : Ambient n) - z.1‖ ≤ S.δ / 2}

theorem closedPairs_compact {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) :
    IsCompact (closedPairs S) :=
  (isClosed_le (continuous_subtype_val.comp continuous_snd |>.sub
    (continuous_subtype_val.comp continuous_fst) |>.norm) continuous_const).isCompact

def toNear {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) : closedPairs S → nearPairs S :=
  fun z => ⟨z.val, z.property.trans_lt (half_lt_self S.pos)⟩

theorem toNear_continuous {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F) : Continuous (toNear S) :=
  continuous_subtype_val.subtype_mk _

theorem exists_uniform_close {n : ℕ} {F : ReversibleMetric n} (S : SegmentData F)
    (hconst : ∀ P : Sphere n, ∀ t, S.sc P P t = P) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ > 0, ρ ≤ S.δ ∧ ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < ρ →
      ∀ t : ClosedInterval, ‖S.sc P Q t - P‖ < ε := by
  have : CompactSpace (closedPairs S) := isCompact_iff_compactSpace.mp (closedPairs_compact S)
  have hc := (curve_continuous S).comp (toNear_continuous S)
  obtain ⟨η, hη, hu⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  refine ⟨min (S.δ / 2) η, lt_min (half_pos S.pos) hη,
    (min_le_left _ _).trans (half_le_self S.pos.le), fun P Q hPQ t => ?_⟩
  let a : closedPairs S := ⟨(P, Q), hPQ.le.trans (min_le_left _ _)⟩
  let b : closedPairs S := ⟨(P, P), by
    change ‖(P : Ambient n) - P‖ ≤ S.δ / 2
    rw [sub_self, norm_zero]
    exact (half_pos S.pos).le⟩
  have hd : dist a b < η := by
    change max (dist P P) (dist Q P) < η
    rw [dist_self, max_eq_right dist_nonneg]
    exact hPQ.trans_le (min_le_right _ _)
  have hcurve := hu (a := a) (b := b) hd
  have hpoint : ‖S.sc P Q t - S.sc P P t‖ ≤ dist (curve S (toNear S a)) (curve S (toNear S b)) :=
    ContinuousMap.dist_apply_le_dist (f := curve S (toNear S a)) (g := curve S (toNear S b)) t
  rw [hconst P t] at hpoint
  exact hpoint.trans_lt hcurve

end
end Finsler.ContinuousSegmentFamily
