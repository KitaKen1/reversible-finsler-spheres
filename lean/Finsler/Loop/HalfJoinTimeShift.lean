module

public import Finsler.Topology.JoinSplitHomotopy
public import Finsler.Analysis.IntervalH1CircleAction

/-! A genuine half-period time shift of a half-time H1 concatenation
is exactly the half-time concatenation with the two factors exchanged. -/

@[expose] public section
namespace Finsler.HalfJoinTimeShift
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.H1LoopJoin
open Finsler.CompactH1Alignment Finsler.H1FiberBase Finsler.SobolevEnergy
open Finsler.SobolevShift Finsler.SobolevCircleRepresentative Finsler.SobolevConcat
open Finsler.JoinSplitHomotopy Finsler.SobolevCircleAction Set
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1800000


theorem half_join {n : ℕ} (u v : SphereLoop n) (h : basepoint u = basepoint v) :
    shiftSphere (join (1 / 2) (by norm_num) (by norm_num) u v h) (1 / 2) =
      join (1 / 2) (by norm_num) (by norm_num) v u h.symm := by
  let w := join (1 / 2) (by norm_num) (by norm_num) u v h
  apply sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative (shiftData w.data (1 / 2)) t =
    continuousRepresentative (SobolevConcat.concat (v.data : Space n) (u.data : Space n) (by norm_num) (by norm_num)) t
  rw [representative_shiftData w.data (1 / 2) t.property]
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [realMap_eqOn w.data ⟨by linarith [t.property.1], by linarith⟩]
    change continuousRepresentative (SobolevConcat.concat (u.data : Space n) (v.data : Space n) (by norm_num) (by norm_num)) ((t : ℝ) + 1 / 2) = _
    rw [representative_concat_right _ _ (by norm_num) (by norm_num) (end_match u v h)
      ⟨by linarith [t.property.1], by linarith⟩,
      representative_concat_left _ _ (by norm_num) (by norm_num) ⟨t.property.1, ht⟩]
    congr 1
    norm_num [rightMap]
    ring
  · have he : (t : ℝ) + 1 / 2 = ((t : ℝ) - 1 / 2) + 1 := by ring
    rw [he, realMap_periodic w.data, realMap_eqOn w.data ⟨by linarith, by linarith [t.property.2]⟩]
    change continuousRepresentative (SobolevConcat.concat (u.data : Space n) (v.data : Space n) (by norm_num) (by norm_num)) ((t : ℝ) - 1 / 2) = _
    rw [representative_concat_left _ _ (by norm_num) (by norm_num) ⟨by linarith, by linarith [t.property.2]⟩,
      representative_concat_right _ _ (by norm_num) (by norm_num) (end_match v u h.symm) ⟨by linarith, t.property.2⟩]
    congr 1
    norm_num [rightMap]
    ring

end
end Finsler.HalfJoinTimeShift
