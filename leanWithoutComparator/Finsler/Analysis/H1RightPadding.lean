module

public import Finsler.Analysis.H1PaddingContinuity
public import Finsler.Topology.ConstantJoinHomotopy

/-! Remove a terminal constant interval by reversing the verified initial-padding construction. -/

@[expose] public section

namespace Finsler.H1RightPadding

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.H1ConstantPadding Finsler.H1PaddingTime Finsler.H1PaddingContinuity
open Finsler.H1LoopJoin Finsler.SobolevConcat Finsler.H1ConcatContinuity
open Finsler.H1FiberBase Finsler.SobolevEnergy Finsler.CompactH1Alignment Set
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 600000

def padded {n : ℕ} (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) (u : SphereLoop n) : SphereLoop n :=
  reverseSphere (H1ConstantPadding.padded b hb0 hb1 (reverseSphere u))

theorem padded_zero {n : ℕ} (u : SphereLoop n) : padded 0 (by norm_num) (by norm_num) u = u := by
  rw [padded, H1ConstantPadding.padded_zero, reverseSphere_involutive]

theorem continuous_padded {n : ℕ} :
    Continuous (fun z : Parameters × SphereLoop n => padded z.1 z.1.property.1 z.1.property.2 z.2) := by
  have he : Continuous (fun z : Parameters × SphereLoop n => (z.1, reverseSphere z.2)) :=
    continuous_fst.prodMk ((reverseSphere_continuous n).comp continuous_snd)
  exact (reverseSphere_continuous n).comp (H1PaddingContinuity.continuous_padded.comp he)

theorem energy_padded {n : ℕ} (F : ReversibleMetric n) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (u : SphereLoop n) : SobolevEnergy.energy F (padded b hb0 hb1 u) =
      SobolevEnergy.energy F u / (1 - b) := by
  rw [padded, energy_reverseSphere, H1ConstantPadding.energy_padded, energy_reverseSphere]

theorem representative_padded {n : ℕ} (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (u : SphereLoop n) (t : ClosedInterval) :
    continuousRepresentative ((padded b hb0 hb1 u).data : Space n) t =
      continuousRepresentative (u.data : Space n) (1 - time b (1 - (t : ℝ))) := by
  change continuousRepresentative (reverseData
    ((H1ConstantPadding.padded b hb0 hb1 (reverseSphere u)).data : Space n)) t = _
  rw [representative_reverseData _ t.property]
  have hp := H1PaddingTime.representative_padded b hb0 hb1 (reverseSphere u) (reflectionInterval t)
  change continuousRepresentative
      ((H1ConstantPadding.padded b hb0 hb1 (reverseSphere u)).data : Space n) (reflection t) =
    continuousRepresentative ((reverseSphere u).data : Space n) (time b (reflection t)) at hp
  rw [hp]
  exact representative_reverseData (u.data : Space n)
    (time_mem hb0 hb1 (reflection_mem_Icc t.property))

theorem reflected_time_left {b t : ℝ} (hb1 : b < 1) (ht : t ≤ 1 - b) :
    1 - time b (1 - t) = (1 - b)⁻¹ * t := by
  rw [time_of_ge hb1 (by linarith)]
  field_simp [(sub_pos.mpr hb1).ne'] <;> ring

theorem reflected_time_right {b t : ℝ} (hb1 : b < 1) (ht : 1 - b ≤ t) :
    1 - time b (1 - t) = 1 := by
  rw [time_of_le hb1 (by linarith), sub_zero]

theorem padded_join {n : ℕ} (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (u : SphereLoop n) :
    padded b hb0.le hb1 u =
      join (1 - b) (sub_pos.mpr hb1) (by linarith) u (constantSphereLoop (point u))
        (constant_matches u).symm := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  apply Subtype.ext
  change continuousRepresentative ((padded b hb0.le hb1 u).data : Space n) t =
    continuousRepresentative (concat (u.data : Space n) (constantData (point u : Ambient n))
      (sub_pos.mpr hb1) (by linarith)) t
  rw [representative_padded]
  by_cases ht : (t : ℝ) ≤ 1 - b
  · rw [reflected_time_left hb1 ht,
      representative_concat_left _ _ (sub_pos.mpr hb1) (by linarith) ⟨t.property.1, ht⟩]
  · have hge : 1 - b ≤ (t : ℝ) := (lt_of_not_ge ht).le
    have hm : continuousRepresentative (u.data : Space n) 1 =
        continuousRepresentative (constantData (point u : Ambient n)) 0 :=
      end_match u (constantSphereLoop (point u)) (constant_matches u).symm
    rw [reflected_time_right hb1 hge,
      representative_concat_right _ _ (sub_pos.mpr hb1) (by linarith) hm ⟨hge, t.property.2⟩,
      continuousRepresentative_constantData _ (right_time_mem (by linarith : 1 - b < 1)
        t.property hge)]
    exact periodic_trace u

theorem padded_join_at {n : ℕ} (a b : ℝ) (hb0 : 0 < b) (hb1 : b < 1)
    (ha0 : 0 < a) (ha1 : a < 1) (he : 1 - b = a) (u : SphereLoop n) :
    padded b hb0.le hb1 u = join a ha0 ha1 u (constantSphereLoop (point u))
      (constant_matches u).symm := by
  subst a
  exact padded_join b hb0 hb1 u

theorem padded_mem_cut {n : ℕ} (F : ReversibleMetric n) {p q b : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hb0 : 0 ≤ b) (hb : b ≤ q / (q + p))
    (u : SphereLoop n) (hu : u ∈ Finsler.BorelLoop.lev F p) :
    padded b hb0 (lt_of_le_of_lt hb ((div_lt_one (add_pos hq hp)).mpr (by linarith))) u ∈
      Finsler.BorelLoop.lev F (p + q) := by
  apply (Finsler.Birkhoff.mem_lev_iff (add_pos hp hq) _).mpr
  have hu' : SobolevEnergy.energy F (reverseSphere u) < p ^ 2 := by
    rw [energy_reverseSphere]
    exact (Finsler.Birkhoff.mem_lev_iff hp u).mp hu
  rw [padded, energy_reverseSphere]
  exact (H1ConstantPadding.energy_padded_cut F hq hp hb0 hb (reverseSphere u) hu').trans_eq
    (by rw [add_comm q p])

end
end Finsler.H1RightPadding
