module

public import Finsler.Analysis.H1ConstantPadding

/-! The actual padding time and a uniform value estimate including zero padding.
This estimate controls values, not the strong-L2 convergence of velocities. -/

@[expose] public section

namespace Finsler.H1PaddingTime

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.H1ConstantPadding
open Finsler.SobolevConcat Finsler.H1LoopJoin Finsler.H1ConcatContinuity
open Finsler.H1FiberBase Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 400000

def time (a t : ℝ) : ℝ := max 0 ((t - a) / (1 - a))

theorem time_mem {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    time a t ∈ Icc (0 : ℝ) 1 := by
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  exact (div_le_one (sub_pos.mpr ha1)).mpr (by linarith [ht.2])

theorem time_zero {t : ℝ} (ht : 0 ≤ t) : time 0 t = t := by
  simp only [time, sub_zero, div_one, max_eq_right ht]

theorem time_of_le {a t : ℝ} (ha1 : a < 1) (ht : t ≤ a) : time a t = 0 := by
  exact max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr ha1).le)

theorem time_of_ge {a t : ℝ} (ha1 : a < 1) (ht : a ≤ t) :
    time a t = (t - a) / (1 - a) :=
  max_eq_right (div_nonneg (sub_nonneg.mpr ht) (sub_pos.mpr ha1).le)

theorem rightMap_eq_time {a t : ℝ} (ha1 : a < 1) (ht : a ≤ t) :
    rightMap a t = time a t := by
  rw [time_of_ge ha1 ht]
  unfold rightMap
  ring

theorem time_close {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |time a t - t| ≤ a := by
  by_cases h : t ≤ a
  · rw [time_of_le ha1 h, zero_sub, abs_neg, abs_of_nonneg ht.1]
    exact h
  · have hlt : a < t := lt_of_not_ge h
    rw [time_of_ge ha1 hlt.le]
    have hle : (t - a) / (1 - a) ≤ t := by
      apply (div_le_iff₀ (sub_pos.mpr ha1)).mpr
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ht.2)]
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hlo : t - a ≤ (t - a) / (1 - a) := by
      apply (le_div_iff₀ (sub_pos.mpr ha1)).mpr
      nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hlt.le)]
    linarith

theorem representative_padded {n : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (u : SphereLoop n) (t : ClosedInterval) :
    continuousRepresentative ((padded a ha0 ha1 u).data : Space n) t =
      continuousRepresentative (u.data : Space n) (time a t) := by
  by_cases hz : a = 0
  · subst a
    rw [padded_zero, time_zero t.property.1]
  · have hp : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hz)
    rw [padded_pos hp ha1]
    change continuousRepresentative
      (concat (constantData (point u : Ambient n)) (u.data : Space n) hp ha1) t = _
    by_cases ht : (t : ℝ) ≤ a
    · rw [representative_concat_left _ _ hp ha1 ⟨t.property.1, ht⟩,
        continuousRepresentative_constantData _ (left_time_mem hp t.property ht), time_of_le ha1 ht]
      rfl
    · have hgt : a < (t : ℝ) := lt_of_not_ge ht
      have hm : continuousRepresentative (constantData (point u : Ambient n)) 1 =
          continuousRepresentative (u.data : Space n) 0 :=
        end_match (constantSphereLoop (point u)) u (constant_matches u)
      exact (representative_concat_right (constantData (point u : Ambient n))
        (u.data : Space n) hp ha1 hm ⟨hgt.le, t.property.2⟩).trans
        (congrArg (continuousRepresentative (u.data : Space n)) (rightMap_eq_time ha1 hgt.le))

theorem representative_padding_bound {n : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (u : SphereLoop n) (t : ClosedInterval) :
    ‖continuousRepresentative ((padded a ha0 ha1 u).data : Space n) t -
      continuousRepresentative (u.data : Space n) t‖ ≤
        Real.sqrt a * ‖velocity (u.data : Space n)‖ := by
  rw [representative_padded]
  exact (continuousRepresentative_holder_half (u.data : Space n) t.property
    (time_mem ha0 ha1 t.property)).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (time_close ha0 ha1 t.property)) (norm_nonneg _))

end
end Finsler.H1PaddingTime

