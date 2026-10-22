module

public import Finsler.Analysis.H1JoinContinuity
public import Finsler.Topology.BorelEvaluation
public import Finsler.Analysis.H1FiberBase
public import Finsler.Topology.SphereUnitCandidate

/-! Actual constant-first padding and uniform control of the original energy cut.
The joint strong-H1 continuity at zero padding is still a separate analytic task. -/

@[expose] public section

namespace Finsler.H1ConstantPadding

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev
open Finsler.CompactH1Alignment Finsler.H1LoopJoin Finsler.H1JoinContinuity
open Finsler.H1FiberBase Finsler.BorelEvaluation Finsler.BorelLoop Set
open Finsler.SobolevEnergy
open scoped Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 300000

theorem constant_matches {n : ℕ} (u : SphereLoop n) :
    basepoint (constantSphereLoop (point u)) = basepoint u :=
  congrArg Subtype.val (eval_constant (point u))

def padded {n : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (u : SphereLoop n) : SphereLoop n :=
  if h : a = 0 then u else join a (lt_of_le_of_ne ha0 (Ne.symm h)) ha1
    (constantSphereLoop (point u)) u (constant_matches u)

theorem padded_zero {n : ℕ} (u : SphereLoop n) : padded 0 (by norm_num) (by norm_num) u = u := by
  simp [padded]

theorem padded_pos {n : ℕ} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (u : SphereLoop n) :
    padded a ha0.le ha1 u = join a ha0 ha1 (constantSphereLoop (point u)) u
      (constant_matches u) := by
  simp only [padded, dite_eq_right ha0.ne']

theorem padded_basepoint {n : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (u : SphereLoop n) :
    basepoint (padded a ha0 ha1 u) = basepoint u := by
  by_cases h : a = 0
  · subst a
    rw [padded_zero]
  · rw [padded, dite_eq_right h, basepoint_join, constant_matches]

theorem energy_padded {n : ℕ} (F : ReversibleMetric n) (a : ℝ)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (u : SphereLoop n) :
    energy F (padded a ha0 ha1 u) = energy F u / (1 - a) := by
  by_cases h : a = 0
  · subst a
    simp only [padded_zero, sub_zero, div_one]
  · rw [padded, dite_eq_right h, energy_join, energy_constantSphereLoop, zero_div, zero_add]

theorem energy_padded_le {n : ℕ} (F : ReversibleMetric n) {a A : ℝ}
    (ha0 : 0 ≤ a) (haA : a ≤ A) (hA1 : A < 1) (u : SphereLoop n) :
    energy F (padded a ha0 (lt_of_le_of_lt haA hA1) u) ≤ energy F u / (1 - A) := by
  rw [energy_padded]
  exact div_le_div_of_nonneg_left (energy_nonneg F u) (sub_pos.mpr hA1) (by linarith)

theorem energy_padded_cut {n : ℕ} (F : ReversibleMetric n) {p q a : ℝ}
    (hp : 0 < p) (hq : 0 < q) (ha0 : 0 ≤ a) (ha : a ≤ p / (p + q))
    (u : SphereLoop n) (hu : energy F u < q ^ 2) :
    energy F (padded a ha0 (lt_of_le_of_lt ha
      ((div_lt_one (add_pos hp hq)).mpr (by linarith))) u) < (p + q) ^ 2 := by
  have hA : p / (p + q) < 1 := (div_lt_one (add_pos hp hq)).mpr (by linarith)
  have hd : 1 - p / (p + q) = q / (p + q) := by field_simp <;> ring
  calc
    _ ≤ energy F u / (1 - p / (p + q)) := energy_padded_le F ha0 ha hA u
    _ < q ^ 2 / (1 - p / (p + q)) :=
      (div_lt_div_iff_of_pos_right (sub_pos.mpr hA)).mpr hu
    _ = q * (p + q) := by rw [hd]; field_simp <;> ring
    _ < (p + q) ^ 2 := by nlinarith [mul_pos hp (add_pos hp hq)]

theorem padded_mem_cut {n : ℕ} (F : ReversibleMetric n) {p q a : ℝ}
    (hp : 0 < p) (hq : 0 < q) (ha0 : 0 ≤ a) (ha : a ≤ p / (p + q))
    (u : SphereLoop n) (hu : u ∈ lev F q) :
    padded a ha0 (lt_of_le_of_lt ha ((div_lt_one (add_pos hp hq)).mpr (by linarith))) u ∈
      lev F (p + q) := by
  apply (Finsler.Birkhoff.mem_lev_iff (add_pos hp hq) _).mpr
  exact energy_padded_cut F hp hq ha0 ha u ((Finsler.Birkhoff.mem_lev_iff hq u).mp hu)

theorem continuous_padded_fixed {n : ℕ} {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Continuous (padded (n := n) a ha0.le ha1) := by
  let e : SphereLoop n → composable n := fun u =>
    ⟨(constantSphereLoop (point u), u), constant_matches u⟩
  have he : Continuous e :=
    (((SphereTopClass.constantSphereLoop_continuous n).comp continuous_point).prodMk continuous_id).subtype_mk _
  exact ((continuous_join (n := n) a ha0 ha1).comp he).congr (fun u => (padded_pos ha0 ha1 u).symm)

end
end Finsler.H1ConstantPadding

