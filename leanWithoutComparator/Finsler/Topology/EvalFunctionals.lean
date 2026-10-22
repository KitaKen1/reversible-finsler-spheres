module

public import Finsler.Topology.FunctionalCover

/-! Evaluation functionals which are odd under the half rotation. For a time t and a vector e
the functional d_{t,e}(γ) = ⟨γ(t) − γ(t + 1/2), e⟩ is continuous on H¹ loops, changes sign under
the half rotation, and the reversal takes d_{t,e} to d_{−t,e}. Hence d_{t,e} + d_{−t,e} is odd
under the half rotation and even under the reversal, and d_{t,e} − d_{−t,e} is odd under
both. If both are smaller than η in absolute value at a loop, so is d_{t,e}. -/

@[expose] public section

namespace Finsler.EvalFunctionals

open Set Topology
open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse Finsler.BorelK
open Finsler.MilnorHomotopy Finsler.MilnorEquivariance Finsler.MilnorContinuity
open Finsler.FunctionalCover

noncomputable section

variable {n : ℕ}

/-- The reversal on points at all real times. -/
theorem pt_reverse_neg (u : SphereLoop n) (x : ℝ) : pt (reverseSphere u) x = pt u (-x) := by
  have hfl := Int.floor_le x
  have hfl' := Int.lt_floor_add_one x
  have hyI : x - ⌊x⌋ ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  rw [pt_eq_of_sub_int (reverseSphere u) (x := x) (y := x - ⌊x⌋) (-⌊x⌋) (by push_cast; ring),
    pt_reverse _ hyI]
  exact pt_eq_of_sub_int u (x := 1 - (x - ⌊x⌋)) (y := -x) (-(1 + ⌊x⌋)) (by push_cast; ring)

theorem pt_coe_continuous (t : ℝ) : Continuous fun u : SphereLoop n => (pt u t : Ambient n) := by
  have h : Continuous fun p : ℝ × SphereLoop n => pt p.2 t :=
    pt_continuous (g := fun _ => t) continuous_const
  have h2 : Continuous fun u : SphereLoop n => ((0 : ℝ), u) :=
    continuous_const.prodMk continuous_id
  have h3 : Continuous ((fun p : ℝ × SphereLoop n => pt p.2 t) ∘
      fun u : SphereLoop n => ((0 : ℝ), u)) := h.comp h2
  exact continuous_subtype_val.comp h3

/-- The difference of a loop and its half rotation at time t, paired with e. -/
def diff (t : ℝ) (e : Ambient n) (u : SphereLoop n) : ℝ :=
  inner ℝ ((pt u t : Ambient n) - (pt u (t + 1 / 2) : Ambient n)) e

theorem diff_continuous (t : ℝ) (e : Ambient n) : Continuous (diff (n := n) t e) :=
  ((pt_coe_continuous t).sub (pt_coe_continuous (t + 1 / 2))).inner continuous_const

theorem diff_half (t : ℝ) (e : Ambient n) (u : SphereLoop n) :
    diff t e (half +ᵥ u) = -diff t e u := by
  have h1 : pt (half +ᵥ u) t = pt u (t + 1 / 2) := pt_vadd u (1 / 2) t
  have h2 : pt (half +ᵥ u) (t + 1 / 2) = pt u t := by
    have h := pt_vadd u (1 / 2) (t + 1 / 2)
    rw [show t + 1 / 2 + 1 / 2 = t + 1 by ring, pt_add_one] at h
    exact h
  unfold diff
  rw [h1, h2, ← inner_neg_left, neg_sub]

theorem diff_reverse (t : ℝ) (e : Ambient n) (u : SphereLoop n) :
    diff t e (reverseSphere u) = diff (-t) e u := by
  have h1 : pt (reverseSphere u) t = pt u (-t) := pt_reverse_neg u t
  have h2 : pt (reverseSphere u) (t + 1 / 2) = pt u (-t + 1 / 2) := by
    rw [pt_reverse_neg]
    exact pt_eq_of_sub_int u (x := -(t + 1 / 2)) (y := -t + 1 / 2) 1 (by push_cast; ring)
  unfold diff
  rw [h1, h2]

/-- The functional d_{t,e} + d_{−t,e}: odd under the half rotation, even under the reversal. -/
def evenFunctional (t : ℝ) (e : Ambient n) : OddFunctional n where
  ψ u := diff t e u + diff (-t) e u
  continuous := (diff_continuous t e).add (diff_continuous (-t) e)
  half_odd u := by rw [diff_half, diff_half, neg_add]
  rev_parity := Or.inl fun u => by rw [diff_reverse, diff_reverse, neg_neg, add_comm]

/-- The functional d_{t,e} − d_{−t,e}: odd under the half rotation and under the reversal. -/
def oddFunctional (t : ℝ) (e : Ambient n) : OddFunctional n where
  ψ u := diff t e u - diff (-t) e u
  continuous := (diff_continuous t e).sub (diff_continuous (-t) e)
  half_odd u := by rw [diff_half, diff_half, neg_sub_neg, neg_sub]
  rev_parity := Or.inr fun u => by rw [diff_reverse, diff_reverse, neg_neg, neg_sub]

/-- If the even and the odd functional of (t, e) are smaller than η at a loop, so is the
difference functional. -/
theorem abs_diff_lt {t : ℝ} {e : Ambient n} {u : SphereLoop n} {η : ℝ}
    (h1 : |(evenFunctional t e).ψ u| < η) (h2 : |(oddFunctional t e).ψ u| < η) :
    |diff t e u| < η := by
  have h1' : |diff t e u + diff (-t) e u| < η := h1
  have h2' : |diff t e u - diff (-t) e u| < η := h2
  rw [abs_lt] at h1' h2' ⊢
  constructor <;> linarith [h1'.1, h1'.2, h2'.1, h2'.2]

end

end Finsler.EvalFunctionals
