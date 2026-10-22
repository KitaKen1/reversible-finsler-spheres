module

public import Finsler.Geometry.PolygonSampling
public import Finsler.Analysis.PrimitiveParts

/-! The straightening homotopy between a loop and the broken geodesic of its samples. On every
piece [k/N,(k+1)/N] the part of width τ/N centred at the midpoint is replaced by the short segment
between its end points; τ = 0 gives the loop and τ = 1 the broken geodesic of the samples. This
file defines the value and velocity of the homotopy and describes the value on the parts. -/

@[expose] public section

namespace Finsler.MilnorHomotopy

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevEnergy Finsler.PolygonLoop Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.PiecewiseC1 Finsler.SobolevCircleRepresentative Finsler.SobolevOfPrimitive
open Finsler.PrimitiveParts Finsler.SobolevAffine Finsler.AmbientLagrangian
open Finsler.SphereDistance (minEnergy pathsBetween minEnergy_le)
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- The left end of the straightened part of piece k. -/
@[irreducible] def leftEnd (N : ℕ) (τ : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + 1 / 2 - τ / 2) / N

/-- The right end of the straightened part of piece k. -/
@[irreducible] def rightEnd (N : ℕ) (τ : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + 1 / 2 + τ / 2) / N

/-- The sphere point of a loop at a real time. -/
def pt (u : SphereLoop n) (x : ℝ) : Sphere n :=
  sphereCircleMap u (x : SobolevCircleRepresentative.Circle)

theorem pt_coe (u : SphereLoop n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (pt u x : Ambient n) = continuousRepresentative (u.data : Space n) x := by
  unfold pt
  rw [sphereCircleMap_val]
  exact circleMap_coe u.data hx

/-- The segment parameter of a time in the straightened part. -/
def segParam (N : ℕ) (τ t : ℝ) : ℝ := (pieceLoc N t - (1 / 2 - τ / 2)) / τ

/-- The value of the straightening homotopy. -/
def homVal (sc : Sphere n → Sphere n → ℝ → Ambient n) (N : ℕ) (τ : ℝ) (u : SphereLoop n)
    (t : ℝ) : Ambient n :=
  if |pieceLoc N t - 1 / 2| ≤ τ / 2 then
    sc (pt u (leftEnd N τ (pieceIdx N t))) (pt u (rightEnd N τ (pieceIdx N t))) (segParam N τ t)
  else continuousRepresentative (u.data : Space n) t

/-- The velocity of the straightening homotopy. -/
def homVel (sv : Sphere n → Sphere n → ℝ → Ambient n) (N : ℕ) (τ : ℝ) (u : SphereLoop n)
    (t : ℝ) : Ambient n :=
  if |pieceLoc N t - 1 / 2| < τ / 2 then
    ((N : ℝ) / τ) •
      sv (pt u (leftEnd N τ (pieceIdx N t))) (pt u (rightEnd N τ (pieceIdx N t))) (segParam N τ t)
  else velocity (u.data : Space n) t

/-- The rescaled segment on the straightened part of piece k. -/
def segC (sc : Sphere n → Sphere n → ℝ → Ambient n) (N : ℕ) (τ : ℝ) (u : SphereLoop n) (k : ℕ)
    (t : ℝ) : Ambient n :=
  sc (pt u (leftEnd N τ k)) (pt u (rightEnd N τ k)) ((N : ℝ) / τ * (t - leftEnd N τ k))

/-- Its velocity. -/
def segV (sv : Sphere n → Sphere n → ℝ → Ambient n) (N : ℕ) (τ : ℝ) (u : SphereLoop n) (k : ℕ)
    (t : ℝ) : Ambient n :=
  ((N : ℝ) / τ) •
    sv (pt u (leftEnd N τ k)) (pt u (rightEnd N τ k)) ((N : ℝ) / τ * (t - leftEnd N τ k))

/-- The break points of the homotopy: k/N and the two ends of the straightened part of piece k. -/
@[irreducible] def brk (N : ℕ) (τ : ℝ) (j : ℕ) : ℝ :=
  if j % 3 = 0 then ((j / 3 : ℕ) : ℝ) / N
  else if j % 3 = 1 then leftEnd N τ (j / 3) else rightEnd N τ (j / 3)

section Ends

variable {N : ℕ} {τ : ℝ}

theorem leftEnd_ge (hN : (0 : ℝ) < N) (hτ : τ ≤ 1) (k : ℕ) : (k : ℝ) / N ≤ leftEnd N τ k := by
  unfold leftEnd
  apply div_le_div_of_nonneg_right _ hN.le
  linarith

theorem leftEnd_le_rightEnd (hN : (0 : ℝ) < N) (hτ : 0 ≤ τ) (k : ℕ) :
    leftEnd N τ k ≤ rightEnd N τ k := by
  unfold leftEnd rightEnd
  apply div_le_div_of_nonneg_right _ hN.le
  linarith

theorem rightEnd_le (hN : (0 : ℝ) < N) (hτ : τ ≤ 1) (k : ℕ) :
    rightEnd N τ k ≤ ((k : ℝ) + 1) / N := by
  unfold rightEnd
  apply div_le_div_of_nonneg_right _ hN.le
  linarith

theorem rightEnd_sub_leftEnd (k : ℕ) : rightEnd N τ k - leftEnd N τ k = τ / N := by
  unfold leftEnd rightEnd
  rw [div_sub_div_same]
  congr 1
  ring

theorem piece_mem_Icc {k : ℕ} (hk : k < N) (hN : (0 : ℝ) < N) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) / N) (((k : ℝ) + 1) / N)) : t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_trans (by positivity) ht.1
  · have : ((k : ℝ) + 1) / N ≤ 1 := by
      rw [div_le_one hN]
      exact_mod_cast hk
    exact ht.2.trans this

theorem piece_le_one (hN : (0 : ℝ) < N) {k : ℕ} (hk : k < N) : ((k : ℝ) + 1) / N ≤ 1 := by
  rw [div_le_one hN]
  exact_mod_cast hk

theorem rightEnd_eq_leftEnd (hτ : τ = 0) (k : ℕ) : rightEnd N τ k = leftEnd N τ k := by
  subst hτ
  unfold rightEnd leftEnd
  ring

theorem loc_of_mem {k : ℕ} (hk : k < N) {t : ℝ}
    (ht : t ∈ Ico ((k : ℝ) / N) (((k : ℝ) + 1) / N)) : pieceLoc N t = (N : ℝ) * t - k := by
  unfold pieceLoc
  rw [pieceIdx_eq hk ht]

theorem pieceLoc_zero : pieceLoc N 0 = 0 := by
  unfold pieceLoc pieceIdx
  simp

theorem pieceLoc_one (hN : 0 < N) : pieceLoc N 1 = 1 := by
  unfold pieceLoc
  rw [pieceIdx_one, natCast_pred hN]
  ring

/-- At the right end of a piece the local parameter is 0 or 1. -/
theorem abs_loc_piece_end [NeZero N] {k : ℕ} (hk : k < N) :
    |pieceLoc N (((k : ℝ) + 1) / N) - 1 / 2| = 1 / 2 := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases lt_or_eq_of_le (Nat.succ_le_of_lt hk) with hk1 | hk1
  · have hmem : ((k : ℝ) + 1) / N ∈ Ico (((k + 1 : ℕ) : ℝ) / N) ((((k + 1 : ℕ) : ℝ) + 1) / N) := by
      push_cast
      exact ⟨le_rfl, div_lt_div_of_pos_right (by linarith) hN'⟩
    unfold pieceLoc
    rw [pieceIdx_eq hk1 hmem]
    push_cast
    rw [mul_div_cancel₀ _ hN'.ne']
    norm_num
  · have h1 : ((k : ℝ) + 1) / N = 1 := by
      rw [show ((k : ℝ) + 1) = N by exact_mod_cast hk1, div_self hN'.ne']
    rw [h1]
    unfold pieceLoc
    rw [pieceIdx_one N, natCast_pred hN, mul_one]
    norm_num

/-- On the first part of piece k the homotopy is not straightened. -/
theorem loc_partA (hN : (0 : ℝ) < N) (hτ : 0 ≤ τ) {k : ℕ} (hk : k < N) {t : ℝ}
    (ht : t ∈ Icc ((k : ℝ) / N) (leftEnd N τ k)) : τ / 2 ≤ |pieceLoc N t - 1 / 2| := by
  have h2 := ht.2
  unfold leftEnd at h2
  rw [le_div_iff₀ hN] at h2
  have hlt : t < ((k : ℝ) + 1) / N := by
    rw [lt_div_iff₀ hN]
    linarith
  rw [loc_of_mem hk ⟨ht.1, hlt⟩]
  exact le_abs.mpr (Or.inr (by linarith))

/-- On the last part of piece k the homotopy is not straightened. -/
theorem loc_partC [NeZero N] (hN : (0 : ℝ) < N) (hτ : τ ∈ Icc (0 : ℝ) 1) {k : ℕ} (hk : k < N)
    {t : ℝ} (ht : t ∈ Icc (rightEnd N τ k) (((k : ℝ) + 1) / N)) :
    τ / 2 ≤ |pieceLoc N t - 1 / 2| := by
  rcases lt_or_ge t (((k : ℝ) + 1) / N) with hlt | hge
  · have hl : (k : ℝ) / N ≤ t :=
      (leftEnd_ge hN hτ.2 k).trans ((leftEnd_le_rightEnd hN hτ.1 k).trans ht.1)
    rw [loc_of_mem hk ⟨hl, hlt⟩]
    have h1 := ht.1
    unfold rightEnd at h1
    rw [div_le_iff₀ hN] at h1
    exact le_abs.mpr (Or.inl (by linarith))
  · have hte : t = ((k : ℝ) + 1) / N := le_antisymm ht.2 hge
    rw [hte, abs_loc_piece_end hk]
    linarith [hτ.2]

/-- Inside the straightened part of piece k. -/
theorem partB_facts (hN : (0 : ℝ) < N) (hτ : τ ∈ Icc (0 : ℝ) 1) (hτ0 : 0 < τ) {k : ℕ}
    (hk : k < N) {t : ℝ} (ht : t ∈ Ioo (leftEnd N τ k) (rightEnd N τ k)) :
    pieceIdx N t = k ∧ |pieceLoc N t - 1 / 2| < τ / 2 ∧
      segParam N τ t = (N : ℝ) / τ * (t - leftEnd N τ k) := by
  have hτne : τ ≠ 0 := hτ0.ne'
  have hNne : (N : ℝ) ≠ 0 := hN.ne'
  have hl := leftEnd_ge hN hτ.2 k
  have hr := rightEnd_le hN hτ.2 k
  have hidx : pieceIdx N t = k := pieceIdx_eq hk ⟨hl.trans ht.1.le, ht.2.trans_le hr⟩
  have hloc : pieceLoc N t = (N : ℝ) * t - k := by
    unfold pieceLoc
    rw [hidx]
  have h1 := ht.1
  have h2 := ht.2
  unfold leftEnd at h1
  unfold rightEnd at h2
  rw [div_lt_iff₀ hN] at h1
  rw [lt_div_iff₀ hN] at h2
  refine ⟨hidx, ?_, ?_⟩
  · rw [hloc, abs_lt]
    constructor <;> linarith
  · unfold segParam
    rw [hloc]
    unfold leftEnd
    field_simp
    ring

theorem segArg_mem (hN : (0 : ℝ) < N) (hτ0 : 0 < τ) {k : ℕ} {t : ℝ}
    (ht : t ∈ Icc (leftEnd N τ k) (rightEnd N τ k)) :
    (N : ℝ) / τ * (t - leftEnd N τ k) ∈ Icc (0 : ℝ) 1 := by
  have hc : 0 ≤ (N : ℝ) / τ := div_nonneg hN.le hτ0.le
  constructor
  · exact mul_nonneg hc (sub_nonneg.mpr ht.1)
  · calc (N : ℝ) / τ * (t - leftEnd N τ k) ≤ (N : ℝ) / τ * (rightEnd N τ k - leftEnd N τ k) :=
          mul_le_mul_of_nonneg_left (by linarith [ht.2]) hc
      _ = 1 := by
          rw [rightEnd_sub_leftEnd]
          field_simp

theorem homVel_eq_vel {sv : Sphere n → Sphere n → ℝ → Ambient n} {u : SphereLoop n} {t : ℝ}
    (h : τ / 2 ≤ |pieceLoc N t - 1 / 2|) : homVel sv N τ u t = velocity (u.data : Space n) t := by
  unfold homVel
  exact ite_eq_right (not_lt.mpr h)

theorem brk_three_mul (k : ℕ) : brk N τ (3 * k) = (k : ℝ) / N := by
  have h1 : 3 * k % 3 = 0 := by omega
  have h2 : 3 * k / 3 = k := by omega
  simp [brk, h1, h2]

theorem brk_three_mul_add_one (k : ℕ) : brk N τ (3 * k + 1) = leftEnd N τ k := by
  have h1 : (3 * k + 1) % 3 = 1 := by omega
  have h2 : (3 * k + 1) / 3 = k := by omega
  simp [brk, h1, h2]

theorem brk_three_mul_add_two (k : ℕ) : brk N τ (3 * k + 2) = rightEnd N τ k := by
  have h1 : (3 * k + 2) % 3 = 2 := by omega
  have h2 : (3 * k + 2) / 3 = k := by omega
  simp [brk, h1, h2]

theorem brk_zero : brk N τ 0 = 0 := by
  simpa using brk_three_mul (N := N) (τ := τ) 0

theorem brk_top (hN : 0 < N) : brk N τ (3 * N) = 1 := by
  rw [brk_three_mul, div_self (Nat.cast_ne_zero.mpr hN.ne')]

/-- The consecutive break points are k/N, the ends of the straightened part, and (k+1)/N. -/
theorem brk_cases {j : ℕ} (hj : j < 3 * N) :
    ∃ k < N, (brk N τ j = (k : ℝ) / N ∧ brk N τ (j + 1) = leftEnd N τ k) ∨
      (brk N τ j = leftEnd N τ k ∧ brk N τ (j + 1) = rightEnd N τ k) ∨
      (brk N τ j = rightEnd N τ k ∧ brk N τ (j + 1) = ((k : ℝ) + 1) / N) := by
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 3 ∧ j = 3 * k + i :=
    ⟨j / 3, j % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod j 3).symm⟩
  refine ⟨k, by omega, ?_⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · exact Or.inl ⟨brk_three_mul k, brk_three_mul_add_one k⟩
  · exact Or.inr (Or.inl ⟨brk_three_mul_add_one k, brk_three_mul_add_two k⟩)
  · refine Or.inr (Or.inr ⟨brk_three_mul_add_two k, ?_⟩)
    rw [show 3 * k + 2 + 1 = 3 * (k + 1) by ring, brk_three_mul]
    push_cast
    ring

/-- A property of consecutive break points follows from the three kinds of parts. -/
theorem brk_induction {P : ℝ → ℝ → Prop} (hA : ∀ k < N, P ((k : ℝ) / N) (leftEnd N τ k))
    (hB : ∀ k < N, P (leftEnd N τ k) (rightEnd N τ k))
    (hC : ∀ k < N, P (rightEnd N τ k) (((k : ℝ) + 1) / N)) {j : ℕ} (hj : j < 3 * N) :
    P (brk N τ j) (brk N τ (j + 1)) := by
  obtain ⟨k, hk, h | h | h⟩ := brk_cases (τ := τ) hj
  · rw [h.1, h.2]
    exact hA k hk
  · rw [h.1, h.2]
    exact hB k hk
  · rw [h.1, h.2]
    exact hC k hk

theorem partA_bounds (hN : (0 : ℝ) < N) (hτ : τ ∈ Icc (0 : ℝ) 1) {k : ℕ} (hk : k < N) :
    0 ≤ (k : ℝ) / N ∧ leftEnd N τ k ≤ 1 ∧ (k : ℝ) / N ≤ leftEnd N τ k :=
  ⟨by positivity, (leftEnd_le_rightEnd hN hτ.1 k).trans ((rightEnd_le hN hτ.2 k).trans
    (piece_le_one hN hk)), leftEnd_ge hN hτ.2 k⟩

theorem partC_bounds (hN : (0 : ℝ) < N) (hτ : τ ∈ Icc (0 : ℝ) 1) {k : ℕ} (hk : k < N) :
    0 ≤ rightEnd N τ k ∧ ((k : ℝ) + 1) / N ≤ 1 ∧ rightEnd N τ k ≤ ((k : ℝ) + 1) / N :=
  ⟨(by positivity : (0 : ℝ) ≤ (k : ℝ) / N).trans ((leftEnd_ge hN hτ.2 k).trans
    (leftEnd_le_rightEnd hN hτ.1 k)), piece_le_one hN hk, rightEnd_le hN hτ.2 k⟩

theorem brk_mono (hτ : τ ∈ Icc (0 : ℝ) 1) (hN : (0 : ℝ) < N) {j : ℕ} (hj : j < 3 * N) :
    brk N τ j ≤ brk N τ (j + 1) :=
  brk_induction (P := fun x y => x ≤ y) (fun k _ => leftEnd_ge hN hτ.2 k)
    (fun k _ => leftEnd_le_rightEnd hN hτ.1 k) (fun k _ => rightEnd_le hN hτ.2 k) hj

/-- The integral over [0,1] is the sum of the integrals over the parts. -/
theorem integral_eq_sum_brk (hN : 0 < N) {f : ℝ → ℝ}
    (hf : ∀ j < 3 * N, IntervalIntegrable f volume (brk N τ j) (brk N τ (j + 1))) :
    ∫ t in (0 : ℝ)..1, f t =
      ∑ j ∈ Finset.range (3 * N), ∫ t in (brk N τ j)..(brk N τ (j + 1)), f t := by
  have h := intervalIntegral.sum_integral_adjacent_intervals hf
  rw [brk_zero, brk_top hN] at h
  exact h.symm

theorem brk_mem (hτ : τ ∈ Icc (0 : ℝ) 1) (hN : 0 < N) {j : ℕ} (hj : j ≤ 3 * N) :
    brk N τ j ∈ Icc (0 : ℝ) 1 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rcases lt_or_eq_of_le hj with hj | rfl
  · obtain ⟨k, hk, h | h | h⟩ := brk_cases (τ := τ) hj
    · rw [h.1]
      exact piece_mem_Icc hk hN' ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hN'.le⟩
    · rw [h.1]
      exact piece_mem_Icc hk hN' ⟨leftEnd_ge hN' hτ.2 k,
        (leftEnd_le_rightEnd hN' hτ.1 k).trans (rightEnd_le hN' hτ.2 k)⟩
    · rw [h.1]
      exact piece_mem_Icc hk hN' ⟨(leftEnd_ge hN' hτ.2 k).trans (leftEnd_le_rightEnd hN' hτ.1 k),
        rightEnd_le hN' hτ.2 k⟩
  · rw [brk_top hN]
    exact ⟨zero_le_one, le_rfl⟩

theorem leftEnd_one (k : ℕ) : leftEnd N 1 k = (k : ℝ) / N := by
  unfold leftEnd
  congr 1
  ring

theorem rightEnd_one (k : ℕ) : rightEnd N 1 k = ((k : ℝ) + 1) / N := by
  unfold rightEnd
  congr 1
  ring

theorem segParam_one (t : ℝ) : segParam N 1 t = pieceLoc N t := by
  unfold segParam
  ring

end Ends

section Values

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      Finsler.SphereDistance.minEnergy F P Q)
  {N : ℕ} [NeZero N] {a : ℝ}
  (hspace : ∀ u : SphereLoop n, energy F u < a ^ 2 →
    ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖ < δ)
  {u : SphereLoop n} (hu : energy F u < a ^ 2) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)

include hspace hu hτ in
/-- The chords of the straightened parts are short. -/
theorem chord_short {k : ℕ} (hk : k < N) :
    ‖(pt u (rightEnd N τ k) : Ambient n) - pt u (leftEnd N τ k)‖ < δ := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hl := leftEnd_ge hN' hτ.2 k
  have hlr := leftEnd_le_rightEnd hN' hτ.1 k
  have hr := rightEnd_le hN' hτ.2 k
  have hlI : leftEnd N τ k ∈ Icc (0 : ℝ) 1 := piece_mem_Icc hk hN' ⟨hl, hlr.trans hr⟩
  have hrI : rightEnd N τ k ∈ Icc (0 : ℝ) 1 := piece_mem_Icc hk hN' ⟨hl.trans hlr, hr⟩
  rw [pt_coe u hlI, pt_coe u hrI]
  apply hspace u hu _ _ hlI hrI
  rw [rightEnd_sub_leftEnd, abs_of_nonneg (by have := hτ.1; positivity)]
  exact div_le_div_of_nonneg_right hτ.2 hN'.le

theorem time_of_loc {N : ℕ} (hN : (0 : ℝ) < N) (t : ℝ) :
    t = ((pieceIdx N t : ℝ) + pieceLoc N t) / N := by
  unfold pieceLoc
  field_simp
  ring

theorem segParam_left {N : ℕ} {τ t : ℝ} (h2 : pieceLoc N t - 1 / 2 = -(τ / 2)) :
    segParam N τ t = 0 := by
  unfold segParam
  rw [show pieceLoc N t - (1 / 2 - τ / 2) = 0 by linarith only [h2], zero_div]

theorem segParam_right {N : ℕ} {τ t : ℝ} (hτ0 : 0 < τ) (h2 : pieceLoc N t - 1 / 2 = τ / 2) :
    segParam N τ t = 1 := by
  unfold segParam
  rw [show pieceLoc N t - (1 / 2 - τ / 2) = τ by linarith only [h2], div_self hτ0.ne']

theorem time_eq_leftEnd {N : ℕ} (hN : (0 : ℝ) < N) {τ t : ℝ}
    (h2 : pieceLoc N t - 1 / 2 = -(τ / 2)) : t = leftEnd N τ (pieceIdx N t) := by
  calc t = ((pieceIdx N t : ℝ) + pieceLoc N t) / N := time_of_loc hN t
    _ = leftEnd N τ (pieceIdx N t) := by
      unfold leftEnd
      congr 1
      linarith only [h2]

theorem time_eq_rightEnd {N : ℕ} (hN : (0 : ℝ) < N) {τ t : ℝ}
    (h2 : pieceLoc N t - 1 / 2 = τ / 2) : t = rightEnd N τ (pieceIdx N t) := by
  calc t = ((pieceIdx N t : ℝ) + pieceLoc N t) / N := time_of_loc hN t
    _ = rightEnd N τ (pieceIdx N t) := by
      unfold rightEnd
      congr 1
      linarith only [h2]

include hseg hspace hu hτ in
/-- Away from the open straightened parts the homotopy is the loop. -/
theorem homVal_eq_rep {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (h : τ / 2 ≤ |pieceLoc N t - 1 / 2|) :
    homVal sc N τ u t = continuousRepresentative (u.data : Space n) t := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hkN := pieceIdx_lt hN t
  have hshort := chord_short F hspace hu hτ hkN
  obtain ⟨-, -, h0, h1, -, -⟩ := hseg _ _ hshort
  unfold homVal
  by_cases hle : |pieceLoc N t - 1 / 2| ≤ τ / 2
  · rw [ite_eq_left hle]
    have heq : |pieceLoc N t - 1 / 2| = τ / 2 := le_antisymm hle h
    have hτ2 : (0 : ℝ) ≤ τ / 2 := by have := hτ.1; positivity
    have hleft : pieceLoc N t - 1 / 2 = -(τ / 2) → sc (pt u (leftEnd N τ (pieceIdx N t)))
        (pt u (rightEnd N τ (pieceIdx N t))) (segParam N τ t) =
          continuousRepresentative (u.data : Space n) t := by
      intro h2
      have hp : segParam N τ t = 0 := segParam_left h2
      have hte := time_eq_leftEnd hN' h2
      calc sc (pt u (leftEnd N τ (pieceIdx N t))) (pt u (rightEnd N τ (pieceIdx N t)))
            (segParam N τ t) =
          sc (pt u (leftEnd N τ (pieceIdx N t))) (pt u (rightEnd N τ (pieceIdx N t))) 0 :=
            congrArg _ hp
        _ = (pt u (leftEnd N τ (pieceIdx N t)) : Ambient n) := h0
        _ = continuousRepresentative (u.data : Space n) (leftEnd N τ (pieceIdx N t)) :=
            pt_coe u (by rw [← hte]; exact ht)
        _ = continuousRepresentative (u.data : Space n) t :=
            congrArg (continuousRepresentative (u.data : Space n)) hte.symm
    rcases (abs_eq hτ2).mp heq with h2 | h2
    · by_cases hτ0 : τ = 0
      · apply hleft
        rw [h2, hτ0]
        norm_num
      · have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτ0)
        have hp : segParam N τ t = 1 := segParam_right hτpos h2
        have hte := time_eq_rightEnd hN' h2
        calc sc (pt u (leftEnd N τ (pieceIdx N t))) (pt u (rightEnd N τ (pieceIdx N t)))
              (segParam N τ t) =
            sc (pt u (leftEnd N τ (pieceIdx N t))) (pt u (rightEnd N τ (pieceIdx N t))) 1 :=
              congrArg _ hp
          _ = (pt u (rightEnd N τ (pieceIdx N t)) : Ambient n) := h1
          _ = continuousRepresentative (u.data : Space n) (rightEnd N τ (pieceIdx N t)) :=
              pt_coe u (by rw [← hte]; exact ht)
          _ = continuousRepresentative (u.data : Space n) t :=
              congrArg (continuousRepresentative (u.data : Space n)) hte.symm
    · exact hleft h2
  · rw [ite_eq_right hle]

include hseg hspace hu hτ in
/-- On the straightened part of piece k the homotopy is the rescaled segment. -/
theorem homVal_eq_segC (hτ0 : 0 < τ) {k : ℕ} (hk : k < N) {t : ℝ}
    (ht : t ∈ Icc (leftEnd N τ k) (rightEnd N τ k)) :
    homVal sc N τ u t = segC sc N τ u k t := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hτne : τ ≠ 0 := hτ0.ne'
  have hNne : (N : ℝ) ≠ 0 := hN'.ne'
  have hshort := chord_short F hspace hu hτ hk
  obtain ⟨-, -, h0, h1, -, -⟩ := hseg _ _ hshort
  have hl := leftEnd_ge hN' hτ.2 k
  have hr := rightEnd_le hN' hτ.2 k
  rcases lt_or_ge t (((k : ℝ) + 1) / N) with htk | htk
  · have hidx : pieceIdx N t = k := pieceIdx_eq hk ⟨hl.trans ht.1, htk⟩
    have hloc : pieceLoc N t = (N : ℝ) * t - k := by
      unfold pieceLoc
      rw [hidx]
    have hin : |pieceLoc N t - 1 / 2| ≤ τ / 2 := by
      rw [hloc, abs_le]
      have h1' := ht.1
      have h2' := ht.2
      unfold leftEnd at h1'
      unfold rightEnd at h2'
      rw [div_le_iff₀ hN'] at h1'
      rw [le_div_iff₀ hN'] at h2'
      constructor <;> nlinarith
    unfold homVal
    rw [ite_eq_left hin, hidx]
    unfold segC
    congr 1
    unfold segParam
    rw [hloc]
    unfold leftEnd
    field_simp
    ring
  · have hte : t = ((k : ℝ) + 1) / N := le_antisymm (ht.2.trans hr) htk
    have htR : t = rightEnd N τ k := le_antisymm ht.2 (hte ▸ hr)
    have htI : t ∈ Icc (0 : ℝ) 1 := piece_mem_Icc hk hN' ⟨hl.trans ht.1, ht.2.trans hr⟩
    have hrep := homVal_eq_rep F hseg hspace hu hτ htI (by
      rw [hte, abs_loc_piece_end hk]
      linarith [hτ.2])
    rw [hrep]
    have hp : (N : ℝ) / τ * (t - leftEnd N τ k) = 1 := by
      rw [htR, rightEnd_sub_leftEnd]
      field_simp
    unfold segC
    rw [hp, h1, ← htR]
    exact (pt_coe u htI).symm

include hseg hspace hu hτ in
theorem segC_hasDerivAt (hτ0 : 0 < τ) {k : ℕ} (hk : k < N) {t : ℝ}
    (ht : t ∈ Icc (leftEnd N τ k) (rightEnd N τ k)) :
    HasDerivAt (segC sc N τ u k) (segV sv N τ u k t) t := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hd := (hseg _ _ (chord_short F hspace hu hτ hk)).1 _ (segArg_mem hN' hτ0 ht)
  have ha : HasDerivAt (fun s : ℝ => (N : ℝ) / τ * (s - leftEnd N τ k)) ((N : ℝ) / τ) t := by
    have h := ((hasDerivAt_id' t).sub_const (leftEnd N τ k)).const_mul ((N : ℝ) / τ)
    rwa [mul_one] at h
  exact hd.scomp t ha

include hseg hspace hu hτ in
theorem segV_continuousOn (hτ0 : 0 < τ) {k : ℕ} (hk : k < N) :
    ContinuousOn (segV sv N τ u k) (Icc (leftEnd N τ k) (rightEnd N τ k)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hc := (hseg _ _ (chord_short F hspace hu hτ hk)).2.1
  have ha : Continuous (fun s : ℝ => (N : ℝ) / τ * (s - leftEnd N τ k)) :=
    continuous_const.mul (continuous_id.sub continuous_const)
  exact (hc.comp ha.continuousOn (fun s hs => segArg_mem hN' hτ0 hs)).const_smul ((N : ℝ) / τ)

include hseg hspace hu hτ in
theorem segC_continuousOn (hτ0 : 0 < τ) {k : ℕ} (hk : k < N) :
    ContinuousOn (segC sc N τ u k) (Icc (leftEnd N τ k) (rightEnd N τ k)) := fun _ ht =>
  (segC_hasDerivAt F hseg hspace hu hτ hτ0 hk ht).continuousAt.continuousWithinAt

include hseg hspace hu hτ in
theorem norm_segC {k : ℕ} (hk : k < N) (t : ℝ) : ‖segC sc N τ u k t‖ = 1 :=
  (hseg _ _ (chord_short F hspace hu hτ hk)).2.2.2.2.1 _

omit [NeZero N] in
include hτ in
theorem homVel_eq_segV (hN : (0 : ℝ) < N) (hτ0 : 0 < τ) {k : ℕ} (hk : k < N) {t : ℝ}
    (ht : t ∈ Ioo (leftEnd N τ k) (rightEnd N τ k)) :
    homVel sv N τ u t = segV sv N τ u k t := by
  obtain ⟨hidx, hlt, hpar⟩ := partB_facts hN hτ hτ0 hk ht
  unfold homVel segV
  rw [ite_eq_left hlt, hidx, hpar]

include hseg hspace hu hτ in
/-- The primitive identity on a part where the homotopy is the loop. -/
theorem partU_eq {x₀ x₁ : ℝ} (h0 : 0 ≤ x₀) (h1 : x₁ ≤ 1) (h01 : x₀ ≤ x₁)
    (hloc : ∀ t ∈ Icc x₀ x₁, τ / 2 ≤ |pieceLoc N t - 1 / 2|) :
    ∀ t ∈ Icc x₀ x₁, homVal sc N τ u t - homVal sc N τ u x₀ = ∫ s in x₀..t, homVel sv N τ u s := by
  intro t ht
  have haI : x₀ ∈ Icc (0 : ℝ) 1 := ⟨h0, h01.trans h1⟩
  have htI : t ∈ Icc (0 : ℝ) 1 := ⟨h0.trans ht.1, ht.2.trans h1⟩
  rw [homVal_eq_rep F hseg hspace hu hτ htI (hloc t ht),
    homVal_eq_rep F hseg hspace hu hτ haI (hloc x₀ ⟨le_rfl, h01⟩),
    continuousRepresentative_sub _ haI htI]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  exact (homVel_eq_vel (hloc s ⟨hs.1, hs.2.trans ht.2⟩)).symm

include hseg hspace hu hτ in
/-- Integrability on a part where the homotopy is the loop. -/
theorem partU_integrable {E : Type*} [NormedAddCommGroup E] {Φ : Ambient n → Ambient n → E}
    (hΦ : IntervalIntegrable (fun t => Φ (continuousRepresentative (u.data : Space n) t)
      (velocity (u.data : Space n) t)) volume 0 1)
    {x₀ x₁ : ℝ} (h0 : 0 ≤ x₀) (h1 : x₁ ≤ 1) (h01 : x₀ ≤ x₁)
    (hloc : ∀ t ∈ Icc x₀ x₁, τ / 2 ≤ |pieceLoc N t - 1 / 2|) :
    IntervalIntegrable (fun t => Φ (homVal sc N τ u t) (homVel sv N τ u t)) volume x₀ x₁ := by
  have hsub : uIcc x₀ x₁ ⊆ uIcc 0 1 := by
    rw [uIcc_of_le h01, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc h0 h1
  apply (hΦ.mono_set hsub).congr
  intro t ht
  rw [uIoc_of_le h01] at ht
  have ht' : t ∈ Icc x₀ x₁ := Ioc_subset_Icc_self ht
  dsimp only
  rw [homVal_eq_rep F hseg hspace hu hτ ⟨h0.trans ht'.1, ht'.2.trans h1⟩ (hloc t ht'),
    homVel_eq_vel (hloc t ht')]

include hseg hspace hu hτ in
/-- The primitive identity on the straightened part of piece k. -/
theorem partB_eq {k : ℕ} (hk : k < N) :
    ∀ t ∈ Icc (leftEnd N τ k) (rightEnd N τ k),
      homVal sc N τ u t - homVal sc N τ u (leftEnd N τ k) =
        ∫ s in (leftEnd N τ k)..t, homVel sv N τ u s := by
  intro t ht
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  by_cases hτ0 : τ = 0
  · have hte : t = leftEnd N τ k := le_antisymm (ht.2.trans (rightEnd_eq_leftEnd hτ0 k).le) ht.1
    rw [hte, sub_self, intervalIntegral.integral_same]
  · have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτ0)
    have hlr := leftEnd_le_rightEnd hN' hτ.1 k
    rw [homVal_eq_segC F hseg hspace hu hτ hτpos hk ht,
      homVal_eq_segC F hseg hspace hu hτ hτpos hk ⟨le_rfl, hlr⟩]
    have hsub : uIcc (leftEnd N τ k) t ⊆ Icc (leftEnd N τ k) (rightEnd N τ k) := by
      rw [uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2
    rw [intervalIntegral.integral_congr_Ioo_of_le ht.1 (f := homVel sv N τ u)
      (g := segV sv N τ u k) (fun s hs => homVel_eq_segV hτ hN' hτpos hk ⟨hs.1, hs.2.trans_le ht.2⟩),
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => segC_hasDerivAt F hseg hspace hu hτ hτpos hk (hsub hs))
        ((segV_continuousOn F hseg hspace hu hτ hτpos hk).mono hsub).intervalIntegrable]

include hseg hspace hu hτ in
/-- Integrability on the straightened part of piece k. -/
theorem partB_integrable {E : Type*} [NormedAddCommGroup E] {Φ : Ambient n → Ambient n → E}
    {k : ℕ} (hk : k < N)
    (hΦ : 0 < τ → ContinuousOn (fun t => Φ (segC sc N τ u k t) (segV sv N τ u k t))
      (Icc (leftEnd N τ k) (rightEnd N τ k))) :
    IntervalIntegrable (fun t => Φ (homVal sc N τ u t) (homVel sv N τ u t)) volume
      (leftEnd N τ k) (rightEnd N τ k) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  by_cases hτ0 : τ = 0
  · rw [rightEnd_eq_leftEnd hτ0 k]
  · have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτ0)
    have hlr := leftEnd_le_rightEnd hN' hτ.1 k
    have h1 : IntervalIntegrable (fun t => Φ (segC sc N τ u k t) (segV sv N τ u k t)) volume
        (leftEnd N τ k) (rightEnd N τ k) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hlr]
      exact hΦ hτpos
    apply h1.congr_uIoo
    intro t ht
    rw [uIoo_of_le hlr] at ht
    dsimp only
    rw [homVal_eq_segC F hseg hspace hu hτ hτpos hk (Ioo_subset_Icc_self ht),
      homVel_eq_segV hτ hN' hτpos hk ht]

include hseg hspace hu hτ in
theorem brk_part_eq {j : ℕ} (hj : j < 3 * N) : ∀ t ∈ Icc (brk N τ j) (brk N τ (j + 1)),
    homVal sc N τ u t - homVal sc N τ u (brk N τ j) = ∫ s in (brk N τ j)..t, homVel sv N τ u s := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  exact brk_induction (P := fun x₀ x₁ => ∀ t ∈ Icc x₀ x₁,
      homVal sc N τ u t - homVal sc N τ u x₀ = ∫ s in x₀..t, homVel sv N τ u s)
    (fun k hk => partU_eq F hseg hspace hu hτ (partA_bounds hN' hτ hk).1
      (partA_bounds hN' hτ hk).2.1 (partA_bounds hN' hτ hk).2.2
      (fun t ht => loc_partA hN' hτ.1 hk ht))
    (fun k hk => partB_eq F hseg hspace hu hτ hk)
    (fun k hk => partU_eq F hseg hspace hu hτ (partC_bounds hN' hτ hk).1
      (partC_bounds hN' hτ hk).2.1 (partC_bounds hN' hτ hk).2.2
      (fun t ht => loc_partC hN' hτ hk ht)) hj

include hseg hspace hu hτ in
theorem brk_part_integrable {E : Type*} [NormedAddCommGroup E] {Φ : Ambient n → Ambient n → E}
    (hΦu : IntervalIntegrable (fun t => Φ (continuousRepresentative (u.data : Space n) t)
      (velocity (u.data : Space n) t)) volume 0 1)
    (hΦs : 0 < τ → ∀ k < N, ContinuousOn (fun t => Φ (segC sc N τ u k t) (segV sv N τ u k t))
      (Icc (leftEnd N τ k) (rightEnd N τ k)))
    {j : ℕ} (hj : j < 3 * N) :
    IntervalIntegrable (fun t => Φ (homVal sc N τ u t) (homVel sv N τ u t)) volume
      (brk N τ j) (brk N τ (j + 1)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  exact brk_induction
    (P := fun x₀ x₁ => IntervalIntegrable (fun t => Φ (homVal sc N τ u t) (homVel sv N τ u t))
      volume x₀ x₁)
    (fun k hk => partU_integrable F hseg hspace hu hτ hΦu (partA_bounds hN' hτ hk).1
      (partA_bounds hN' hτ hk).2.1 (partA_bounds hN' hτ hk).2.2
      (fun t ht => loc_partA hN' hτ.1 hk ht))
    (fun k hk => partB_integrable F hseg hspace hu hτ hk (fun hτ0 => hΦs hτ0 k hk))
    (fun k hk => partU_integrable F hseg hspace hu hτ hΦu (partC_bounds hN' hτ hk).1
      (partC_bounds hN' hτ hk).2.1 (partC_bounds hN' hτ hk).2.2
      (fun t ht => loc_partC hN' hτ hk ht)) hj

include hseg hspace hu hτ in
/-- Integrability of an expression in the value and velocity of the homotopy. -/
theorem homPair_intervalIntegrable {E : Type*} [NormedAddCommGroup E]
    {Φ : Ambient n → Ambient n → E}
    (hΦu : IntervalIntegrable (fun t => Φ (continuousRepresentative (u.data : Space n) t)
      (velocity (u.data : Space n) t)) volume 0 1)
    (hΦs : 0 < τ → ∀ k < N, ContinuousOn (fun t => Φ (segC sc N τ u k t) (segV sv N τ u k t))
      (Icc (leftEnd N τ k) (rightEnd N τ k))) :
    IntervalIntegrable (fun t => Φ (homVal sc N τ u t) (homVel sv N τ u t)) volume 0 1 := by
  have hN := Nat.pos_of_neZero N
  have h := IntervalIntegrable.trans_iterate (a := brk N τ) (n := 3 * N)
    (f := fun t => Φ (homVal sc N τ u t) (homVel sv N τ u t)) (μ := volume)
    (fun j hj => brk_part_integrable F hseg hspace hu hτ hΦu hΦs hj)
  rwa [brk_zero, brk_top hN] at h

include hseg hspace hu hτ in
theorem homVel_intervalIntegrable : IntervalIntegrable (homVel sv N τ u) volume 0 1 :=
  homPair_intervalIntegrable F hseg hspace hu hτ (Φ := fun _ v => v)
    (velocity_intervalIntegrable _) (fun hτ0 _ hk => segV_continuousOn F hseg hspace hu hτ hτ0 hk)

include hseg hspace hu hτ in
/-- The value of the homotopy is its value at 0 plus the primitive of its velocity. -/
theorem homVal_eq_add_integral {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    homVal sc N τ u t = homVal sc N τ u 0 + ∫ s in (0 : ℝ)..t, homVel sv N τ u s := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := eq_add_integral_of_parts (V := homVal sc N τ u) (W := homVel sv N τ u)
    (x := brk N τ) (3 * N) (fun j hj => brk_mono hτ hN' hj)
    (fun j hj => brk_part_eq F hseg hspace hu hτ hj)
    (fun j hj => brk_part_integrable F hseg hspace hu hτ (Φ := fun _ v => v)
      (velocity_intervalIntegrable _)
      (fun hτ0 _ hk => segV_continuousOn F hseg hspace hu hτ hτ0 hk) hj) t
    (by rw [brk_zero, brk_top hN]; exact ht)
  rw [brk_zero] at h
  exact sub_eq_iff_eq_add'.mp h

include hseg hspace hu hτ in
theorem homVel_memLp : MemLp (homVel sv N τ u) 2 intervalMeasure := by
  have hmeas : AEStronglyMeasurable (homVel sv N τ u) intervalMeasure :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (homVel_intervalIntegrable F hseg hspace hu hτ)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hsq : IntervalIntegrable (fun t => ‖homVel sv N τ u t‖ ^ 2) volume 0 1 :=
    homPair_intervalIntegrable F hseg hspace hu hτ (Φ := fun _ v => ‖v‖ ^ 2)
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr (integrable_velocity_sq _))
      (fun hτ0 _ hk => (segV_continuousOn F hseg hspace hu hτ hτ0 hk).norm.pow 2)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hsq

include hseg hspace hu hτ in
theorem homVal_continuousOn : ContinuousOn (homVal sc N τ u) (Icc 0 1) := by
  have hc := intervalIntegral.continuousOn_primitive_interval'
    (homVel_intervalIntegrable F hseg hspace hu hτ) left_mem_uIcc
  rw [uIcc_of_le zero_le_one] at hc
  exact (continuousOn_const.add hc).congr (fun t ht => homVal_eq_add_integral F hseg hspace hu hτ ht)

include hseg hspace hu hτ in
theorem norm_homVal {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖homVal sc N τ u t‖ = 1 := by
  have hN := Nat.pos_of_neZero N
  unfold homVal
  by_cases h : |pieceLoc N t - 1 / 2| ≤ τ / 2
  · rw [ite_eq_left h]
    exact (hseg _ _ (chord_short F hspace hu hτ (pieceIdx_lt hN t))).2.2.2.2.1 _
  · rw [ite_eq_right h]
    exact u.sphere_constraint ⟨t, ht⟩

include hseg hspace hu hτ in
theorem homVal_one_eq_zero : homVal sc N τ u 1 = homVal sc N τ u 0 := by
  have hN := Nat.pos_of_neZero N
  have h1 : τ / 2 ≤ |pieceLoc N 1 - 1 / 2| := by
    rw [pieceLoc_one hN, show |(1 : ℝ) - 1 / 2| = 1 / 2 by norm_num]
    linarith [hτ.2]
  have h0 : τ / 2 ≤ |pieceLoc N 0 - 1 / 2| := by
    rw [pieceLoc_zero, show |(0 : ℝ) - 1 / 2| = 1 / 2 by norm_num]
    linarith [hτ.2]
  rw [homVal_eq_rep F hseg hspace hu hτ (by norm_num) h1,
    homVal_eq_rep F hseg hspace hu hτ (by norm_num) h0]
  have hp := u.data.2
  rw [mem_periodicSubmodule_iff] at hp
  exact hp

/-- The straightening homotopy at time τ as an H¹ graph element. -/
def homLoop : Space n :=
  ofPrimitive (homVal_continuousOn F hseg hspace hu hτ) (homVel_memLp F hseg hspace hu hτ)
    (fun _ ht => homVal_eq_add_integral F hseg hspace hu hτ ht)

theorem homLoop_periodic : homLoop F hseg hspace hu hτ ∈ periodicSubmodule n :=
  ofPrimitive_periodic _ _ _ (homVal_one_eq_zero F hseg hspace hu hτ)

theorem representative_homLoop {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (homLoop F hseg hspace hu hτ) t = homVal sc N τ u t :=
  representative_ofPrimitive _ _ _ ht

theorem velocity_homLoop_ae :
    velocity (homLoop F hseg hspace hu hτ) =ᵐ[intervalMeasure] homVel sv N τ u :=
  velocity_ofPrimitive_ae _ _ _

/-- The straightening homotopy at time τ as a sphere loop. -/
def homSphereLoop : SphereLoop n :=
  ⟨⟨homLoop F hseg hspace hu hτ, homLoop_periodic F hseg hspace hu hτ⟩, fun t => by
    change ‖continuousRepresentative (homLoop F hseg hspace hu hτ) t‖ = 1
    rw [representative_homLoop F hseg hspace hu hτ t.2]
    exact norm_homVal F hseg hspace hu hτ t.2⟩

/-- The minimal energy between two points of a loop is at most the length of the time interval
times the energy on it. -/
theorem minEnergy_le_part (F : ReversibleMetric n) (u : SphereLoop n) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    minEnergy F (pt u s : Ambient n) (pt u t) ≤
      (t - s) * ∫ x in s..t, lagrangian F (continuousRepresentative (u.data : Space n) x,
        velocity (u.data : Space n) x) := by
  have hw := data_mem_spherePath u
  have hmemp : restrict (u.data : Space n) hs ht hst ∈
      pathsBetween n (pt u s : Ambient n) (pt u t) :=
    ⟨restrict_mem hw hs ht hst, (representative_restrict_zero _ hs ht hst).trans (pt_coe u hs).symm,
      (representative_restrict_one _ hs ht hst).trans (pt_coe u ht).symm⟩
  exact (minEnergy_le F hmemp).trans_eq (pathEnergy_restrict F (u.data : Space n) hs ht hst)

/-- The energy of the rescaled segment on the straightened part of piece k. -/
theorem segEnergy (hτ0 : 0 < τ) (k : ℕ) :
    ∫ t in (leftEnd N τ k)..(rightEnd N τ k), lagrangian F (segC sc N τ u k t, segV sv N τ u k t) =
      (N : ℝ) / τ * ∫ s in (0 : ℝ)..1, lagrangian F (sc (pt u (leftEnd N τ k))
        (pt u (rightEnd N τ k)) s, sv (pt u (leftEnd N τ k)) (pt u (rightEnd N τ k)) s) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hc0 : (N : ℝ) / τ ≠ 0 := (div_pos hN' hτ0).ne'
  have hfun : (fun t => lagrangian F (segC sc N τ u k t, segV sv N τ u k t)) =
      fun t => ((N : ℝ) / τ) ^ 2 * lagrangian F (sc (pt u (leftEnd N τ k)) (pt u (rightEnd N τ k))
        ((N : ℝ) / τ * t - (N : ℝ) / τ * leftEnd N τ k), sv (pt u (leftEnd N τ k))
          (pt u (rightEnd N τ k)) ((N : ℝ) / τ * t - (N : ℝ) / τ * leftEnd N τ k)) := by
    funext t
    simp only [segC, segV]
    rw [Finsler.EnergyConservation.lagrangian_velocity_smul, mul_sub]
  rw [hfun, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_sub
    (f := fun s => lagrangian F (sc (pt u (leftEnd N τ k)) (pt u (rightEnd N τ k)) s,
      sv (pt u (leftEnd N τ k)) (pt u (rightEnd N τ k)) s)) hc0]
  have hb1 : (N : ℝ) / τ * leftEnd N τ k - (N : ℝ) / τ * leftEnd N τ k = 0 := sub_self _
  have hb2 : (N : ℝ) / τ * rightEnd N τ k - (N : ℝ) / τ * leftEnd N τ k = 1 := by
    rw [← mul_sub, rightEnd_sub_leftEnd]
    field_simp
  rw [hb1, hb2, smul_eq_mul]
  generalize (∫ s in (0 : ℝ)..1, lagrangian F (sc (pt u (leftEnd N τ k))
    (pt u (rightEnd N τ k)) s, sv (pt u (leftEnd N τ k)) (pt u (rightEnd N τ k)) s)) = I
  field_simp

include hseg hspace hu hτ in
/-- On a part where the homotopy is the loop, the energies agree. -/
theorem partU_energy_eq {x₀ x₁ : ℝ} (h0 : 0 ≤ x₀) (h1 : x₁ ≤ 1) (h01 : x₀ ≤ x₁)
    (hloc : ∀ t ∈ Icc x₀ x₁, τ / 2 ≤ |pieceLoc N t - 1 / 2|) :
    ∫ t in x₀..x₁, lagrangian F (homVal sc N τ u t, homVel sv N τ u t) =
      ∫ t in x₀..x₁, lagrangian F (continuousRepresentative (u.data : Space n) t,
        velocity (u.data : Space n) t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le h01] at ht
  exact congrArg₂ (fun x v => lagrangian F (x, v))
    (homVal_eq_rep F hseg hspace hu hτ ⟨h0.trans ht.1, ht.2.trans h1⟩ (hloc t ht))
    (homVel_eq_vel (hloc t ht))

include hseg hspace hu hτ in
/-- On the straightened part the energy does not increase. -/
theorem partB_energy_le {k : ℕ} (hk : k < N) :
    ∫ t in (leftEnd N τ k)..(rightEnd N τ k), lagrangian F (homVal sc N τ u t, homVel sv N τ u t) ≤
      ∫ t in (leftEnd N τ k)..(rightEnd N τ k), lagrangian F
        (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  by_cases hτ0 : τ = 0
  · rw [rightEnd_eq_leftEnd hτ0 k, intervalIntegral.integral_same, intervalIntegral.integral_same]
  · have hτpos : 0 < τ := lt_of_le_of_ne hτ.1 (Ne.symm hτ0)
    have hlr := leftEnd_le_rightEnd hN' hτ.1 k
    have hl := leftEnd_ge hN' hτ.2 k
    have hr := rightEnd_le hN' hτ.2 k
    have hlI : leftEnd N τ k ∈ Icc (0 : ℝ) 1 := piece_mem_Icc hk hN' ⟨hl, hlr.trans hr⟩
    have hrI : rightEnd N τ k ∈ Icc (0 : ℝ) 1 := piece_mem_Icc hk hN' ⟨hl.trans hlr, hr⟩
    have hcongr : ∫ t in (leftEnd N τ k)..(rightEnd N τ k),
        lagrangian F (homVal sc N τ u t, homVel sv N τ u t) =
        ∫ t in (leftEnd N τ k)..(rightEnd N τ k),
          lagrangian F (segC sc N τ u k t, segV sv N τ u k t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hlr
      intro t ht
      exact congrArg₂ (fun x v => lagrangian F (x, v))
        (homVal_eq_segC F hseg hspace hu hτ hτpos hk (Ioo_subset_Icc_self ht))
        (homVel_eq_segV hτ hN' hτpos hk ht)
    have hme := (minEnergy_le_part F u hlI hrI hlr).trans_eq
      (congrArg (· * _) (rightEnd_sub_leftEnd (N := N) (τ := τ) k))
    have halg : ∀ m I : ℝ, m ≤ τ / N * I → (N : ℝ) / τ * m ≤ I := by
      intro m I h
      calc (N : ℝ) / τ * m ≤ (N : ℝ) / τ * (τ / N * I) :=
            mul_le_mul_of_nonneg_left h (div_nonneg hN'.le hτpos.le)
        _ = I := by field_simp
    calc ∫ t in (leftEnd N τ k)..(rightEnd N τ k),
          lagrangian F (homVal sc N τ u t, homVel sv N τ u t)
        = ∫ t in (leftEnd N τ k)..(rightEnd N τ k),
          lagrangian F (segC sc N τ u k t, segV sv N τ u k t) := hcongr
      _ = (N : ℝ) / τ * ∫ s in (0 : ℝ)..1, lagrangian F (sc (pt u (leftEnd N τ k))
          (pt u (rightEnd N τ k)) s, sv (pt u (leftEnd N τ k)) (pt u (rightEnd N τ k)) s) :=
            segEnergy F hτpos k
      _ = (N : ℝ) / τ * minEnergy F (pt u (leftEnd N τ k) : Ambient n) (pt u (rightEnd N τ k)) :=
            congrArg _ (hseg _ _ (chord_short F hspace hu hτ hk)).2.2.2.2.2
      _ ≤ _ := halg _ _ hme

include hseg hspace hu hτ in
theorem brk_part_energy_le {j : ℕ} (hj : j < 3 * N) :
    ∫ t in (brk N τ j)..(brk N τ (j + 1)), lagrangian F (homVal sc N τ u t, homVel sv N τ u t) ≤
      ∫ t in (brk N τ j)..(brk N τ (j + 1)), lagrangian F
        (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  exact brk_induction (P := fun x₀ x₁ =>
      ∫ t in x₀..x₁, lagrangian F (homVal sc N τ u t, homVel sv N τ u t) ≤
        ∫ t in x₀..x₁, lagrangian F
          (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t))
    (fun k hk => (partU_energy_eq F hseg hspace hu hτ (partA_bounds hN' hτ hk).1
      (partA_bounds hN' hτ hk).2.1 (partA_bounds hN' hτ hk).2.2
      (fun t ht => loc_partA hN' hτ.1 hk ht)).le)
    (fun k hk => partB_energy_le F hseg hspace hu hτ hk)
    (fun k hk => (partU_energy_eq F hseg hspace hu hτ (partC_bounds hN' hτ hk).1
      (partC_bounds hN' hτ hk).2.1 (partC_bounds hN' hτ hk).2.2
      (fun t ht => loc_partC hN' hτ hk ht)).le) hj

include hseg hspace hu hτ in
theorem pathEnergy_homLoop :
    pathEnergy F (homLoop F hseg hspace hu hτ) =
      ∫ t in (0 : ℝ)..1, lagrangian F (homVal sc N τ u t, homVel sv N τ u t) := by
  rw [pathEnergy_eq_intervalIntegral]
  apply intervalIntegral.integral_congr_ae
  have h1 : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) 1 →
      velocity (homLoop F hseg hspace hu hτ) t = homVel sv N τ u t := by
    have h := velocity_homLoop_ae F hseg hspace hu hτ
    change ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) 1)),
      velocity (homLoop F hseg hspace hu hτ) t = homVel sv N τ u t at h
    rw [ae_restrict_iff' measurableSet_Ioo] at h
    exact h
  have h2 : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by
    rw [ae_iff]
    simp
  filter_upwards [h1, h2] with t ht1 ht2 ht
  rw [uIoc_of_le zero_le_one] at ht
  have ht' : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, lt_of_le_of_ne ht.2 ht2⟩
  rw [representative_homLoop F hseg hspace hu hτ (Ioo_subset_Icc_self ht'), ht1 ht']

include hseg hspace hu hτ in
/-- The straightening homotopy does not increase the energy. -/
theorem energy_homSphereLoop_le : energy F (homSphereLoop F hseg hspace hu hτ) ≤ energy F u := by
  have hN := Nat.pos_of_neZero N
  change pathEnergy F (homLoop F hseg hspace hu hτ) ≤ pathEnergy F (u.data : Space n)
  have hseg' : 0 < τ → ∀ k < N, ContinuousOn (fun t => (fun x v => lagrangian F (x, v))
      (segC sc N τ u k t) (segV sv N τ u k t)) (Icc (leftEnd N τ k) (rightEnd N τ k)) := by
    intro hτ0 k hk t ht
    have hz : segC sc N τ u k t ≠ 0 := by
      intro h0
      have h1 := norm_segC F hseg hspace hu hτ hk t
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun x => (segC sc N τ u k x, segV sv N τ u k x)) (x := t)
      (lagrangian_continuousAt F (z := (segC sc N τ u k t, segV sv N τ u k t)) hz)
      ((segC_continuousOn F hseg hspace hu hτ hτ0 hk t ht).prodMk
        (segV_continuousOn F hseg hspace hu hτ hτ0 hk t ht))
  have hdens := density_intervalIntegrable F (data_mem_spherePath u)
  have hint1 : ∀ j < 3 * N, IntervalIntegrable
      (fun t => lagrangian F (homVal sc N τ u t, homVel sv N τ u t)) volume
      (brk N τ j) (brk N τ (j + 1)) := fun j hj =>
    brk_part_integrable F hseg hspace hu hτ (Φ := fun x v => lagrangian F (x, v)) hdens hseg' hj
  have hint2 : ∀ j < 3 * N, IntervalIntegrable (fun t => lagrangian F
      (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t)) volume
      (brk N τ j) (brk N τ (j + 1)) := by
    intro j hj
    apply hdens.mono_set
    have h1 := brk_mem hτ hN (j := j) hj.le
    have h2 := brk_mem hτ hN (j := j + 1) hj
    have hm := brk_mono hτ (by exact_mod_cast hN : (0 : ℝ) < N) hj
    rw [uIcc_of_le zero_le_one, uIcc_of_le hm]
    exact Icc_subset_Icc h1.1 h2.2
  calc pathEnergy F (homLoop F hseg hspace hu hτ)
      = ∫ t in (0 : ℝ)..1, lagrangian F (homVal sc N τ u t, homVel sv N τ u t) :=
        pathEnergy_homLoop F hseg hspace hu hτ
    _ = ∑ j ∈ Finset.range (3 * N), ∫ t in (brk N τ j)..(brk N τ (j + 1)),
          lagrangian F (homVal sc N τ u t, homVel sv N τ u t) := integral_eq_sum_brk hN hint1
    _ ≤ ∑ j ∈ Finset.range (3 * N), ∫ t in (brk N τ j)..(brk N τ (j + 1)), lagrangian F
          (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t) :=
        Finset.sum_le_sum fun j hj =>
          brk_part_energy_le F hseg hspace hu hτ (Finset.mem_range.mp hj)
    _ = ∫ t in (0 : ℝ)..1, lagrangian F
          (continuousRepresentative (u.data : Space n) t, velocity (u.data : Space n) t) :=
        (integral_eq_sum_brk hN hint2).symm
    _ = pathEnergy F (u.data : Space n) := (pathEnergy_eq_intervalIntegral F _).symm

include hseg hspace hu hτ in
/-- At τ = 0 the homotopy is the loop. -/
theorem homSphereLoop_zero (hτ0 : τ = 0) : homSphereLoop F hseg hspace hu hτ = u := by
  apply sphereLoop_data_injective
  apply eq_of_representative_eqOn
  intro t ht
  change continuousRepresentative (homLoop F hseg hspace hu hτ) t = _
  rw [representative_homLoop F hseg hspace hu hτ ht]
  exact homVal_eq_rep F hseg hspace hu hτ ht (by rw [hτ0, zero_div]; exact abs_nonneg _)

theorem pt_eq_samplePoly (u : SphereLoop n) {k : ℕ} (hk : k < N) :
    pt u ((k : ℝ) / N) = samplePoly N u (k : ZMod N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  apply Subtype.ext
  rw [pt_coe u (piece_mem_Icc hk hN' ⟨le_rfl, div_le_div_of_nonneg_right (by linarith) hN'.le⟩)]
  exact (sampleN_natCast u hk).symm

theorem pt_eq_samplePoly_succ (u : SphereLoop n) {k : ℕ} (hk : k < N) :
    pt u (((k : ℝ) + 1) / N) = samplePoly N u ((k : ZMod N) + 1) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  apply Subtype.ext
  rw [pt_coe u (piece_mem_Icc hk hN' ⟨div_le_div_of_nonneg_right (by linarith) hN'.le, le_rfl⟩)]
  exact (sampleN_natCast_succ u hk).symm

include hseg hspace hu hτ in
/-- At τ = 1 the homotopy is the broken geodesic of the samples. -/
theorem homSphereLoop_one (hτ1 : τ = 1) :
    homSphereLoop F hseg hspace hu hτ =
      polySphereLoop F hseg (shortPolygon_samplePoly F hspace hu) := by
  have hN := Nat.pos_of_neZero N
  apply sphereLoop_data_injective
  apply eq_of_representative_eqOn
  intro t ht
  change continuousRepresentative (homLoop F hseg hspace hu hτ) t =
    continuousRepresentative (polyLoop F hseg (shortPolygon_samplePoly F hspace hu)) t
  rw [representative_homLoop F hseg hspace hu hτ ht, representative_polyLoop F hseg _ ht, hτ1]
  have hloc := pieceLoc_mem hN ht
  have hle : |pieceLoc N t - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [hloc.1, hloc.2]
  have hk := pieceIdx_lt hN t
  unfold homVal polyCurve glue edgeCurve
  rw [ite_eq_left hle, leftEnd_one, rightEnd_one, segParam_one, pt_eq_samplePoly u hk,
    pt_eq_samplePoly_succ u hk]

end Values

end

end Finsler.MilnorHomotopy
