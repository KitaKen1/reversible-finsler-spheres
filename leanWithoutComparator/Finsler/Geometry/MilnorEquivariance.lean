module

public import Finsler.Geometry.MilnorContinuity
public import Finsler.Analysis.IntervalH1ShiftEnergy

/-! Equivariance of the straightening homotopy. On the real line the homotopy is described with the
integer part of N t: the straightened part of the piece containing t is centred at
(⌊N t⌋ + 1/2)/N. Shifting t by 1/N shifts the integer part by 1, so rotating the loop by 1/N
rotates the homotopy by 1/N. Reflecting t to 1 − t maps the piece k to the piece N − 1 − k and the
local parameter to 1 minus it, so with reversible segments the homotopy of the reversed loop is the
reversed homotopy. -/

@[expose] public section

namespace Finsler.MilnorEquivariance

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevSpherePath
open Finsler.SobolevEnergy Finsler.PolygonLoop Finsler.PiecewiseC1
open Finsler.SobolevCircleRepresentative Finsler.SobolevCircleAction Finsler.MilnorHomotopy
open Finsler.MilnorContinuity Finsler.SobolevShiftEnergy Finsler.SobolevReverse
open Finsler.PolygonSampling Finsler.PolygonCritical
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

theorem pt_add_one (u : SphereLoop n) (x : ℝ) : pt u (x + 1) = pt u x := by
  unfold pt
  rw [AddCircle.coe_add_period]

theorem pt_vadd (u : SphereLoop n) (s x : ℝ) :
    pt (((s : ℝ) : SobolevCircleRepresentative.Circle) +ᵥ u) x = pt u (x + s) := by
  unfold pt
  rw [sphereCircleMap_vadd, add_comm (s : SobolevCircleRepresentative.Circle), AddCircle.coe_add]

theorem realMap_vadd (u : SphereLoop n) (s x : ℝ) :
    realMap ((((s : ℝ) : SobolevCircleRepresentative.Circle) +ᵥ u).data) x =
      realMap u.data (x + s) := by
  have h := congrArg (fun P : Sphere n => (P : Ambient n)) (pt_vadd u s x)
  exact h

/-- The integer part of N t, as a real number. -/
def fl (N : ℕ) (t : ℝ) : ℝ := ⌊(N : ℝ) * t⌋

/-- The fractional part of N t. -/
def fr (N : ℕ) (t : ℝ) : ℝ := (N : ℝ) * t - fl N t

theorem fl_add_one (N : ℕ) (t : ℝ) : fl N (t + 1) = fl N t + N := by
  unfold fl
  rw [mul_add, mul_one, Int.floor_add_natCast]
  push_cast
  ring

theorem fr_add_one (N : ℕ) (t : ℝ) : fr N (t + 1) = fr N t := by
  unfold fr
  rw [fl_add_one]
  ring

theorem fl_add_inv {N : ℕ} (hN : (N : ℝ) ≠ 0) (t : ℝ) : fl N (t + 1 / N) = fl N t + 1 := by
  unfold fl
  rw [mul_add, mul_one_div_cancel hN, Int.floor_add_one]
  push_cast
  ring

theorem fr_add_inv {N : ℕ} (hN : (N : ℝ) ≠ 0) (t : ℝ) : fr N (t + 1 / N) = fr N t := by
  unfold fr
  rw [fl_add_inv hN, mul_add, mul_one_div_cancel hN]
  ring

/-- The homotopy on the real line, described with the integer part of N t. -/
def homReal (sc : Sphere n → Sphere n → ℝ → Ambient n) (N : ℕ) (τ : ℝ) (u : SphereLoop n)
    (t : ℝ) : Ambient n :=
  if |fr N t - 1 / 2| ≤ τ / 2 then
    sc (pt u ((fl N t + 1 / 2 - τ / 2) / N)) (pt u ((fl N t + 1 / 2 + τ / 2) / N))
      ((fr N t - (1 / 2 - τ / 2)) / τ)
  else realMap u.data t

theorem homReal_add_one (sc : Sphere n → Sphere n → ℝ → Ambient n) {N : ℕ} (hN : (N : ℝ) ≠ 0)
    (τ : ℝ) (u : SphereLoop n) (t : ℝ) : homReal sc N τ u (t + 1) = homReal sc N τ u t := by
  have hl : pt u ((fl N (t + 1) + 1 / 2 - τ / 2) / N) = pt u ((fl N t + 1 / 2 - τ / 2) / N) := by
    rw [fl_add_one, show (fl N t + N + 1 / 2 - τ / 2) / N = (fl N t + 1 / 2 - τ / 2) / N + 1 by
      field_simp; ring, pt_add_one]
  have hr : pt u ((fl N (t + 1) + 1 / 2 + τ / 2) / N) = pt u ((fl N t + 1 / 2 + τ / 2) / N) := by
    rw [fl_add_one, show (fl N t + N + 1 / 2 + τ / 2) / N = (fl N t + 1 / 2 + τ / 2) / N + 1 by
      field_simp; ring, pt_add_one]
  unfold homReal
  rw [fr_add_one, hl, hr, realMap_periodic]

theorem homReal_rotate (sc : Sphere n → Sphere n → ℝ → Ambient n) {N : ℕ} (hN : (N : ℝ) ≠ 0)
    (τ : ℝ) (u : SphereLoop n) (t : ℝ) :
    homReal sc N τ ((((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ u) t =
      homReal sc N τ u (t + 1 / N) := by
  have hl : pt ((((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ u)
      ((fl N t + 1 / 2 - τ / 2) / N) = pt u ((fl N (t + 1 / N) + 1 / 2 - τ / 2) / N) := by
    rw [pt_vadd, fl_add_inv hN]
    congr 1
    field_simp
    ring
  have hr : pt ((((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ u)
      ((fl N t + 1 / 2 + τ / 2) / N) = pt u ((fl N (t + 1 / N) + 1 / 2 + τ / 2) / N) := by
    rw [pt_vadd, fl_add_inv hN]
    congr 1
    field_simp
    ring
  unfold homReal
  rw [fr_add_inv hN, hl, hr, realMap_vadd]

theorem pieceIdx_cast {N : ℕ} [NeZero N] {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    (pieceIdx N t : ℝ) = fl N t := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hNt : 0 ≤ (N : ℝ) * t := mul_nonneg hN'.le ht.1
  have hlt : ⌊(N : ℝ) * t⌋₊ < N := by
    rw [Nat.floor_lt hNt]
    calc (N : ℝ) * t < N * 1 := mul_lt_mul_of_pos_left ht.2 hN'
      _ = N := mul_one _
  have hidx : pieceIdx N t = ⌊(N : ℝ) * t⌋₊ := by
    unfold pieceIdx
    exact min_eq_left (Nat.le_sub_one_of_lt hlt)
  rw [hidx]
  unfold fl
  exact natCast_floor_eq_intCast_floor hNt

section Rotation

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

include hseg hspace in
theorem realMap_homSphereLoop_of_mem {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    realMap (homSphereLoop F hseg hspace hu hτ).data t = homReal sc N τ u t := by
  have htI : t ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self ht
  rw [realMap_eqOn _ htI]
  change continuousRepresentative (homLoop F hseg hspace hu hτ) t = _
  rw [representative_homLoop F hseg hspace hu hτ htI]
  have hloc : pieceLoc N t = fr N t := by
    unfold pieceLoc fr
    rw [pieceIdx_cast ht]
  have hl : leftEnd N τ (pieceIdx N t) = (fl N t + 1 / 2 - τ / 2) / N := by
    unfold leftEnd
    rw [pieceIdx_cast ht]
  have hr : rightEnd N τ (pieceIdx N t) = (fl N t + 1 / 2 + τ / 2) / N := by
    unfold rightEnd
    rw [pieceIdx_cast ht]
  have hs : segParam N τ t = (fr N t - (1 / 2 - τ / 2)) / τ := by
    unfold segParam
    rw [hloc]
  unfold homVal homReal
  rw [hloc, hl, hr, hs, realMap_eqOn _ htI]

include hseg hspace in
theorem realMap_homSphereLoop (t : ℝ) :
    realMap (homSphereLoop F hseg hspace hu hτ).data t = homReal sc N τ u t := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  set g : ℝ → Ambient n := fun t =>
    realMap (homSphereLoop F hseg hspace hu hτ).data t - homReal sc N τ u t with hg
  have hgp : Function.Periodic g 1 := by
    intro s
    simp only [hg]
    rw [realMap_periodic, homReal_add_one sc hN']
  obtain ⟨y, hy, hgy⟩ := hgp.exists_mem_Ico₀ one_pos t
  have h0 : g y = 0 := by
    simp only [hg]
    rw [realMap_homSphereLoop_of_mem F hseg hspace hu hτ hy, sub_self]
  have h1 : g t = 0 := hgy.trans h0
  simp only [hg] at h1
  exact sub_eq_zero.mp h1

include hseg hspace in
/-- Rotating the loop by 1/N rotates the homotopy by 1/N. -/
theorem homSphereLoop_rotate :
    homSphereLoop F hseg hspace (u := (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ u)
      ((energy_vadd F _ u).trans_lt hu) hτ =
      (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ homSphereLoop F hseg hspace hu hτ := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  apply sphereCircleMap_injective n
  apply ContinuousMap.ext
  intro x
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [sphereCircleMap_vadd]
  apply Subtype.ext
  rw [sphereCircleMap_val, sphereCircleMap_val]
  have h1 := realMap_homSphereLoop F hseg hspace
    ((energy_vadd F (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) u).trans_lt hu) hτ t
  have h2 := realMap_homSphereLoop F hseg hspace hu hτ (t + 1 / N)
  rw [realMap_apply] at h1 h2
  rw [show (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +
      (t : SobolevCircleRepresentative.Circle) =
      ((t + 1 / N : ℝ) : SobolevCircleRepresentative.Circle) by rw [add_comm]; rfl]
  rw [h1, h2, homReal_rotate sc hN']

end Rotation

theorem pt_reverse (u : SphereLoop n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    pt (reverseSphere u) x = pt u (1 - x) := by
  have hx' : 1 - x ∈ Icc (0 : ℝ) 1 := reflection_mem_Icc hx
  apply Subtype.ext
  rw [pt_coe _ hx, pt_coe _ hx']
  exact representative_reverseData (u.data : Space n) hx

theorem rep_reverse (u : SphereLoop n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative ((reverseSphere u).data : Space n) t =
      continuousRepresentative (u.data : Space n) (1 - t) :=
  representative_reverseData (u.data : Space n) ht

theorem natCast_rev_real {N k : ℕ} (hk : k < N) : ((N - 1 - k : ℕ) : ℝ) = N - 1 - k := by
  rw [Nat.cast_sub (by omega : k ≤ N - 1), Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]

theorem one_sub_leftEnd {N k : ℕ} (hN : (0 : ℝ) < N) (hk : k < N) (τ : ℝ) :
    1 - leftEnd N τ k = rightEnd N τ (N - 1 - k) := by
  unfold leftEnd rightEnd
  rw [natCast_rev_real hk]
  field_simp
  ring

theorem one_sub_rightEnd {N k : ℕ} (hN : (0 : ℝ) < N) (hk : k < N) (τ : ℝ) :
    1 - rightEnd N τ k = leftEnd N τ (N - 1 - k) := by
  unfold leftEnd rightEnd
  rw [natCast_rev_real hk]
  field_simp
  ring

/-- Inside a piece, reflection maps the piece k to the piece N − 1 − k. -/
theorem piece_reflect {N k : ℕ} (hk : k < N) {t : ℝ}
    (ht : t ∈ Ioo ((k : ℝ) / N) (((k : ℝ) + 1) / N)) :
    pieceIdx N (1 - t) = N - 1 - k ∧ pieceLoc N (1 - t) = 1 - ((N : ℝ) * t - k) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hj : N - 1 - k < N := by omega
  have h1 := ht.1
  have h2 := ht.2
  rw [div_lt_iff₀ hN] at h1
  rw [lt_div_iff₀ hN] at h2
  have hmem : 1 - t ∈ Ico (((N - 1 - k : ℕ) : ℝ) / N) ((((N - 1 - k : ℕ) : ℝ) + 1) / N) := by
    rw [natCast_rev_real hk]
    constructor
    · rw [div_le_iff₀ hN]
      nlinarith
    · rw [lt_div_iff₀ hN]
      nlinarith
  have hidx := pieceIdx_eq hj hmem
  refine ⟨hidx, ?_⟩
  unfold pieceLoc
  rw [hidx, natCast_rev_real hk]
  ring

/-- Off the straightened set, the reflected time is off the straightened set too. -/
theorem loc_reflect_ge {N : ℕ} [NeZero N] {τ t : ℝ} (hτ : τ ≤ 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (h : τ / 2 ≤ |pieceLoc N t - 1 / 2|) : τ / 2 ≤ |pieceLoc N (1 - t) - 1 / 2| := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk := pieceIdx_lt hN t
  have hpiece := mem_piece hN ht
  have hloc : pieceLoc N t = (N : ℝ) * t - pieceIdx N t := rfl
  rcases eq_or_lt_of_le hpiece.1 with h0 | h0
  · -- t = k/N: 1 − t = (N − k)/N is an end of a piece
    have e : (pieceIdx N t : ℝ) = N * t := by
      field_simp at h0
      linarith
    have hte : 1 - t = (((N - 1 - pieceIdx N t : ℕ) : ℝ) + 1) / N := by
      rw [natCast_rev_real hk, eq_div_iff hN'.ne']
      linarith
    rw [hte, abs_loc_piece_end (by omega : N - 1 - pieceIdx N t < N)]
    linarith
  rcases eq_or_lt_of_le hpiece.2 with h1 | h1
  · -- t = (k+1)/N: 1 − t = (N − 1 − k)/N is the start of a piece or 0
    have e : (pieceIdx N t : ℝ) + 1 = N * t := by
      field_simp at h1
      linarith
    have hte : 1 - t = ((N - 1 - pieceIdx N t : ℕ) : ℝ) / N := by
      rw [natCast_rev_real hk, eq_div_iff hN'.ne']
      linarith
    rcases Nat.eq_zero_or_pos (N - 1 - pieceIdx N t) with hz | hz
    · rw [hte, hz, Nat.cast_zero, zero_div, pieceLoc_zero,
        show |(0 : ℝ) - 1 / 2| = 1 / 2 by norm_num]
      linarith
    · have hj : N - 1 - pieceIdx N t - 1 < N := by omega
      have hte' : 1 - t = (((N - 1 - pieceIdx N t - 1 : ℕ) : ℝ) + 1) / N := by
        rw [hte]
        congr 1
        rw [Nat.cast_sub (by omega : 1 ≤ N - 1 - pieceIdx N t), Nat.cast_one]
        ring
      rw [hte', abs_loc_piece_end hj]
      linarith
  · have hr := (piece_reflect hk ⟨h0, h1⟩).2
    rw [hr, ← hloc, show 1 - pieceLoc N t - 1 / 2 = -(pieceLoc N t - 1 / 2) by ring, abs_neg]
    exact h

section Reversal

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      Finsler.SphereDistance.minEnergy F P Q)
  (hrev : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
    sc Q P s = sc P Q (1 - s))
  {N : ℕ} [NeZero N] {a : ℝ}
  (hspace : ∀ u : SphereLoop n, energy F u < a ^ 2 →
    ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖ < δ)
  {u : SphereLoop n} (hu : energy F u < a ^ 2) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1)

include hseg hrev hspace hu hτ in
/-- The homotopy of the reversed loop at t is the homotopy of the loop at 1 − t. -/
theorem homVal_reverse {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    homVal sc N τ (reverseSphere u) t = homVal sc N τ u (1 - t) := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hu' : energy F (reverseSphere u) < a ^ 2 := (energy_reverseSphere F u).trans_lt hu
  have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := reflection_mem_Icc ht
  by_cases h : τ / 2 ≤ |pieceLoc N t - 1 / 2|
  · rw [homVal_eq_rep F hseg hspace hu' hτ ht h, rep_reverse u ht,
      homVal_eq_rep F hseg hspace hu hτ ht' (loc_reflect_ge hτ.2 ht h)]
  · rw [not_le] at h
    have hτ0 : 0 < τ := by
      have := abs_nonneg (pieceLoc N t - 1 / 2)
      linarith
    have hk := pieceIdx_lt hN t
    have hpiece := mem_piece hN ht
    have hloc : pieceLoc N t = (N : ℝ) * t - pieceIdx N t := rfl
    have hl0 : 0 < pieceLoc N t := by
      rw [abs_lt] at h
      linarith [hτ.2]
    have hl1 : pieceLoc N t < 1 := by
      rw [abs_lt] at h
      linarith [hτ.2]
    have hin : t ∈ Ioo ((pieceIdx N t : ℝ) / N) (((pieceIdx N t : ℝ) + 1) / N) := by
      constructor
      · rw [div_lt_iff₀ hN']
        linarith
      · rw [lt_div_iff₀ hN']
        linarith
    obtain ⟨hidx', hloc'⟩ := piece_reflect hk hin
    rw [← hloc] at hloc'
    have hlt' : |pieceLoc N (1 - t) - 1 / 2| ≤ τ / 2 := by
      rw [hloc', show 1 - pieceLoc N t - 1 / 2 = -(pieceLoc N t - 1 / 2) by ring, abs_neg]
      exact h.le
    have hj : N - 1 - pieceIdx N t < N := by omega
    have hshort := chord_short F hspace hu hτ hj
    have hlI : leftEnd N τ (pieceIdx N t) ∈ Icc (0 : ℝ) 1 :=
      piece_mem_Icc hk hN' ⟨leftEnd_ge hN' hτ.2 _,
        (leftEnd_le_rightEnd hN' hτ.1 _).trans (rightEnd_le hN' hτ.2 _)⟩
    have hrI : rightEnd N τ (pieceIdx N t) ∈ Icc (0 : ℝ) 1 :=
      piece_mem_Icc hk hN' ⟨(leftEnd_ge hN' hτ.2 _).trans (leftEnd_le_rightEnd hN' hτ.1 _),
        rightEnd_le hN' hτ.2 _⟩
    have hP : pt (reverseSphere u) (leftEnd N τ (pieceIdx N t)) =
        pt u (rightEnd N τ (N - 1 - pieceIdx N t)) := by
      rw [pt_reverse u hlI, one_sub_leftEnd hN' hk]
    have hQ : pt (reverseSphere u) (rightEnd N τ (pieceIdx N t)) =
        pt u (leftEnd N τ (N - 1 - pieceIdx N t)) := by
      rw [pt_reverse u hrI, one_sub_rightEnd hN' hk]
    have hs : segParam N τ (1 - t) = 1 - segParam N τ t := by
      unfold segParam
      rw [hloc']
      field_simp
      ring
    have hsI : segParam N τ t ∈ Icc (0 : ℝ) 1 :=
      Finsler.MilnorContinuity.segParam_mem hτ0 h.le
    unfold homVal
    rw [ite_eq_left h.le, ite_eq_left hlt', hidx', hP, hQ, hs]
    exact hrev _ _ hshort _ hsI

include hseg hrev hspace in
/-- The homotopy of the reversed loop is the reversed homotopy. -/
theorem homSphereLoop_reverse :
    homSphereLoop F hseg hspace (u := reverseSphere u) ((energy_reverseSphere F u).trans_lt hu) hτ =
      reverseSphere (homSphereLoop F hseg hspace hu hτ) := by
  apply sphereLoop_eq_of_representative_eq
  intro t
  rw [sphereRepresentative_reverseSphere]
  apply Subtype.ext
  change continuousRepresentative (homLoop F hseg hspace
      ((energy_reverseSphere F u).trans_lt hu) hτ) t =
    continuousRepresentative (homLoop F hseg hspace hu hτ) (reflectionInterval t)
  rw [representative_homLoop F hseg hspace _ hτ t.2,
    representative_homLoop F hseg hspace hu hτ (reflectionInterval t).2]
  exact homVal_reverse F hseg hrev hspace hu hτ t.2

end Reversal

/-- Sampling commutes with the rotation by 1/N. -/
theorem samplePoly_rotate {N : ℕ} [NeZero N] (u : SphereLoop n) :
    samplePoly N ((((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ u) =
      rotatePolygon (samplePoly N u) := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  funext i
  apply Subtype.ext
  have hk : i.val < N := ZMod.val_lt i
  have hi : ((i.val : ℕ) : ZMod N) = i := ZMod.natCast_zmod_val i
  have h1 : (samplePoly N ((((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ u) i :
      Ambient n) = continuousRepresentative
        (((((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ u).data : Space n)
        ((i.val : ℝ) / N) := by
    have := sampleN_natCast ((((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ u) hk
    rw [hi] at this
    exact this
  have h2 : (rotatePolygon (samplePoly N u) i : Ambient n) =
      continuousRepresentative (u.data : Space n) (((i.val : ℝ) + 1) / N) := by
    have := sampleN_natCast_succ u hk
    rw [hi] at this
    exact this
  have hs : (i.val : ℝ) / N ∈ Icc (0 : ℝ) 1 := (sampleTime N i).2
  have ht : ((i.val : ℝ) + 1) / N ∈ Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hN']
      exact_mod_cast hk
  rw [h1, h2, ← realMap_eqOn _ hs, ← realMap_eqOn _ ht, realMap_vadd]
  congr 1
  ring

/-- Sampling commutes with the reversal. -/
theorem samplePoly_reverse {N : ℕ} [NeZero N] (u : SphereLoop n) :
    samplePoly N (reverseSphere u) = reversePolygon (samplePoly N u) := by
  have hN := Nat.pos_of_neZero N
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  funext i
  apply Subtype.ext
  have hk : i.val < N := ZMod.val_lt i
  have hi : ((i.val : ℕ) : ZMod N) = i := ZMod.natCast_zmod_val i
  have h1 : (samplePoly N (reverseSphere u) i : Ambient n) =
      continuousRepresentative ((reverseSphere u).data : Space n) ((i.val : ℝ) / N) := by
    have := sampleN_natCast (reverseSphere u) hk
    rw [hi] at this
    exact this
  have hs : (i.val : ℝ) / N ∈ Icc (0 : ℝ) 1 := (sampleTime N i).2
  have hneg : -i = ((N - 1 - i.val : ℕ) : ZMod N) + 1 := by
    rw [natCast_rev hk, hi]
    ring
  have h2 : (samplePoly N u (((N - 1 - i.val : ℕ) : ZMod N) + 1) : Ambient n) =
      continuousRepresentative (u.data : Space n) ((((N - 1 - i.val : ℕ) : ℝ) + 1) / N) :=
    sampleN_natCast_succ u (by omega : N - 1 - i.val < N)
  rw [h1, rep_reverse u hs]
  change _ = (samplePoly N u (-i) : Ambient n)
  rw [hneg, h2]
  congr 1
  rw [natCast_rev_real hk]
  field_simp
  ring

section Global

variable (F : ReversibleMetric n) {δ : ℝ} {sc sv : Sphere n → Sphere n → ℝ → Ambient n}
  (hseg : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ →
    (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (sc P Q) (sv P Q t) t) ∧
    ContinuousOn (sv P Q) (Icc 0 1) ∧ sc P Q 0 = P ∧ sc P Q 1 = Q ∧
    (∀ t, ‖sc P Q t‖ = 1) ∧
    ∫ t in (0 : ℝ)..1, Finsler.AmbientLagrangian.lagrangian F (sc P Q t, sv P Q t) =
      Finsler.SphereDistance.minEnergy F P Q)
  (hrev : ∀ P Q : Sphere n, ‖(Q : Ambient n) - P‖ < δ → ∀ s ∈ Icc (0 : ℝ) 1,
    sc Q P s = sc P Q (1 - s))
  {N : ℕ} [NeZero N] {a : ℝ}
  (hspace : ∀ u : SphereLoop n, energy F u < a ^ 2 →
    ∀ s t : ℝ, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖continuousRepresentative (u.data : Space n) t -
        continuousRepresentative (u.data : Space n) s‖ < δ)

theorem milnorH_of_not {p : ℝ × SphereLoop n}
    (h : ¬ (p.1 ∈ Icc (0 : ℝ) 1 ∧ energy F p.2 < a ^ 2)) : milnorH F hseg hspace p = p.2 :=
  dite_eq_right h

/-- The straightening homotopy commutes with the rotation by 1/N. -/
theorem milnorH_rotate (p : ℝ × SphereLoop n) :
    milnorH F hseg hspace (p.1, (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ p.2) =
      (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ milnorH F hseg hspace p := by
  by_cases h : p.1 ∈ Icc (0 : ℝ) 1 ∧ energy F p.2 < a ^ 2
  · rw [milnorH_of_mem F hseg hspace
      (p := (p.1, (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ p.2))
      ⟨h.1, (energy_vadd F _ p.2).trans_lt h.2⟩, milnorH_of_mem F hseg hspace h]
    exact homSphereLoop_rotate F hseg hspace h.2 h.1
  · have h' : ¬ ((p.1, (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ p.2).1 ∈
        Icc (0 : ℝ) 1 ∧
        energy F (p.1, (((1 / N : ℝ)) : SobolevCircleRepresentative.Circle) +ᵥ p.2).2 < a ^ 2) := by
      intro h''
      exact h ⟨h''.1, (energy_vadd F _ p.2).symm.trans_lt h''.2⟩
    rw [milnorH_of_not F hseg hspace h', milnorH_of_not F hseg hspace h]

include hrev in
/-- The straightening homotopy commutes with the reversal. -/
theorem milnorH_reverse (p : ℝ × SphereLoop n) :
    milnorH F hseg hspace (p.1, reverseSphere p.2) = reverseSphere (milnorH F hseg hspace p) := by
  by_cases h : p.1 ∈ Icc (0 : ℝ) 1 ∧ energy F p.2 < a ^ 2
  · rw [milnorH_of_mem F hseg hspace (p := (p.1, reverseSphere p.2))
      ⟨h.1, (energy_reverseSphere F p.2).trans_lt h.2⟩, milnorH_of_mem F hseg hspace h]
    exact homSphereLoop_reverse F hseg hrev hspace h.2 h.1
  · have h' : ¬ ((p.1, reverseSphere p.2).1 ∈ Icc (0 : ℝ) 1 ∧
        energy F (p.1, reverseSphere p.2).2 < a ^ 2) := by
      intro h''
      exact h ⟨h''.1, (energy_reverseSphere F p.2).symm.trans_lt h''.2⟩
    rw [milnorH_of_not F hseg hspace h', milnorH_of_not F hseg hspace h]

end Global

end

end Finsler.MilnorEquivariance
