module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.ZMod.Basic

/-! Positivity of a Jacobi operator on the families supported at isolated indices. Let H be a
symmetric operator on the L² product of copies of V indexed by the residues modulo K whose
component at i is c (T_i w_{i+1} + A_i w_i + B_i w_{i-1}) with c > 0 and injective T_i, B_i.
Suppose the quadratic form of H is nonnegative on the families vanishing on a set S of indices.
If i and one of its neighbours are outside S, then A_i is positive definite: a family supported
at i with zero form would pair to zero with the families supported at that neighbour, which
forces B_{i+1} a = 0 or T_{i-1} a = 0. Hence the form of H is positive on the nonzero families
vanishing on a set S₂ whose complement consists of such indices with both neighbours in S₂.
This is the absence of conjugate points for a minimizing chain, in the form needed for the
invariance of the nullity of a polygon when the number of vertices is doubled. -/

@[expose] public section

namespace Finsler.JacobiPositive

open scoped RealInnerProductSpace

noncomputable section

/-- If a symmetric form is nonnegative along the line w + t z and vanishes at w, then w pairs to
zero with z. -/
theorem inner_eq_zero_of_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) {w z : E}
    (hpsd : ∀ t : ℝ, 0 ≤ ⟪H (w + t • z), w + t • z⟫) (hw : ⟪H w, w⟫ = 0) : ⟪H w, z⟫ = 0 := by
  have hexp : ∀ t : ℝ, ⟪H (w + t • z), w + t • z⟫ = 2 * t * ⟪H w, z⟫ + t ^ 2 * ⟪H z, z⟫ := by
    intro t
    have hsym : ⟪H z, w⟫ = ⟪H w, z⟫ := by rw [hH z w, real_inner_comm]
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right,
      hw, hsym]
    ring
  by_contra hb
  have hs : 0 < |⟪H z, z⟫| + 1 := by positivity
  have h := hpsd (-⟪H w, z⟫ / (|⟪H z, z⟫| + 1))
  rw [hexp] at h
  have hb2 : 0 < ⟪H w, z⟫ ^ 2 := by positivity
  have hq : ⟪H z, z⟫ ≤ |⟪H z, z⟫| := le_abs_self _
  have e : 2 * (-⟪H w, z⟫ / (|⟪H z, z⟫| + 1)) * ⟪H w, z⟫ +
      (-⟪H w, z⟫ / (|⟪H z, z⟫| + 1)) ^ 2 * ⟪H z, z⟫ =
      ⟪H w, z⟫ ^ 2 * (⟪H z, z⟫ - 2 * (|⟪H z, z⟫| + 1)) / (|⟪H z, z⟫| + 1) ^ 2 := by
    field_simp
    ring
  rw [e] at h
  have hneg : ⟪H w, z⟫ ^ 2 * (⟪H z, z⟫ - 2 * (|⟪H z, z⟫| + 1)) / (|⟪H z, z⟫| + 1) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos
    · nlinarith [abs_nonneg ⟪H z, z⟫]
    · positivity
  linarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {K : ℕ} [NeZero K]

/-- The inner product with a family supported at one index. -/
theorem inner_single (x : PiLp 2 (fun _ : ZMod K => V)) (j : ZMod K) (η : V) :
    ⟪x, (PiLp.single 2 j η : PiLp 2 (fun _ : ZMod K => V))⟫ = ⟪x j, η⟫ := by
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro b _ hb
    rw [PiLp.single_eq_of_ne 2 hb, inner_zero_right]
  · intro h
    exact absurd (Finset.mem_univ j) h

section Jacobi

variable (H : PiLp 2 (fun _ : ZMod K => V) →ₗ[ℝ] PiLp 2 (fun _ : ZMod K => V))
  (T A B : ZMod K → V →ₗ[ℝ] V) {c : ℝ}
  (hJ : ∀ (w : PiLp 2 (fun _ : ZMod K => V)) (i : ZMod K),
    H w i = c • (T i (w (i + 1)) + A i (w i) + B i (w (i - 1))))
  (h10 : (1 : ZMod K) ≠ 0) (h20 : (2 : ZMod K) ≠ 0)

include hJ h10 in
/-- The form at a family supported at one index. -/
theorem inner_single_self (i : ZMod K) (a : V) :
    ⟪H (PiLp.single 2 i a), (PiLp.single 2 i a : PiLp 2 (fun _ : ZMod K => V))⟫ =
      c * ⟪A i a, a⟫ := by
  have h1 : i + 1 ≠ i := fun h => h10 (by simpa using h)
  have h2 : i - 1 ≠ i := fun h => h10 (by
    have h' : i - (i - 1) = i - i := congrArg (fun t => i - t) h
    simpa using h')
  rw [inner_single, hJ, PiLp.single_eq_same, PiLp.single_eq_of_ne 2 h1,
    PiLp.single_eq_of_ne 2 h2, map_zero, map_zero, zero_add, add_zero, real_inner_smul_left]

include hJ h10 h20 in
/-- The pairing of a family supported at i with a family supported at i + 1. -/
theorem inner_single_succ (i : ZMod K) (a η : V) :
    ⟪H (PiLp.single 2 i a), (PiLp.single 2 (i + 1) η : PiLp 2 (fun _ : ZMod K => V))⟫ =
      c * ⟪B (i + 1) a, η⟫ := by
  have h1 : i + 1 + 1 ≠ i := fun h => h20 (by
    have h' : i + 2 = i := by
      rw [show i + 2 = i + 1 + 1 by ring]
      exact h
    simpa using h')
  have h2 : i + 1 ≠ i := fun h => h10 (by simpa using h)
  rw [inner_single, hJ, PiLp.single_eq_of_ne 2 h1, PiLp.single_eq_of_ne 2 h2,
    add_sub_cancel_right, PiLp.single_eq_same, map_zero, map_zero, zero_add, zero_add,
    real_inner_smul_left]

include hJ h10 h20 in
/-- The pairing of a family supported at i with a family supported at i - 1. -/
theorem inner_single_pred (i : ZMod K) (a η : V) :
    ⟪H (PiLp.single 2 i a), (PiLp.single 2 (i - 1) η : PiLp 2 (fun _ : ZMod K => V))⟫ =
      c * ⟪T (i - 1) a, η⟫ := by
  have h1 : i - 1 - 1 ≠ i := fun h => h20 (by
    have h' : i - (i - 1 - 1) = i - i := congrArg (fun t => i - t) h
    have h'' : i - (i - 1 - 1) = 2 := by ring
    rw [h'', sub_self] at h'
    exact h')
  have h2 : i - 1 ≠ i := fun h => h10 (by
    have h' : i - (i - 1) = i - i := congrArg (fun t => i - t) h
    simpa using h')
  rw [inner_single, hJ, sub_add_cancel, PiLp.single_eq_same, PiLp.single_eq_of_ne 2 h2,
    PiLp.single_eq_of_ne 2 h1, map_zero, map_zero, add_zero, add_zero, real_inner_smul_left]

variable (hH : H.IsSymmetric) (hc : 0 < c) (S : Set (ZMod K))
  (hpsd : ∀ z : PiLp 2 (fun _ : ZMod K => V), (∀ i ∈ S, z i = 0) → 0 ≤ ⟪H z, z⟫)
  (hT : ∀ i, Function.Injective (T i)) (hB : ∀ i, Function.Injective (B i))

include hJ h10 h20 hH hc hpsd hT hB in
/-- **Positivity of the diagonal block** at an index which, with one of its neighbours, lies
outside the set where the families are required to vanish. -/
theorem diag_pos {i : ZMod K} (hi : i ∉ S) (hn : i + 1 ∉ S ∨ i - 1 ∉ S) {a : V} (ha : a ≠ 0) :
    0 < ⟪A i a, a⟫ := by
  have hsupp : ∀ (j : ZMod K) (η : V), j ∉ S → ∀ l ∈ S,
      (PiLp.single 2 j η : PiLp 2 (fun _ : ZMod K => V)) l = 0 := by
    intro j η hj l hl
    have hlj : l ≠ j := fun h => hj (h ▸ hl)
    rw [PiLp.single_eq_of_ne 2 hlj]
  have h0 : 0 ≤ ⟪A i a, a⟫ := by
    have h := hpsd (PiLp.single 2 i a) (hsupp i a hi)
    rw [inner_single_self H T A B hJ h10] at h
    exact nonneg_of_mul_nonneg_right h hc
  refine lt_of_le_of_ne h0 fun hzero => ha ?_
  have hw : ⟪H (PiLp.single 2 i a), (PiLp.single 2 i a : PiLp 2 (fun _ : ZMod K => V))⟫ = 0 := by
    rw [inner_single_self H T A B hJ h10, ← hzero, mul_zero]
  have hline : ∀ (j : ZMod K) (η : V), j ∉ S → ∀ t : ℝ,
      0 ≤ ⟪H (PiLp.single 2 i a + t • PiLp.single 2 j η),
        (PiLp.single 2 i a + t • PiLp.single 2 j η : PiLp 2 (fun _ : ZMod K => V))⟫ := by
    intro j η hj t
    refine hpsd _ fun l hl => ?_
    change (PiLp.single 2 i a : PiLp 2 (fun _ : ZMod K => V)) l +
      t • (PiLp.single 2 j η : PiLp 2 (fun _ : ZMod K => V)) l = 0
    rw [hsupp i a hi l hl, hsupp j η hj l hl, smul_zero, add_zero]
  rcases hn with hn | hn
  · have h := inner_eq_zero_of_nonneg H hH (hline (i + 1) (B (i + 1) a) hn) hw
    rw [inner_single_succ H T A B hJ h10 h20] at h
    have h' : ⟪B (i + 1) a, B (i + 1) a⟫ = 0 := (mul_eq_zero.mp h).resolve_left hc.ne'
    have h'' : B (i + 1) a = 0 := inner_self_eq_zero.mp h'
    exact hB (i + 1) (h''.trans (map_zero _).symm)
  · have h := inner_eq_zero_of_nonneg H hH (hline (i - 1) (T (i - 1) a) hn) hw
    rw [inner_single_pred H T A B hJ h10 h20] at h
    have h' : ⟪T (i - 1) a, T (i - 1) a⟫ = 0 := (mul_eq_zero.mp h).resolve_left hc.ne'
    have h'' : T (i - 1) a = 0 := inner_self_eq_zero.mp h'
    exact hT (i - 1) (h''.trans (map_zero _).symm)

include hJ h10 h20 hH hc hpsd hT hB in
/-- **Positivity on the families supported at isolated indices.** -/
theorem inner_pos (S₂ : Set (ZMod K))
    (hS₂ : ∀ i, i ∉ S₂ → i + 1 ∈ S₂ ∧ i - 1 ∈ S₂ ∧ i ∉ S ∧ (i + 1 ∉ S ∨ i - 1 ∉ S))
    {u : PiLp 2 (fun _ : ZMod K => V)} (hu : ∀ i ∈ S₂, u i = 0) (hne : u ≠ 0) :
    0 < ⟪H u, u⟫ := by
  classical
  have hterm : ∀ i : ZMod K, ⟪H u i, u i⟫ = c * ⟪A i (u i), u i⟫ := by
    intro i
    by_cases hi : i ∈ S₂
    · rw [hu i hi, inner_zero_right, inner_zero_right, mul_zero]
    · obtain ⟨h1, h2, -, -⟩ := hS₂ i hi
      rw [hJ, hu _ h1, hu _ h2, map_zero, map_zero, zero_add, add_zero, real_inner_smul_left]
  have hnonneg : ∀ i : ZMod K, 0 ≤ c * ⟪A i (u i), u i⟫ := by
    intro i
    by_cases hi : i ∈ S₂
    · rw [hu i hi, inner_zero_right, mul_zero]
    · by_cases h0 : u i = 0
      · rw [h0, inner_zero_right, mul_zero]
      · obtain ⟨-, -, h3, h4⟩ := hS₂ i hi
        exact (mul_pos hc (diag_pos H T A B hJ h10 h20 hH hc S hpsd hT hB h3 h4 h0)).le
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra hall
    exact hne (PiLp.ext fun i => by
      by_contra h
      exact hall ⟨i, h⟩)
  have hi₀S : i₀ ∉ S₂ := fun h => hi₀ (hu i₀ h)
  obtain ⟨-, -, h3, h4⟩ := hS₂ i₀ hi₀S
  rw [PiLp.inner_apply]
  simp only [hterm]
  exact Finset.sum_pos' (fun i _ => hnonneg i)
    ⟨i₀, Finset.mem_univ _, mul_pos hc (diag_pos H T A B hJ h10 h20 hH hc S hpsd hT hB h3 h4 hi₀)⟩

end Jacobi

end

end Finsler.JacobiPositive
