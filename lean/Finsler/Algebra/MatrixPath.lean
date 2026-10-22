module

public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Paths of invertible real matrices. Two real square matrices are joined if there is a
continuous path of invertible matrices from one to the other. Products of joined matrices are
joined. A transvection is joined to the identity, hence so is every product of transvections; a
diagonal matrix with nonzero entries is joined to the diagonal matrix of the signs of its
entries. Since every matrix is a product of transvections, a diagonal matrix and transvections,
the square of an invertible matrix is joined to the identity, and so is every even power. A
matrix without real eigenvalues is joined to the identity along the segment to the identity.
Consequently the product of a matrix without real eigenvalues and an even power of an invertible
matrix is joined to the identity; this is the form in which the holonomy of a frame along a
critical circle occurs. No rotation matrices are needed. -/

@[expose] public section

namespace Finsler.MatrixPath

open Matrix Set

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two real matrices are joined by a continuous path of invertible matrices. -/
def Conn (A B : Matrix n n ℝ) : Prop :=
  ∃ γ : ℝ → Matrix n n ℝ, Continuous γ ∧ γ 0 = A ∧ γ 1 = B ∧ ∀ t, (γ t).det ≠ 0

theorem conn_refl {A : Matrix n n ℝ} (hA : A.det ≠ 0) : Conn A A :=
  ⟨fun _ => A, continuous_const, rfl, rfl, fun _ => hA⟩

theorem conn_symm {A B : Matrix n n ℝ} (h : Conn A B) : Conn B A := by
  obtain ⟨γ, hγ, h0, h1, hd⟩ := h
  refine ⟨fun t => γ (1 - t), hγ.comp (continuous_const.sub continuous_id), ?_, ?_,
    fun t => hd _⟩
  · change γ (1 - 0) = B
    rw [sub_zero, h1]
  · change γ (1 - 1) = A
    rw [sub_self, h0]

/-- Products of joined matrices are joined. -/
theorem conn_mul {A A' B B' : Matrix n n ℝ} (hA : Conn A A') (hB : Conn B B') :
    Conn (A * B) (A' * B') := by
  obtain ⟨γ, hγ, h0, h1, hd⟩ := hA
  obtain ⟨δ, hδ, k0, k1, kd⟩ := hB
  refine ⟨fun t => γ t * δ t, hγ.matrix_mul hδ, ?_, ?_, fun t => ?_⟩
  · change γ 0 * δ 0 = A * B
    rw [h0, k0]
  · change γ 1 * δ 1 = A' * B'
    rw [h1, k1]
  · rw [det_mul]
    exact mul_ne_zero (hd t) (kd t)

/-- A transvection is joined to the identity. -/
theorem conn_transvection {i j : n} (hij : i ≠ j) (c : ℝ) : Conn (transvection i j c) 1 := by
  refine ⟨fun t => transvection i j ((1 - t) * c), ?_, ?_, ?_, fun t => ?_⟩
  · have h : (fun t : ℝ => transvection i j ((1 - t) * c)) =
        fun t : ℝ => (1 : Matrix n n ℝ) + ((1 - t) * c) • Matrix.single i j (1 : ℝ) := by
      funext t
      rw [transvection, Matrix.smul_single, smul_eq_mul, mul_one]
    rw [h]
    fun_prop
  · change transvection i j ((1 - 0) * c) = transvection i j c
    rw [sub_zero, one_mul]
  · change transvection i j ((1 - 1) * c) = 1
    rw [sub_self, zero_mul, transvection_zero]
  · rw [det_transvection_of_ne _ _ hij]
    exact one_ne_zero

/-- A product of transvections is joined to the identity. -/
theorem conn_list (L : List (TransvectionStruct n ℝ)) :
    Conn (L.map TransvectionStruct.toMatrix).prod 1 := by
  induction L with
  | nil =>
    rw [List.map_nil, List.prod_nil]
    exact conn_refl (by rw [det_one]; exact one_ne_zero)
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons]
    have h := conn_mul (conn_transvection t.hij t.c) ih
    rw [mul_one] at h
    exact h

/-- The sign of a real number as a real number: 1 for positive numbers and −1 otherwise. -/
def sgn (x : ℝ) : ℝ := if 0 < x then 1 else -1

theorem sgn_mul_sgn (x : ℝ) : sgn x * sgn x = 1 := by
  unfold sgn
  split_ifs <;> norm_num

/-- A convex combination of a nonzero number and its sign is not zero. -/
theorem combo_ne_zero {x τ : ℝ} (hx : x ≠ 0) (h0 : 0 ≤ τ) (h1 : τ ≤ 1) :
    (1 - τ) * x + τ * sgn x ≠ 0 := by
  unfold sgn
  split_ifs with h
  · rcases eq_or_lt_of_le h1 with e | e
    · rw [e]
      norm_num
    · have h3 : 0 < (1 - τ) * x := mul_pos (sub_pos.mpr e) h
      exact ne_of_gt (by nlinarith)
  · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp h) hx
    rcases eq_or_lt_of_le h1 with e | e
    · rw [e]
      norm_num
    · have h3 : (1 - τ) * x < 0 := mul_neg_of_pos_of_neg (sub_pos.mpr e) hneg
      exact ne_of_lt (by nlinarith)

/-- A diagonal matrix with nonzero entries is joined to the diagonal matrix of the signs. -/
theorem conn_diagonal (d : n → ℝ) (hd : ∀ i, d i ≠ 0) :
    Conn (diagonal d) (diagonal fun i => sgn (d i)) := by
  refine ⟨fun t => diagonal fun i => (1 - max 0 (min 1 t)) * d i + max 0 (min 1 t) * sgn (d i),
    ?_, ?_, ?_, fun t => ?_⟩
  · refine Continuous.matrix_diagonal (continuous_pi fun i => ?_)
    fun_prop
  · change (diagonal fun i => (1 - max 0 (min 1 (0 : ℝ))) * d i +
      max 0 (min 1 (0 : ℝ)) * sgn (d i)) = diagonal d
    rw [min_eq_right (zero_le_one : (0 : ℝ) ≤ 1), max_self]
    congr 1
    funext i
    ring
  · change (diagonal fun i => (1 - max 0 (min 1 (1 : ℝ))) * d i +
      max 0 (min 1 (1 : ℝ)) * sgn (d i)) = diagonal fun i => sgn (d i)
    rw [min_self, max_eq_right (zero_le_one : (0 : ℝ) ≤ 1)]
    congr 1
    funext i
    ring
  · rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      combo_ne_zero (hd i) (le_max_left _ _) (max_le zero_le_one (min_le_left _ _))

/-- An invertible real matrix is joined to a diagonal matrix of signs. -/
theorem exists_conn_sign {A : Matrix n n ℝ} (hA : A.det ≠ 0) :
    ∃ D : n → ℝ, Conn A (diagonal fun i => sgn (D i)) := by
  obtain ⟨L, L', D, hD⟩ := Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec A
  have hD0 : ∀ i, D i ≠ 0 := by
    intro i hi
    apply hA
    rw [hD, det_mul, det_mul, det_diagonal, Finset.prod_eq_zero (Finset.mem_univ i) hi,
      mul_zero, zero_mul]
  refine ⟨D, ?_⟩
  have h := conn_mul (conn_mul (conn_list L) (conn_diagonal D hD0)) (conn_list L')
  rw [← hD, one_mul, mul_one] at h
  exact h

/-- The square of an invertible real matrix is joined to the identity. -/
theorem conn_sq {A : Matrix n n ℝ} (hA : A.det ≠ 0) : Conn (A * A) 1 := by
  obtain ⟨D, h⟩ := exists_conn_sign hA
  have h2 := conn_mul h h
  have hs : (diagonal fun i => sgn (D i)) * (diagonal fun i => sgn (D i)) =
      (1 : Matrix n n ℝ) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact sgn_mul_sgn (D i)
  rw [hs] at h2
  exact h2

/-- An even power of an invertible real matrix is joined to the identity. -/
theorem conn_pow_even {A : Matrix n n ℝ} (hA : A.det ≠ 0) (r : ℕ) : Conn (A ^ (2 * r)) 1 := by
  have h : A ^ (2 * r) = A ^ r * A ^ r := by rw [two_mul, pow_add]
  rw [h]
  exact conn_sq (by rw [det_pow]; exact pow_ne_zero r hA)

/-- A real matrix without real eigenvalues is joined to the identity. -/
theorem conn_of_no_real_eigenvalue {R : Matrix n n ℝ}
    (h : ∀ (μ : ℝ) (v : n → ℝ), R.mulVec v = μ • v → v = 0) : Conn R 1 := by
  refine ⟨fun t => (1 - max 0 (min 1 t)) • R + max 0 (min 1 t) • (1 : Matrix n n ℝ),
    ?_, ?_, ?_, fun t => ?_⟩
  · fun_prop
  · change (1 - max 0 (min 1 (0 : ℝ))) • R + max 0 (min 1 (0 : ℝ)) • (1 : Matrix n n ℝ) = R
    rw [min_eq_right (zero_le_one : (0 : ℝ) ≤ 1), max_self, sub_zero, one_smul, zero_smul,
      add_zero]
  · change (1 - max 0 (min 1 (1 : ℝ))) • R + max 0 (min 1 (1 : ℝ)) • (1 : Matrix n n ℝ) = 1
    rw [min_self, max_eq_right (zero_le_one : (0 : ℝ) ≤ 1), sub_self, zero_smul, one_smul,
      zero_add]
  · set τ : ℝ := max 0 (min 1 t) with hτ
    have h1 : τ ≤ 1 := max_le zero_le_one (min_le_left _ _)
    intro hdet
    obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    apply hv
    have he : (1 - τ) • R.mulVec v + τ • v = 0 := by
      rw [← hv0, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
    rcases eq_or_lt_of_le h1 with e | e
    · rw [e, sub_self, zero_smul, zero_add, one_smul] at he
      exact he
    · have hpos : (0 : ℝ) < 1 - τ := sub_pos.mpr e
      apply h (-(τ / (1 - τ))) v
      have h3 : (1 - τ) • R.mulVec v = (1 - τ) • (-(τ / (1 - τ))) • v := by
        rw [smul_smul, mul_neg, mul_div_cancel₀ _ hpos.ne', neg_smul]
        exact eq_neg_of_add_eq_zero_left he
      exact smul_right_injective _ hpos.ne' h3

/-- The product of a matrix without real eigenvalues and an even power of an invertible matrix
is joined to the identity. -/
theorem conn_mul_pow_even {R A : Matrix n n ℝ}
    (hR : ∀ (μ : ℝ) (v : n → ℝ), R.mulVec v = μ • v → v = 0) (hA : A.det ≠ 0) (r : ℕ) :
    Conn (R * A ^ (2 * r)) 1 := by
  have h := conn_mul (conn_of_no_real_eigenvalue hR) (conn_pow_even hA r)
  rw [mul_one] at h
  exact h

end

end Finsler.MatrixPath
