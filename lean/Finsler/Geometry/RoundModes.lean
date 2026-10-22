module

public import Finsler.Geometry.RoundPolygon

/-! The Fourier modes of the circulant second variation, without trigonometric sums.

On polygons w : Z/N → ℝⁿ⁺¹ with the ℓ² pairing ⟪w, w'⟫ = Σ ⟪w_i, w'_i⟫, the averaged shift
(T w)_i = (w_{i+1} + w_{i−1})/2 is symmetric, and the circulant form of the normal second
variation is S_c(w) = Σ ⟪w_i, w_{i+1}⟫ − c Σ ‖w_i‖² = ⟪w, T w⟫ − c ⟪w, w⟫. The polygon
regular N j a b (vertices cos(2πjk/N) a + sin(2πjk/N) b, any a, b) is an eigenvector of T with
eigenvalue cos(2πj/N) (this is `regular_sub_add`). Eigenvectors for different eigenvalues are
orthogonal because T is symmetric, so for v = Σ_j v_j with eigenvalues λ_j pairwise distinct

  S_c(v) = Σ_j (λ_j − c) ‖v_j‖²,   ‖v‖² = Σ_j ‖v_j‖².

No orthogonality relation of discrete trigonometric sums is needed. -/

@[expose] public section

namespace Finsler.RoundModes

open Finsler.SphereGeometry Finsler.RoundPolygon
open Finset
open scoped RealInnerProductSpace Real

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-- The ℓ² pairing of polygons. -/
def pair (w w' : ZMod N → Ambient n) : ℝ := ∑ i : ZMod N, ⟪w i, w' i⟫

/-- The averaged shift. -/
def avg (w : ZMod N → Ambient n) : ZMod N → Ambient n := fun i => (1 / 2 : ℝ) • (w (i + 1) + w (i - 1))

/-- The circulant form of the normal second variation. -/
def circForm (c : ℝ) (w : ZMod N → Ambient n) : ℝ :=
  ∑ i : ZMod N, ⟪w i, w (i + 1)⟫ - c * ∑ i : ZMod N, ‖w i‖ ^ 2

theorem pair_comm (w w' : ZMod N → Ambient n) : pair w w' = pair w' w := by
  unfold pair
  exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _

theorem pair_self (w : ZMod N → Ambient n) : pair w w = ∑ i : ZMod N, ‖w i‖ ^ 2 := by
  unfold pair
  exact Finset.sum_congr rfl fun i _ => real_inner_self_eq_norm_sq _

theorem pair_self_nonneg (w : ZMod N → Ambient n) : 0 ≤ pair w w := by
  rw [pair_self]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem pair_add_left (w₁ w₂ w' : ZMod N → Ambient n) :
    pair (w₁ + w₂) w' = pair w₁ w' + pair w₂ w' := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply, inner_add_left]

theorem pair_smul_left (r : ℝ) (w w' : ZMod N → Ambient n) :
    pair (r • w) w' = r * pair w w' := by
  unfold pair
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, real_inner_smul_left]

theorem pair_sum_left {ι : Type*} (s : Finset ι) (v : ι → ZMod N → Ambient n)
    (w' : ZMod N → Ambient n) : pair (∑ j ∈ s, v j) w' = ∑ j ∈ s, pair (v j) w' := by
  unfold pair
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_apply, sum_inner]

theorem shift_sum {M : Type*} [AddCommMonoid M] (f : ZMod N → M) (s : ZMod N) :
    ∑ i : ZMod N, f (i + s) = ∑ i : ZMod N, f i :=
  Equiv.sum_comp (Equiv.addRight s) f

theorem shift_sum_sub {M : Type*} [AddCommMonoid M] (f : ZMod N → M) (s : ZMod N) :
    ∑ i : ZMod N, f (i - s) = ∑ i : ZMod N, f i :=
  Equiv.sum_comp (Equiv.subRight s) f

/-- The averaged shift is symmetric. -/
theorem pair_avg (w w' : ZMod N → Ambient n) : pair (avg w) w' = pair w (avg w') := by
  unfold pair avg
  simp only [real_inner_smul_left, real_inner_smul_right, inner_add_left, inner_add_right,
    ← Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  have h1 : ∑ i : ZMod N, ⟪w (i + 1), w' i⟫ = ∑ i : ZMod N, ⟪w i, w' (i - 1)⟫ := by
    rw [← shift_sum (fun i => ⟪w i, w' (i - 1)⟫) 1]
    simp only [add_sub_cancel_right]
  have h2 : ∑ i : ZMod N, ⟪w (i - 1), w' i⟫ = ∑ i : ZMod N, ⟪w i, w' (i + 1)⟫ := by
    rw [← shift_sum_sub (fun i => ⟪w i, w' (i + 1)⟫) 1]
    simp only [sub_add_cancel]
  rw [h1, h2]
  ring

/-- The circulant form is ⟪w, T w⟫ − c ⟪w, w⟫. -/
theorem circForm_eq (c : ℝ) (w : ZMod N → Ambient n) :
    circForm c w = pair w (avg w) - c * pair w w := by
  unfold circForm
  rw [pair_self]
  congr 1
  unfold pair avg
  simp only [real_inner_smul_right, inner_add_right, ← Finset.mul_sum, Finset.sum_add_distrib]
  have h : ∑ i : ZMod N, ⟪w i, w (i - 1)⟫ = ∑ i : ZMod N, ⟪w i, w (i + 1)⟫ := by
    rw [← shift_sum (fun i => ⟪w i, w (i - 1)⟫) 1]
    simp only [add_sub_cancel_right]
    exact Finset.sum_congr rfl fun i _ => real_inner_comm _ _
  rw [h]
  ring

/-- Eigenvectors of a symmetric operator for different eigenvalues are orthogonal. -/
theorem pair_eq_zero_of_eigen {v v' : ZMod N → Ambient n} {l₁ l₂ : ℝ}
    (hv : avg v = l₁ • v) (hv' : avg v' = l₂ • v') (hne : l₁ ≠ l₂) : pair v v' = 0 := by
  have h := pair_avg v v'
  rw [hv, hv', pair_smul_left, pair_comm v (l₂ • v'), pair_smul_left, pair_comm v' v] at h
  have : (l₁ - l₂) * pair v v' = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

/-- The circulant form on a sum of eigenvectors with pairwise distinct eigenvalues. -/
theorem circForm_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (v : ι → ZMod N → Ambient n) (ev : ι → ℝ) (hv : ∀ j ∈ s, avg (v j) = ev j • v j)
    (hinj : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → ev j ≠ ev j') (c : ℝ) :
    circForm c (∑ j ∈ s, v j) = ∑ j ∈ s, (ev j - c) * pair (v j) (v j) := by
  rw [circForm_eq]
  have havg : avg (∑ j ∈ s, v j) = ∑ j ∈ s, ev j • v j := by
    funext i
    simp only [avg, Finset.sum_apply, Pi.smul_apply]
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := congrFun (hv j hj) i
    simp only [avg, Pi.smul_apply] at this
    exact this
  have horth : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → pair (v j) (v j') = 0 := fun j hj j' hj' h =>
    pair_eq_zero_of_eigen (hv j hj) (hv j' hj') (hinj j hj j' hj' h)
  have hdiag : ∀ (μ : ι → ℝ), pair (∑ j ∈ s, v j) (∑ j ∈ s, μ j • v j) =
      ∑ j ∈ s, μ j * pair (v j) (v j) := by
    intro μ
    rw [pair_sum_left]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [pair_comm, pair_sum_left]
    rw [Finset.sum_eq_single j]
    · rw [pair_smul_left]
    · intro j' hj' hne
      rw [pair_smul_left, horth j' hj' j hj hne, mul_zero]
    · intro h
      exact absurd hj h
  rw [havg, hdiag ev]
  have h1 : pair (∑ j ∈ s, v j) (∑ j ∈ s, v j) = ∑ j ∈ s, 1 * pair (v j) (v j) := by
    have := hdiag (fun _ => 1)
    simp only [one_smul] at this
    exact this
  rw [h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The squared norm of a sum of eigenvectors with distinct eigenvalues. -/
theorem pair_sum_self {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (v : ι → ZMod N → Ambient n) (ev : ι → ℝ) (hv : ∀ j ∈ s, avg (v j) = ev j • v j)
    (hinj : ∀ j ∈ s, ∀ j' ∈ s, j ≠ j' → ev j ≠ ev j') :
    pair (∑ j ∈ s, v j) (∑ j ∈ s, v j) = ∑ j ∈ s, pair (v j) (v j) := by
  have h0 := circForm_sum s v ev hv hinj 0
  have h1 := circForm_sum s v ev hv hinj 1
  rw [circForm_eq] at h0 h1
  have : ∑ j ∈ s, (ev j - 0) * pair (v j) (v j) - ∑ j ∈ s, (ev j - 1) * pair (v j) (v j) =
      ∑ j ∈ s, pair (v j) (v j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  linarith

/-! ### The modes -/

/-- The modes of frequency j are eigenvectors with eigenvalue cos(2πj/N). -/
theorem avg_regular (j : ℕ) (a b : Ambient n) :
    avg (regular N j a b) = Real.cos (2 * π * j / N) • regular N j a b := by
  funext i
  have h := regular_sub_add (N := N) j a b i
  change (1 / 2 : ℝ) • (regular N j a b (i + 1) + regular N j a b (i - 1)) =
    Real.cos (2 * π * j / N) • regular N j a b i
  rw [show regular N j a b (i + 1) + regular N j a b (i - 1) =
    regular N j a b (i - 1) + regular N j a b (i + 1) from add_comm _ _, h, smul_smul]
  congr 1
  ring

/-- The eigenvalues cos(2πj/N), 0 ≤ 2j ≤ N, are pairwise distinct. -/
theorem cos_ang_injective {j j' : ℕ} (hj : 2 * j ≤ N) (hj' : 2 * j' ≤ N)
    (h : Real.cos (2 * π * j / N) = Real.cos (2 * π * j' / N)) : j = j' := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hπ : 0 < π := Real.pi_pos
  have hmem : ∀ k : ℕ, 2 * k ≤ N → 2 * π * k / N ∈ Set.Icc 0 π := by
    intro k hk
    constructor
    · positivity
    · rw [div_le_iff₀ hN]
      have : (2 * k : ℝ) ≤ N := by exact_mod_cast hk
      nlinarith
  have := Real.injOn_cos (hmem j hj) (hmem j' hj') h
  have h2 : (j : ℝ) = j' := by
    field_simp at this
    nlinarith [Real.pi_pos]
  exact_mod_cast h2

end

end Finsler.RoundModes
