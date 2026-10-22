module

public import Finsler.Geometry.RoundHessian
public import Finsler.Geometry.RoundModes

/-! Nondegeneracy of the round polygon energy at the regular m-gons in the normal directions.

Let Q be the regular m-gon on the great circle of (x, u), c = cos(2πm/N), and let the normal
polygon w be a sum of modes regular N j a_j b_j with a_j, b_j orthogonal to x and u. The second
variation is 2 N G(c) S_c(w) with G(c) = −2θ/sin θ < 0, and S_c(w) = Σ_j (cos(2πj/N) − c)‖v_j‖²
with ‖w‖² = Σ_j ‖v_j‖² (`RoundModes`). Hence the second variation is negative definite on the
modes 0 ≤ j < m, with constant 2N|G(c)|(cos(2π(m−1)/N) − c), vanishes on j = m (the tangent
directions of the critical manifold that tilt the plane), and is positive definite on the modes
m < j ≤ N/2, with constant 2N|G(c)|(c − cos(2π(m+1)/N)). -/

@[expose] public section

namespace Finsler.RoundNondeg

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundEnergy Finsler.RoundPolygon
open Finsler.RoundHessian Finsler.RoundModes Finsler.PolygonSmooth
open Finsler.SphereRetraction Finsler.IndexComparison
open Finset Filter
open scoped RealInnerProductSpace Real Topology

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-- G(c) < 0 for −1 < c < 1. -/
theorem G_neg {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) : G c < 0 := by
  have ha : 0 < Real.arccos c := Real.arccos_pos.mpr hc1
  have hs : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  unfold G
  have : 0 < 2 * Real.arccos c / Real.sqrt (1 - c ^ 2) := by positivity
  linarith

theorem cos_ang_anti {j j' : ℕ} (hjj : j ≤ j') (hj' : 2 * j' ≤ N) :
    Real.cos (2 * π * j' / N) ≤ Real.cos (2 * π * j / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hπ : 0 < π := Real.pi_pos
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · rw [div_le_iff₀ hN]
    have : (2 * j' : ℝ) ≤ N := by exact_mod_cast hj'
    nlinarith
  · apply div_le_div_of_nonneg_right _ hN.le
    have : (j : ℝ) ≤ j' := by exact_mod_cast hjj
    nlinarith

theorem cos_ang_strict {j j' : ℕ} (hjj : j < j') (hj' : 2 * j' ≤ N) :
    Real.cos (2 * π * j' / N) < Real.cos (2 * π * j / N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hπ : 0 < π := Real.pi_pos
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · rw [div_le_iff₀ hN]
    have : (2 * j' : ℝ) ≤ N := by exact_mod_cast hj'
    nlinarith
  · apply div_lt_div_of_pos_right _ hN
    have : (j : ℝ) < j' := by exact_mod_cast hjj
    nlinarith

/-- −1 < cos(2πm/N) < 1 for 0 < 2m < N. -/
theorem cos_ang_bounds {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N) :
    -1 < Real.cos (2 * π * m / N) ∧ Real.cos (2 * π * m / N) < 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hπ : 0 < π := Real.pi_pos
  have hθ0 : 0 < 2 * π * m / N := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hθπ : 2 * π * m / N < π := by
    rw [div_lt_iff₀ hN]
    have : (2 * m : ℝ) < N := by exact_mod_cast hmN
    nlinarith
  constructor
  · have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
    rw [Real.cos_pi] at h
    exact h
  · have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
    rw [Real.cos_zero] at h
    exact h

omit [NeZero N] in
/-- A sum of modes with coefficients orthogonal to x and u is a normal polygon. -/
theorem modes_normal {x u : Ambient n} (s : Finset ℕ) (a b : ℕ → Ambient n)
    (ha : ∀ j, ⟪x, a j⟫ = 0 ∧ ⟪u, a j⟫ = 0) (hb : ∀ j, ⟪x, b j⟫ = 0 ∧ ⟪u, b j⟫ = 0)
    (i : ZMod N) :
    ⟪x, (∑ j ∈ s, regular N j (a j) (b j)) i⟫ = 0 ∧
      ⟪u, (∑ j ∈ s, regular N j (a j) (b j)) i⟫ = 0 := by
  simp only [Finset.sum_apply, inner_sum, regular, circ, inner_add_right, real_inner_smul_right]
  constructor
  · exact Finset.sum_eq_zero fun j _ => by rw [(ha j).1, (hb j).1]; ring
  · exact Finset.sum_eq_zero fun j _ => by rw [(ha j).2, (hb j).2]; ring

/-- The circulant form on a sum of modes of distinct frequencies 2j ≤ N. -/
theorem circForm_modes (s : Finset ℕ) (hs : ∀ j ∈ s, 2 * j ≤ N) (a b : ℕ → Ambient n)
    (c : ℝ) :
    circForm c (∑ j ∈ s, regular N j (a j) (b j)) =
      ∑ j ∈ s, (Real.cos (2 * π * j / N) - c) *
        pair (regular N j (a j) (b j)) (regular N j (a j) (b j)) :=
  circForm_sum s (fun j => regular N j (a j) (b j)) (fun j => Real.cos (2 * π * j / N))
    (fun j _ => avg_regular j (a j) (b j))
    (fun j hj j' hj' hne h => hne (cos_ang_injective (hs j hj) (hs j' hj') h)) c

theorem pair_modes (s : Finset ℕ) (hs : ∀ j ∈ s, 2 * j ≤ N) (a b : ℕ → Ambient n) :
    pair (∑ j ∈ s, regular N j (a j) (b j)) (∑ j ∈ s, regular N j (a j) (b j)) =
      ∑ j ∈ s, pair (regular N j (a j) (b j)) (regular N j (a j) (b j)) :=
  pair_sum_self s (fun j => regular N j (a j) (b j)) (fun j => Real.cos (2 * π * j / N))
    (fun j _ => avg_regular j (a j) (b j))
    (fun j hj j' hj' hne h => hne (cos_ang_injective (hs j hj) (hs j' hj') h))

section Regular

variable {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N) {x u : Ambient n} (hx : ‖x‖ = 1)
  (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
  (hC2 : ContDiffAt ℝ 2 (polyEnergyN (roundMetric n) N) (regular N m x u))
  (a b : ℕ → Ambient n) (ha : ∀ j, ⟪x, a j⟫ = 0 ∧ ⟪u, a j⟫ = 0)
  (hb : ∀ j, ⟪x, b j⟫ = 0 ∧ ⟪u, b j⟫ = 0)
include hm hmN hx hu hxu hC2 ha hb

theorem hessian_modes (s : Finset ℕ) (hs : ∀ j ∈ s, 2 * j ≤ N) :
    fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) (regular N m x u)
        (∑ j ∈ s, regular N j (a j) (b j)) (∑ j ∈ s, regular N j (a j) (b j)) =
      2 * N * G (Real.cos (2 * π * m / N)) * ∑ j ∈ s,
        (Real.cos (2 * π * j / N) - Real.cos (2 * π * m / N)) *
          pair (regular N j (a j) (b j)) (regular N j (a j) (b j)) := by
  rw [hessian_normal hm hmN hx hu hxu hC2 _ (fun i => (modes_normal s a b ha hb i).1)
    (fun i => (modes_normal s a b ha hb i).2)]
  have h := circForm_modes s hs a b (Real.cos (2 * π * m / N))
  unfold circForm at h
  rw [h]
  ring

/-- Negative definiteness on the low modes 0 ≤ j < m. -/
theorem hessian_low_le :
    fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) (regular N m x u)
        (∑ j ∈ range m, regular N j (a j) (b j)) (∑ j ∈ range m, regular N j (a j) (b j)) ≤
      2 * N * G (Real.cos (2 * π * m / N)) *
        (Real.cos (2 * π * (m - 1 : ℕ) / N) - Real.cos (2 * π * m / N)) *
          pair (∑ j ∈ range m, regular N j (a j) (b j)) (∑ j ∈ range m, regular N j (a j) (b j)) := by
  have hs : ∀ j ∈ range m, 2 * j ≤ N := fun j hj => by
    have := Finset.mem_range.mp hj
    omega
  rw [hessian_modes hm hmN hx hu hxu hC2 a b ha hb _ hs, pair_modes _ hs, Finset.mul_sum,
    Finset.mul_sum]
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hθ := cos_ang_bounds (N := N) hm hmN
  have hG : G (Real.cos (2 * π * m / N)) < 0 := G_neg hθ.1 hθ.2
  apply Finset.sum_le_sum
  intro j hj
  have hjm : j ≤ m - 1 := by
    have := Finset.mem_range.mp hj
    omega
  have hcj : Real.cos (2 * π * (m - 1 : ℕ) / N) ≤ Real.cos (2 * π * j / N) :=
    cos_ang_anti hjm (by omega)
  have hp := pair_self_nonneg (regular N j (a j) (b j))
  have hneg : 2 * N * G (Real.cos (2 * π * m / N)) ≤ 0 := by nlinarith
  have key := mul_nonpos_of_nonpos_of_nonneg hneg (mul_nonneg (sub_nonneg.mpr hcj) hp)
  linarith [key]

/-- Positive definiteness on the high modes m < j ≤ N/2. -/
theorem hessian_high_ge (s : Finset ℕ) (hs : ∀ j ∈ s, m < j ∧ 2 * j ≤ N) :
    2 * N * G (Real.cos (2 * π * m / N)) *
        (Real.cos (2 * π * (m + 1 : ℕ) / N) - Real.cos (2 * π * m / N)) *
          pair (∑ j ∈ s, regular N j (a j) (b j)) (∑ j ∈ s, regular N j (a j) (b j)) ≤
      fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) (regular N m x u)
        (∑ j ∈ s, regular N j (a j) (b j)) (∑ j ∈ s, regular N j (a j) (b j)) := by
  have hs' : ∀ j ∈ s, 2 * j ≤ N := fun j hj => (hs j hj).2
  rw [hessian_modes hm hmN hx hu hxu hC2 a b ha hb _ hs', pair_modes _ hs', Finset.mul_sum,
    Finset.mul_sum]
  have hθ1 := (cos_ang_bounds (N := N) hm hmN).2
  have hθ0 := (cos_ang_bounds (N := N) hm hmN).1
  have hG : G (Real.cos (2 * π * m / N)) < 0 := G_neg hθ0 hθ1
  apply Finset.sum_le_sum
  intro j hj
  have hcj : Real.cos (2 * π * j / N) ≤ Real.cos (2 * π * (m + 1 : ℕ) / N) :=
    cos_ang_anti (by have := (hs j hj).1; omega) (hs j hj).2
  have hp := pair_self_nonneg (regular N j (a j) (b j))
  have hneg : 2 * N * G (Real.cos (2 * π * m / N)) ≤ 0 := by
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
    nlinarith
  have key := mul_nonneg_of_nonpos_of_nonpos hneg
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcj) hp)
  linarith [key]

end Regular

/-! ### The reflection through the plane and the mixed terms -/

/-- The reflection through the plane of the orthonormal pair (x, u). -/
def refl (x u v : Ambient n) : Ambient n := (2 * ⟪x, v⟫) • x + (2 * ⟪u, v⟫) • u - v

section Refl

variable {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
include hx hu hxu

omit [NeZero N] in
theorem inner_refl (v w : Ambient n) : ⟪refl x u v, refl x u w⟫ = ⟪v, w⟫ := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪u, x⟫ = 0 := by rw [real_inner_comm, hxu]
  simp only [refl, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hxx, huu, hxu, hux, real_inner_comm x v,
    real_inner_comm u v]
  ring

omit [NeZero N] in
theorem norm_refl (v : Ambient n) : ‖refl x u v‖ = ‖v‖ := by
  have h := inner_refl hx hu hxu v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have h0 := norm_nonneg (refl x u v)
  have h1 := norm_nonneg v
  nlinarith [sq_nonneg (‖refl x u v‖ - ‖v‖), sq_nonneg (‖refl x u v‖ + ‖v‖)]

end Refl

omit [NeZero N] in
theorem refl_smul (x u : Ambient n) (r : ℝ) (v : Ambient n) :
    refl x u (r • v) = r • refl x u v := by
  simp only [refl, real_inner_smul_right, smul_sub, smul_add, smul_smul]
  congr 2 <;> ring_nf

omit [NeZero N] in
theorem refl_add (x u : Ambient n) (v w : Ambient n) :
    refl x u (v + w) = refl x u v + refl x u w := by
  simp only [refl, inner_add_right, mul_add, add_smul]
  abel

omit [NeZero N] in
theorem refl_sub (x u : Ambient n) (v w : Ambient n) :
    refl x u (v - w) = refl x u v - refl x u w := by
  simp only [refl, inner_sub_right, mul_sub, sub_smul]
  abel

omit [NeZero N] in
theorem refl_plane {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    (α β : ℝ) : refl x u (α • x + β • u) = α • x + β • u := by
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪u, x⟫ = 0 := by rw [real_inner_comm, hxu]
  simp only [refl, inner_add_right, real_inner_smul_right, hxx, huu, hxu, hux]
  module

omit [NeZero N] in
theorem refl_normal (x u : Ambient n) {v : Ambient n} (h1 : ⟪x, v⟫ = 0) (h2 : ⟪u, v⟫ = 0) :
    refl x u v = -v := by
  simp [refl, h1, h2]

omit [NeZero N] in
theorem normalize_refl {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    {v : Ambient n} (hv : v ≠ 0) :
    ((normalize (refl x u v) : Sphere n) : Ambient n) =
      refl x u ((normalize v : Sphere n) : Ambient n) := by
  have hr : refl x u v ≠ 0 := by
    intro h
    have := norm_refl hx hu hxu v
    rw [h, norm_zero] at this
    exact hv (norm_eq_zero.mp this.symm)
  rw [Finsler.AmbientPenalty.coe_normalize hr, Finsler.AmbientPenalty.coe_normalize hv,
    norm_refl hx hu hxu, refl_smul]

/-- The round polygon energy is invariant under the reflection through the plane. -/
theorem polyEnergyN_refl {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    (P : ZMod N → Ambient n) (hP : ∀ i, P i ≠ 0)
    (hna : ∀ i : ZMod N, ⟪((normalize (P i) : Sphere n) : Ambient n),
      (normalize (P (i + 1)) : Ambient n)⟫ ≠ -1) :
    polyEnergyN (roundMetric n) N (fun i => refl x u (P i)) =
      polyEnergyN (roundMetric n) N P := by
  have heq : ∀ i : ZMod N, ⟪((normalize (refl x u (P i)) : Sphere n) : Ambient n),
      (normalize (refl x u (P (i + 1))) : Ambient n)⟫ =
      ⟪((normalize (P i) : Sphere n) : Ambient n), (normalize (P (i + 1)) : Ambient n)⟫ := by
    intro i
    rw [normalize_refl hx hu hxu (hP i), normalize_refl hx hu hxu (hP (i + 1)),
      inner_refl hx hu hxu]
  rw [polyEnergyN_round _ (fun i => by rw [heq]; exact hna i), polyEnergyN_round _ hna]
  simp only [heq]

/-- The second variation has no mixed in-plane/normal terms. -/
theorem hessian_mixed {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N) {x u : Ambient n}
    (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    (hC2 : ContDiffAt ℝ 2 (polyEnergyN (roundMetric n) N) (regular N m x u))
    (a b : ZMod N → Ambient n) (ha : ∀ i, a i = ⟪x, a i⟫ • x + ⟪u, a i⟫ • u)
    (hb : ∀ i, ⟪x, b i⟫ = 0 ∧ ⟪u, b i⟫ = 0) :
    fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) (regular N m x u) a b = 0 := by
  set Q := regular N m x u with hQdef
  have hQ : ∀ i, ‖Q i‖ = 1 := norm_regular hx hu hxu
  have hcθ := cos_ang_bounds (N := N) hm hmN
  have hinner : ∀ i, ⟪Q i, Q (i + 1)⟫ = Real.cos (2 * π * m / N) := inner_regular hx hu hxu
  -- near t = 0 the lines have nonzero vertices and non-antipodal normalized edges
  have hgood : ∀ v : ZMod N → Ambient n, ∀ᶠ t in 𝓝 (0 : ℝ), (∀ i, Q i + t • v i ≠ 0) ∧
      ∀ i : ZMod N, ⟪((normalize (Q i + t • v i) : Sphere n) : Ambient n),
        (normalize (Q (i + 1) + t • v (i + 1)) : Ambient n)⟫ ≠ -1 := by
    intro v
    have hd : ∀ i, HasDerivAt (fun t : ℝ => ((normalize (Q i + t • v i) : Sphere n) : Ambient n))
        (v i - ⟪Q i, v i⟫ • Q i) 0 := fun i => hasDerivAt_normalize_line (hQ i)
    have h1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, Q i + t • v i ≠ 0 := by
      rw [eventually_all]
      intro i
      have hc : ContinuousAt (fun t : ℝ => Q i + t • v i) 0 :=
        (hasDerivAt_line (Q i) (v i)).continuousAt
      have h0 : (fun t : ℝ => Q i + t • v i) 0 ≠ 0 := by
        simp only [zero_smul, add_zero]
        intro h
        have := hQ i
        rw [h, norm_zero] at this
        exact zero_ne_one this
      exact hc.eventually_ne h0
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : ZMod N, ⟪((normalize (Q i + t • v i) : Sphere n) :
        Ambient n), (normalize (Q (i + 1) + t • v (i + 1)) : Ambient n)⟫ ≠ -1 := by
      rw [eventually_all]
      intro i
      have hc : ContinuousAt (fun t : ℝ => ⟪((normalize (Q i + t • v i) : Sphere n) : Ambient n),
          (normalize (Q (i + 1) + t • v (i + 1)) : Ambient n)⟫) 0 :=
        (hd i).continuousAt.inner (hd (i + 1)).continuousAt
      have h0 : (fun t : ℝ => ⟪((normalize (Q i + t • v i) : Sphere n) : Ambient n),
          (normalize (Q (i + 1) + t • v (i + 1)) : Ambient n)⟫) 0 ≠ -1 := by
        simp only [zero_smul, add_zero]
        rw [coe_normalize_of_norm (hQ i), coe_normalize_of_norm (hQ (i + 1)), hinner]
        exact ne_of_gt hcθ.1
      exact hc.eventually_ne h0
    exact h1.and h2
  -- the reflection exchanges the lines through a + b and a − b
  have hQrefl : ∀ i, refl x u (Q i) = Q i := by
    intro i
    rw [hQdef, regular, circ]
    exact refl_plane hx hu hxu _ _
  have hline : ∀ᶠ t in 𝓝 (0 : ℝ), polyEnergyN (roundMetric n) N (Q + t • (a + b)) =
      polyEnergyN (roundMetric n) N (Q + t • (a - b)) := by
    filter_upwards [hgood (a + b)] with t ht
    have hr : (fun i => refl x u ((Q + t • (a + b)) i)) = Q + t • (a - b) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
      rw [refl_add, refl_smul, refl_add, hQrefl, refl_normal x u (hb i).1 (hb i).2]
      conv_lhs => rw [ha i]
      rw [refl_plane hx hu hxu, ← ha i]
      module
    have h := polyEnergyN_refl hx hu hxu (Q + t • (a + b)) (fun i => ht.1 i) (fun i => ht.2 i)
    rw [hr] at h
    exact h.symm
  have hcrit := fderiv_regular_eq_zero hm hmN hx hu hxu (hC2.differentiableAt (by norm_num))
  have T1 := tendsto_div_sq hC2 hcrit (hasDerivAt_line Q (a + b)) (by simp)
  have T2 := tendsto_div_sq hC2 hcrit (hasDerivAt_line Q (a - b)) (by simp)
  have hT : Tendsto (fun t : ℝ => (polyEnergyN (roundMetric n) N (Q + t • (a - b)) -
      polyEnergyN (roundMetric n) N Q) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (1 / 2 * fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) Q (a + b) (a + b))) := by
    refine T1.congr' ?_
    filter_upwards [hline.filter_mono nhdsWithin_le_nhds] with t ht
    rw [ht]
  have heq := tendsto_nhds_unique T2 hT
  have hsymm := (hC2.isSymmSndFDerivAt (by simp)) a b
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
    at heq
  linarith

end

end Finsler.RoundNondeg
