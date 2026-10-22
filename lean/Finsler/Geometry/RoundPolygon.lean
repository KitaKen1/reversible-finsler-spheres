module

public import Finsler.Geometry.RoundEnergy
public import Finsler.Geometry.PolygonCritical
public import Finsler.Geometry.PolygonIterate

/-! The critical polygons of the round metric. For polygons with non-antipodal edges the round
polygon energy is N Σ arccos(⟪q_i, q_{i+1}⟫)². Along a curve of sphere polygons its derivative is
N Σ G(c_i)(⟪q_i', q_{i+1}⟫ + ⟪q_i, q_{i+1}'⟫) with c_i = ⟪q_i, q_{i+1}⟫ and
G(c) = −2 arccos c / √(1 − c²); at a zero edge G(1) = 0 and the edge term is O(r²), since
arccos⟪x, y⟫² ≤ (π²/4)‖x − y‖² for unit vectors (Jordan's inequality), so the formula holds
without case distinction.

Moving one vertex q_j along a great circle in a tangent direction ξ gives the vertex condition
G(c_{j−1})⟪q_{j−1}, ξ⟫ + G(c_j)⟪ξ, q_{j+1}⟫ = 0. Taking ξ the tangential part of
G(c_{j−1}) q_{j−1} + G(c_j) q_{j+1} shows that this part vanishes; its two terms have norms
2 arccos c_{j−1} and 2 arccos c_j, so all edges have the same angle θ (zero edges propagate), and
for θ > 0 the vertices satisfy q_{j−1} + q_{j+1} = 2 cos θ · q_j. Solving the recurrence,
q_k = cos(kθ) q_0 + sin(kθ) u, and closing gives θ = 2πm/N with 0 < 2m < N: the critical polygons
of positive energy are the regular m-gons on great circles. Conversely regular m-gons are
critical, because the derivative regroups into N G(cos θ) Σ ⟪q_i', q_{i−1} + q_{i+1}⟫ and
q_{i−1} + q_{i+1} = 2 cos θ · q_i is orthogonal to the tangent vector q_i'. -/

@[expose] public section

namespace Finsler.RoundPolygon

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundEnergy Finsler.PolygonCritical
open Finsler.PolygonIterate
open Finsler.SphereDistance (minEnergy)
open Set Filter Asymptotics
open scoped Topology RealInnerProductSpace Real

noncomputable section

variable {n : ℕ}

/-! ### The edge function -/

/-- The edge energy as a function of the inner product. -/
def ang2 (c : ℝ) : ℝ := Real.arccos c ^ 2

/-- The derivative coefficient G(c) = −2 arccos c / √(1 − c²). -/
def G (c : ℝ) : ℝ := -(2 * Real.arccos c / Real.sqrt (1 - c ^ 2))

theorem G_one : G 1 = 0 := by
  simp [G]

theorem ang2_hasDerivAt {c : ℝ} (h1 : c ≠ -1) (h2 : c ≠ 1) : HasDerivAt ang2 (G c) c := by
  have h := (Real.hasDerivAt_arccos h1 h2).pow 2
  have h' : HasDerivAt (fun x => Real.arccos x ^ 2) (G c) c := by
    convert h using 1
    simp only [G]
    push_cast
    ring
  exact h'

/-- Jordan's inequality in the form arccos⟪x, y⟫² ≤ (π²/4)‖x − y‖². -/
theorem ang2_le {x y : Ambient n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ang2 ⟪x, y⟫ ≤ π ^ 2 / 4 * ‖x - y‖ ^ 2 := by
  set c := ⟪x, y⟫ with hc
  have hc1 : c ≤ 1 := inner_le_one hx hy
  have hc0 : -1 ≤ c := neg_one_le_inner hx hy
  set θ := Real.arccos c with hθ
  have hθ0 : 0 ≤ θ := Real.arccos_nonneg c
  have hθπ : θ ≤ π := Real.arccos_le_pi c
  have hcos : Real.cos θ = c := Real.cos_arccos hc0 hc1
  have hnorm : ‖x - y‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq_real, hx, hy, ← hc]
    ring
  have hhalf : 1 - Real.cos θ = 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (θ / 2)
    have h3 := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    nlinarith
  have hjordan : 2 / π * (θ / 2) ≤ Real.sin (θ / 2) :=
    Real.mul_le_sin (by linarith) (by linarith)
  have hπ : 0 < π := Real.pi_pos
  have hθs : θ ≤ π * Real.sin (θ / 2) := by
    have : 2 / π * (θ / 2) = θ / π := by field_simp
    rw [this, div_le_iff₀ hπ] at hjordan
    linarith
  have hsq : θ ^ 2 ≤ π ^ 2 * Real.sin (θ / 2) ^ 2 := by
    have := pow_le_pow_left₀ hθ0 hθs 2
    nlinarith
  rw [ang2, ← hθ, hnorm]
  nlinarith

/-- The absolute value of the derivative coefficient times the sine is twice the angle. -/
theorem abs_G_mul_sqrt {c : ℝ} (hc0 : -1 < c) (hc1 : c ≤ 1) :
    |G c| * Real.sqrt (1 - c ^ 2) = 2 * Real.arccos c := by
  rcases eq_or_lt_of_le hc1 with h | h
  · subst h
    simp [G_one, Real.arccos_one]
  · have hs : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
    have ha : 0 ≤ Real.arccos c := Real.arccos_nonneg c
    rw [G, abs_neg, abs_div, abs_of_nonneg (by positivity), abs_of_pos hs, div_mul_cancel₀ _ hs.ne']

/-! ### The derivative of an edge term -/

/-- The derivative of an edge term along curves of unit vectors, including zero edges. -/
theorem edge_hasDerivAt {x y : ℝ → Ambient n} {x' y' : Ambient n}
    (hx : HasDerivAt x x' 0) (hy : HasDerivAt y y' 0) (hxn : ∀ r, ‖x r‖ = 1)
    (hyn : ∀ r, ‖y r‖ = 1) (hna : ⟪x 0, y 0⟫ ≠ -1) :
    HasDerivAt (fun r => ang2 ⟪x r, y r⟫) (G ⟪x 0, y 0⟫ * (⟪x 0, y'⟫ + ⟪x', y 0⟫)) 0 := by
  have hc1 : ⟪x 0, y 0⟫ ≤ 1 := inner_le_one (hxn 0) (hyn 0)
  rcases eq_or_lt_of_le hc1 with h1 | h1
  · -- a zero edge: the term is O(r²)
    have hxy : y 0 = x 0 := eq_of_inner_eq_one (hxn 0) (hyn 0) h1
    rw [h1, G_one, zero_mul]
    have hxO : (fun h => x h - x 0) =O[𝓝 0] fun h => h := by
      simpa using hx.isBigO_sub
    have hyO : (fun h => y h - y 0) =O[𝓝 0] fun h => h := by
      simpa using hy.isBigO_sub
    have hdO : (fun h => x h - y h) =O[𝓝 0] fun h => h := by
      have := hxO.sub hyO
      refine this.congr_left fun h => ?_
      rw [hxy]
      abel
    have hnO : (fun h => ‖x h - y h‖ ^ 2) =O[𝓝 0] fun h => h ^ 2 :=
      (hdO.norm_left).pow 2
    have hfO : (fun h => ang2 ⟪x h, y h⟫) =O[𝓝 0] fun h => ‖x h - y h‖ ^ 2 := by
      refine IsBigO.of_bound (π ^ 2 / 4) (Eventually.of_forall fun h => ?_)
      have h0 : 0 ≤ ang2 ⟪x h, y h⟫ := sq_nonneg _
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, abs_of_nonneg (sq_nonneg _)]
      exact ang2_le (hxn h) (hyn h)
    have hfo : (fun h => ang2 ⟪x h, y h⟫) =o[𝓝 0] fun h => h :=
      (hfO.trans hnO).trans_isLittleO (isLittleO_pow_id (by norm_num))
    have hf0 : ang2 ⟪x 0, y 0⟫ = 0 := by
      rw [h1, ang2, Real.arccos_one]
      norm_num
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    refine hfo.congr_left fun h => ?_
    rw [zero_add, hf0, smul_zero, sub_zero, sub_zero]
  · have hne : ⟪x 0, y 0⟫ ≠ 1 := ne_of_lt h1
    have hinner := HasDerivAt.inner ℝ hx hy
    exact (ang2_hasDerivAt hna hne).comp 0 hinner

/-! ### The round polygon energy -/

/-- On polygons with non-antipodal edges the round polygon energy is N Σ arccos². -/
theorem polyEnergy_round {N : ℕ} [NeZero N] {Q : ZMod N → Ambient n} (hQ : ∀ i, ‖Q i‖ = 1)
    (hna : ∀ i : ZMod N, ⟪Q i, Q (i + 1)⟫ ≠ -1) :
    polyEnergy (roundMetric n) N Q = N * ∑ i : ZMod N, ang2 ⟪Q i, Q (i + 1)⟫ := by
  unfold polyEnergy
  rw [sum_univ_eq_sum_range (fun i : ZMod N => ang2 ⟪Q i, Q (i + 1)⟫)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  exact minEnergy_round (hQ _) (hQ _) (hna _)

/-- The derivative of the round polygon energy along a curve of sphere polygons. -/
theorem polyEnergy_hasDerivAt {N : ℕ} [NeZero N] {c : ℝ → ZMod N → Ambient n}
    {c' : ZMod N → Ambient n} (hcn : ∀ r i, ‖c r i‖ = 1) (hcd : HasDerivAt c c' 0)
    (hna : ∀ i : ZMod N, ⟪c 0 i, c 0 (i + 1)⟫ ≠ -1) :
    HasDerivAt (fun r => polyEnergy (roundMetric n) N (c r))
      (N * ∑ i : ZMod N, G ⟪c 0 i, c 0 (i + 1)⟫ * (⟪c 0 i, c' (i + 1)⟫ + ⟪c' i, c 0 (i + 1)⟫))
      0 := by
  have hci : ∀ i, HasDerivAt (fun r => c r i) (c' i) 0 := fun i => hasDerivAt_pi.mp hcd i
  -- near 0 the edges stay non-antipodal
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ i : ZMod N, ⟪c r i, c r (i + 1)⟫ ≠ -1 := by
    rw [eventually_all]
    intro i
    have hcont : ContinuousAt (fun r => ⟪c r i, c r (i + 1)⟫) 0 :=
      (hci i).continuousAt.inner (hci (i + 1)).continuousAt
    exact hcont.eventually_ne (hna i)
  have hsum : HasDerivAt (fun r => (N : ℝ) * ∑ i : ZMod N, ang2 ⟪c r i, c r (i + 1)⟫)
      (N * ∑ i : ZMod N, G ⟪c 0 i, c 0 (i + 1)⟫ * (⟪c 0 i, c' (i + 1)⟫ + ⟪c' i, c 0 (i + 1)⟫))
      0 := by
    apply HasDerivAt.const_mul
    have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      edge_hasDerivAt (hci i) (hci (i + 1)) (fun r => hcn r i) (fun r => hcn r (i + 1)) (hna i))
    exact h
  refine hsum.congr_of_eventuallyEq ?_
  filter_upwards [hev] with r hr
  exact polyEnergy_round (hcn r) hr

/-! ### Moving one vertex -/

theorem norm_cos_sin {p u : Ambient n} (hp : ‖p‖ = 1) (hu : ‖u‖ = 1) (hpu : ⟪p, u⟫ = 0)
    (r : ℝ) : ‖Real.cos r • p + Real.sin r • u‖ = 1 := by
  have h := norm_sq_comb hp hu hpu (Real.cos r) (Real.sin r)
  rw [Real.cos_sq_add_sin_sq] at h
  have h0 := norm_nonneg (Real.cos r • p + Real.sin r • u)
  nlinarith [sq_nonneg (‖Real.cos r • p + Real.sin r • u‖ - 1)]

/-- Moving the vertex j along the great circle through q_j in the direction ξ. -/
def moveVertex {N : ℕ} (Q : ZMod N → Ambient n) (j : ZMod N) (ξ : Ambient n) (r : ℝ) :
    ZMod N → Ambient n :=
  Function.update Q j (Real.cos r • Q j + Real.sin r • ξ)

theorem moveVertex_zero {N : ℕ} (Q : ZMod N → Ambient n) (j : ZMod N) (ξ : Ambient n) :
    moveVertex Q j ξ 0 = Q := by
  unfold moveVertex
  rw [Real.cos_zero, Real.sin_zero, one_smul, zero_smul, add_zero, Function.update_eq_self]

theorem moveVertex_norm {N : ℕ} {Q : ZMod N → Ambient n} (hQ : ∀ i, ‖Q i‖ = 1) {j : ZMod N}
    {ξ : Ambient n} (hξ1 : ‖ξ‖ = 1) (hξ : ⟪Q j, ξ⟫ = 0) (r : ℝ) (i : ZMod N) :
    ‖moveVertex Q j ξ r i‖ = 1 := by
  unfold moveVertex
  rcases eq_or_ne i j with h | h
  · subst h
    rw [Function.update_self]
    exact norm_cos_sin (hQ i) hξ1 hξ r
  · rw [Function.update_of_ne h]
    exact hQ i

theorem moveVertex_hasDerivAt {N : ℕ} (Q : ZMod N → Ambient n) (j : ZMod N) (ξ : Ambient n) :
    HasDerivAt (moveVertex Q j ξ) (Pi.single j ξ) 0 := by
  rw [hasDerivAt_pi]
  intro i
  unfold moveVertex
  rcases eq_or_ne i j with h | h
  · subst h
    simp only [Function.update_self, Pi.single_eq_same]
    have hc := (Real.hasDerivAt_cos 0).smul_const (Q i)
    have hs := (Real.hasDerivAt_sin 0).smul_const ξ
    have h2 := hc.add hs
    convert h2 using 1
    simp
  · simp only [Function.update_of_ne h, Pi.single_eq_of_ne h]
    exact hasDerivAt_const 0 (Q i)

/-! ### The vertex condition -/

/-- The first variation at a vertex of a critical round polygon. -/
theorem vertex_condition {N : ℕ} [NeZero N] {q : ZMod N → Sphere n}
    (hna : ∀ i : ZMod N, ⟪(q i : Ambient n), q (i + 1)⟫ ≠ -1)
    (hc : PolyCritical (roundMetric n) N q) (j : ZMod N) {ξ : Ambient n} (hξ1 : ‖ξ‖ = 1)
    (hξ : ⟪(q j : Ambient n), ξ⟫ = 0) :
    G ⟪(q (j - 1) : Ambient n), q j⟫ * ⟪(q (j - 1) : Ambient n), ξ⟫ +
      G ⟪(q j : Ambient n), q (j + 1)⟫ * ⟪ξ, (q (j + 1) : Ambient n)⟫ = 0 := by
  set Q : ZMod N → Ambient n := fun i => (q i : Ambient n) with hQdef
  have hQ : ∀ i, ‖Q i‖ = 1 := fun i => by
    simp [hQdef]
  have hcrit := hc (moveVertex Q j ξ) (Pi.single j ξ) (moveVertex_zero Q j ξ)
    (moveVertex_norm hQ hξ1 hξ) (moveVertex_hasDerivAt Q j ξ)
  have hna' : ∀ i : ZMod N, ⟪moveVertex Q j ξ 0 i, moveVertex Q j ξ 0 (i + 1)⟫ ≠ -1 := by
    rw [moveVertex_zero]
    exact hna
  have hder := polyEnergy_hasDerivAt (moveVertex_norm hQ hξ1 hξ) (moveVertex_hasDerivAt Q j ξ)
    hna'
  have heq := hder.unique hcrit
  rw [moveVertex_zero] at heq
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hsum := (mul_eq_zero.mp heq).resolve_left hN
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  have h1 : ∑ i : ZMod N, G ⟪Q i, Q (i + 1)⟫ * ⟪Q i, (Pi.single j ξ : ZMod N → Ambient n) (i + 1)⟫ =
      G ⟪Q (j - 1), Q j⟫ * ⟪Q (j - 1), ξ⟫ := by
    rw [Finset.sum_eq_single (j - 1)]
    · rw [sub_add_cancel, Pi.single_eq_same]
    · intro i _ hi
      have hi' : i + 1 ≠ j := by
        intro h
        apply hi
        rw [← h, add_sub_cancel_right]
      rw [Pi.single_eq_of_ne hi', inner_zero_right, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h2 : ∑ i : ZMod N, G ⟪Q i, Q (i + 1)⟫ * ⟪(Pi.single j ξ : ZMod N → Ambient n) i, Q (i + 1)⟫ =
      G ⟪Q j, Q (j + 1)⟫ * ⟪ξ, Q (j + 1)⟫ := by
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, inner_zero_left, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h1, h2] at hsum
  exact hsum

/-- The vertex condition for all tangent vectors. -/
theorem vertex_condition_all {N : ℕ} [NeZero N] {q : ZMod N → Sphere n}
    (hna : ∀ i : ZMod N, ⟪(q i : Ambient n), q (i + 1)⟫ ≠ -1)
    (hc : PolyCritical (roundMetric n) N q) (j : ZMod N) (ξ : Ambient n)
    (hξ : ⟪(q j : Ambient n), ξ⟫ = 0) :
    G ⟪(q (j - 1) : Ambient n), q j⟫ * ⟪(q (j - 1) : Ambient n), ξ⟫ +
      G ⟪(q j : Ambient n), q (j + 1)⟫ * ⟪ξ, (q (j + 1) : Ambient n)⟫ = 0 := by
  rcases eq_or_ne ξ 0 with h0 | h0
  · subst h0
    simp
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr h0
    set η := ‖ξ‖⁻¹ • ξ with hη
    have hη1 : ‖η‖ = 1 := by
      rw [hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hηt : ⟪(q j : Ambient n), η⟫ = 0 := by
      rw [hη, real_inner_smul_right, hξ, mul_zero]
    have h := vertex_condition hna hc j hη1 hηt
    have hξη : ξ = ‖ξ‖ • η := by
      rw [hη, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    rw [hξη, real_inner_smul_right, real_inner_smul_left]
    have : ‖ξ‖ * (G ⟪(q (j - 1) : Ambient n), q j⟫ * ⟪(q (j - 1) : Ambient n), η⟫ +
        G ⟪(q j : Ambient n), q (j + 1)⟫ * ⟪η, (q (j + 1) : Ambient n)⟫) = 0 := by
      rw [h, mul_zero]
    linarith

/-! ### Geometry of the vertex condition -/

theorem norm_sub_inner_smul {a x : Ambient n} (ha : ‖a‖ = 1) (hx : ‖x‖ = 1) :
    ‖a - ⟪a, x⟫ • x‖ = Real.sqrt (1 - ⟪a, x⟫ ^ 2) := by
  have h2 : ‖a - ⟪a, x⟫ • x‖ ^ 2 = 1 - ⟪a, x⟫ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, ha, hx, Real.norm_eq_abs, mul_pow,
      sq_abs]
    ring
  rw [← h2, Real.sqrt_sq (norm_nonneg _)]

theorem G_ne_zero {c : ℝ} (hc0 : -1 < c) (hc1 : c < 1) : G c ≠ 0 := by
  have ha : 0 < Real.arccos c := Real.arccos_pos.mpr hc1
  have hs : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  unfold G
  have : 0 < 2 * Real.arccos c / Real.sqrt (1 - c ^ 2) := by positivity
  linarith

/-- The vertex condition forces equal angles at both edges, and for a positive angle the
recurrence a + b = 2 cos θ · x. -/
theorem angles_of_vertex {x a b : Ambient n} (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha' : ⟪a, x⟫ ≠ -1) (hb' : ⟪x, b⟫ ≠ -1)
    (hcond : ∀ ξ : Ambient n, ⟪x, ξ⟫ = 0 → G ⟪a, x⟫ * ⟪a, ξ⟫ + G ⟪x, b⟫ * ⟪ξ, b⟫ = 0) :
    ⟪a, x⟫ = ⟪x, b⟫ ∧ (⟪x, b⟫ < 1 → a + b = (2 * ⟪x, b⟫) • x) := by
  set c₁ := ⟪a, x⟫ with hc₁
  set c₂ := ⟪x, b⟫ with hc₂
  have hbx : ⟪b, x⟫ = c₂ := by rw [real_inner_comm]
  set A := a - c₁ • x with hA
  set B := b - c₂ • x with hB
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have hxA : ⟪x, A⟫ = 0 := by
    rw [hA, inner_sub_right, real_inner_smul_right, hxx, real_inner_comm, ← hc₁]
    ring
  have hxB : ⟪x, B⟫ = 0 := by
    rw [hB, inner_sub_right, real_inner_smul_right, hxx, ← hc₂]
    ring
  set V := G c₁ • A + G c₂ • B with hV
  have hxV : ⟪x, V⟫ = 0 := by
    rw [hV, inner_add_right, real_inner_smul_right, real_inner_smul_right, hxA, hxB]
    ring
  have h := hcond V hxV
  have haV : ⟪a, V⟫ = ⟪A, V⟫ := by
    rw [hA, inner_sub_left, real_inner_smul_left, hxV]
    ring
  have hVb : ⟪V, b⟫ = ⟪B, V⟫ := by
    rw [hB, inner_sub_left, real_inner_smul_left, hxV, real_inner_comm V b]
    ring
  rw [haV, hVb] at h
  have hVV : ⟪V, V⟫ = 0 := by
    have : ⟪V, V⟫ = G c₁ * ⟪A, V⟫ + G c₂ * ⟪B, V⟫ := by
      rw [hV, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [this, h]
  have hV0 : V = 0 := inner_self_eq_zero.mp hVV
  -- norms of the two terms
  have hnA : ‖A‖ = Real.sqrt (1 - c₁ ^ 2) := norm_sub_inner_smul ha hx
  have hnB : ‖B‖ = Real.sqrt (1 - c₂ ^ 2) := by
    rw [hB, ← hbx]
    exact norm_sub_inner_smul hb hx
  have hc₁0 : -1 < c₁ := lt_of_le_of_ne (by
    have := neg_one_le_inner ha hx
    exact this) (Ne.symm ha')
  have hc₁1 : c₁ ≤ 1 := inner_le_one ha hx
  have hc₂0 : -1 < c₂ := lt_of_le_of_ne (neg_one_le_inner hx hb) (Ne.symm hb')
  have hc₂1 : c₂ ≤ 1 := inner_le_one hx hb
  have hAB : G c₁ • A = -(G c₂ • B) := by
    rw [← sub_eq_zero, sub_neg_eq_add, ← hV, hV0]
  have hnorm : |G c₁| * Real.sqrt (1 - c₁ ^ 2) = |G c₂| * Real.sqrt (1 - c₂ ^ 2) := by
    have := congrArg norm hAB
    rw [norm_neg, norm_smul, norm_smul, hnA, hnB, Real.norm_eq_abs, Real.norm_eq_abs] at this
    exact this
  rw [abs_G_mul_sqrt hc₁0 hc₁1, abs_G_mul_sqrt hc₂0 hc₂1] at hnorm
  have harc : Real.arccos c₁ = Real.arccos c₂ := by linarith
  have heq : c₁ = c₂ := Real.arccos_injOn ⟨hc₁0.le, hc₁1⟩ ⟨hc₂0.le, hc₂1⟩ harc
  refine ⟨heq, fun hlt => ?_⟩
  have hG : G c₂ ≠ 0 := G_ne_zero hc₂0 hlt
  have hsum : G c₂ • (A + B) = 0 := by
    have h' : G c₁ • A + G c₂ • B = 0 := by
      rw [← hV]
      exact hV0
    rw [heq] at h'
    rw [smul_add]
    exact h'
  have hAB0 : A + B = 0 := (smul_eq_zero.mp hsum).resolve_left hG
  rw [hA, hB, heq] at hAB0
  have : a + b = c₂ • x + c₂ • x := by
    have h' := hAB0
    rw [show a - c₂ • x + (b - c₂ • x) = (a + b) - (c₂ • x + c₂ • x) by abel] at h'
    exact sub_eq_zero.mp h'
  rw [this, ← add_smul]
  congr 1
  ring

/-! ### Classification of the critical polygons -/

theorem cos_step (t θ : ℝ) : Real.cos (t + 2 * θ) = 2 * Real.cos θ * Real.cos (t + θ) - Real.cos t := by
  have h1 : Real.cos (t + 2 * θ) = Real.cos ((t + θ) + θ) := by ring_nf
  have h2 : Real.cos t = Real.cos ((t + θ) - θ) := by ring_nf
  rw [h1, h2, Real.cos_add, Real.cos_sub]
  ring

theorem sin_step (t θ : ℝ) : Real.sin (t + 2 * θ) = 2 * Real.cos θ * Real.sin (t + θ) - Real.sin t := by
  have h1 : Real.sin (t + 2 * θ) = Real.sin ((t + θ) + θ) := by ring_nf
  have h2 : Real.sin t = Real.sin ((t + θ) - θ) := by ring_nf
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

/-- The coefficients of a combination of an orthonormal pair. -/
theorem coeff_eq_of_comb {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    {a b : ℝ} (h : a • x + b • u = x) : a = 1 ∧ b = 0 := by
  have h1 := congrArg (fun v => ⟪v, x⟫) h
  have h2 := congrArg (fun v => ⟪v, u⟫) h
  have hxx : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hx, one_pow]
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  have hux : ⟪u, x⟫ = 0 := by rw [real_inner_comm, hxu]
  simp only [inner_add_left, real_inner_smul_left, hxx, huu, hxu, hux] at h1 h2
  constructor <;> linarith

/-- The critical polygons of positive energy of the round metric are the regular m-gons on great
circles, 0 < 2m < N. -/
theorem regular_of_polyCritical {N : ℕ} [NeZero N] {q : ZMod N → Sphere n}
    (hna : ∀ i : ZMod N, ⟪(q i : Ambient n), q (i + 1)⟫ ≠ -1)
    (hc : PolyCritical (roundMetric n) N q)
    (hpos : 0 < polyEnergy (roundMetric n) N (fun i => (q i : Ambient n))) :
    ∃ (x u : Ambient n) (m : ℕ), ‖x‖ = 1 ∧ ‖u‖ = 1 ∧ ⟪x, u⟫ = 0 ∧ 0 < m ∧ 2 * m < N ∧
      ∀ k : ℕ, (q (k : ZMod N) : Ambient n) =
        Real.cos (2 * π * m / N * k) • x + Real.sin (2 * π * m / N * k) • u := by
  set Q : ZMod N → Ambient n := fun i => (q i : Ambient n) with hQdef
  have hQ : ∀ i, ‖Q i‖ = 1 := fun i => by simp [hQdef]
  -- equal angles and the recurrence at every vertex
  have hvert : ∀ j : ZMod N, ⟪Q (j - 1), Q j⟫ = ⟪Q j, Q (j + 1)⟫ ∧
      (⟪Q j, Q (j + 1)⟫ < 1 → Q (j - 1) + Q (j + 1) = (2 * ⟪Q j, Q (j + 1)⟫) • Q j) := by
    intro j
    have hna1 : ⟪Q (j - 1), Q j⟫ ≠ -1 := by
      have := hna (j - 1)
      rwa [sub_add_cancel] at this
    exact angles_of_vertex (hQ j) (hQ (j - 1)) (hQ (j + 1)) hna1 (hna j)
      (fun ξ hξ => vertex_condition_all hna hc j ξ hξ)
  set c := ⟪Q 0, Q 1⟫ with hcdef
  -- all edges have the same inner product
  have hall : ∀ k : ℕ, ⟪Q (k : ZMod N), Q ((k : ZMod N) + 1)⟫ = c := by
    intro k
    induction k with
    | zero => simp [hcdef]
    | succ k ih =>
      have h := (hvert ((k : ZMod N) + 1)).1
      rw [add_sub_cancel_right, ih] at h
      push_cast
      exact h.symm
  have hall' : ∀ i : ZMod N, ⟪Q i, Q (i + 1)⟫ = c := by
    intro i
    have := hall i.val
    rwa [ZMod.natCast_zmod_val] at this
  -- positive energy excludes the zero edge
  have hc1 : c < 1 := by
    rcases eq_or_lt_of_le (inner_le_one (hQ 0) (hQ 1)) with h | h
    · exfalso
      have hE := polyEnergy_round hQ hna
      have : polyEnergy (roundMetric n) N Q = 0 := by
        rw [hE]
        have hz : ∀ i : ZMod N, ang2 ⟪Q i, Q (i + 1)⟫ = 0 := by
          intro i
          rw [hall' i, hcdef, h, ang2, Real.arccos_one]
          norm_num
        simp [hz]
      exact absurd this (ne_of_gt hpos)
    · exact h
  have hna0 : c ≠ -1 := by
    have h := hna 0
    rw [zero_add] at h
    exact h
  have hc0 : -1 < c := lt_of_le_of_ne (neg_one_le_inner (hQ 0) (hQ 1)) (Ne.symm hna0)
  -- the recurrence
  have hrec : ∀ j : ZMod N, Q (j - 1) + Q (j + 1) = (2 * c) • Q j := by
    intro j
    have h := (hvert j).2
    rw [hall' j] at h
    exact h hc1
  -- the closed form
  set θ := Real.arccos c with hθ
  set s := Real.sqrt (1 - c ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hss : s ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by nlinarith)
  have hcos : Real.cos θ = c := Real.cos_arccos hc0.le hc1.le
  have hsin : Real.sin θ = s := Real.sin_arccos c
  have hθ0 : 0 < θ := Real.arccos_pos.mpr hc1
  have hθπ : θ < π := Real.arccos_lt_pi.mpr hc0
  set x := Q 0 with hx
  set u := s⁻¹ • (Q 1 - c • Q 0) with hu
  have hpp : ⟪x, x⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hQ 0, one_pow]
  have hxu : ⟪x, u⟫ = 0 := by
    rw [hu, real_inner_smul_right, inner_sub_right, real_inner_smul_right, ← hx, hpp, hx, ← hcdef]
    ring
  have hu1 : ‖u‖ = 1 := by
    have hq : ‖Q 1 - c • Q 0‖ ^ 2 = s ^ 2 := by
      rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, hQ 0, hQ 1, Real.norm_eq_abs,
        mul_pow, sq_abs, real_inner_comm, ← hcdef, hss]
      ring
    have h2 : ‖Q 1 - c • Q 0‖ = s := by
      rw [← Real.sqrt_sq (norm_nonneg _), hq, Real.sqrt_sq hs0.le]
    rw [hu, norm_smul, h2, norm_inv, Real.norm_eq_abs, abs_of_pos hs0, inv_mul_cancel₀ hs0.ne']
  have hform : ∀ k : ℕ, Q (k : ZMod N) = Real.cos (θ * k) • x + Real.sin (θ * k) • u ∧
      Q ((k + 1 : ℕ) : ZMod N) = Real.cos (θ * (k + 1 : ℕ)) • x + Real.sin (θ * (k + 1 : ℕ)) • u := by
    intro k
    induction k with
    | zero =>
      constructor
      · simp [hx]
      · simp only [zero_add, Nat.cast_one, mul_one, hcos, hsin]
        rw [hu, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul, hx]
        abel
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hr := hrec ((k + 1 : ℕ) : ZMod N)
      have e1 : ((k + 1 : ℕ) : ZMod N) - 1 = (k : ZMod N) := by push_cast; ring
      have e2 : ((k + 1 : ℕ) : ZMod N) + 1 = ((k + 1 + 1 : ℕ) : ZMod N) := by push_cast; ring
      rw [e1, e2, ih.1, ih.2] at hr
      have h2 : Q ((k + 1 + 1 : ℕ) : ZMod N) = (2 * c) • (Real.cos (θ * (k + 1 : ℕ)) • x +
          Real.sin (θ * (k + 1 : ℕ)) • u) - (Real.cos (θ * k) • x + Real.sin (θ * k) • u) := by
        rw [← hr]
        abel
      rw [h2]
      have hc' := cos_step (θ * k) θ
      have hs' := sin_step (θ * k) θ
      rw [hcos] at hc' hs'
      have ea : θ * ((k + 1 + 1 : ℕ) : ℝ) = θ * k + 2 * θ := by push_cast; ring
      have eb : θ * ((k + 1 : ℕ) : ℝ) = θ * k + θ := by push_cast; ring
      rw [ea, eb, hc', hs']
      simp only [smul_add, smul_smul, sub_smul]
      abel
  -- closing the polygon
  have hclose : Real.cos (θ * N) = 1 := by
    have h := (hform N).1
    rw [ZMod.natCast_self] at h
    exact (coeff_eq_of_comb (hQ 0) hu1 hxu h.symm).1
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff (θ * N)).mp hclose
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hπ : 0 < π := Real.pi_pos
  have hm0 : 0 < m := by
    have : 0 < (m : ℝ) * (2 * π) := by rw [hm]; positivity
    have : (0 : ℝ) < m := (mul_pos_iff_of_pos_right (by positivity)).mp this
    exact_mod_cast this
  have hmN : 2 * m < N := by
    have h1 : (m : ℝ) * (2 * π) < N * π := by
      rw [hm]
      nlinarith
    have : (2 * m : ℝ) < N := by nlinarith
    exact_mod_cast this
  refine ⟨x, u, m.toNat, hQ 0, hu1, hxu, by omega, by omega, fun k => ?_⟩
  have hθm : θ = 2 * π * (m.toNat : ℕ) / N := by
    have hmt : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
      have : ((m.toNat : ℤ) : ℝ) = (m : ℝ) := by rw [Int.toNat_of_nonneg hm0.le]
      exact_mod_cast this
    rw [hmt]
    field_simp
    linarith
  rw [← hθm]
  exact (hform k).1

/-! ### Regular polygons are critical -/

/-- The point at angle t on the great circle of the orthonormal pair (x, u). -/
def circ (x u : Ambient n) (t : ℝ) : Ambient n := Real.cos t • x + Real.sin t • u

theorem circ_add_two_pi (x u : Ambient n) (t : ℝ) (k : ℕ) :
    circ x u (t + k * (2 * π)) = circ x u t := by
  rw [circ, circ, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

theorem circ_sub_add (x u : Ambient n) (t θ : ℝ) :
    circ x u (t - θ) + circ x u (t + θ) = (2 * Real.cos θ) • circ x u t := by
  have hc : Real.cos (t - θ) + Real.cos (t + θ) = 2 * Real.cos θ * Real.cos t := by
    rw [Real.cos_sub, Real.cos_add]
    ring
  have hs : Real.sin (t - θ) + Real.sin (t + θ) = 2 * Real.cos θ * Real.sin t := by
    rw [Real.sin_sub, Real.sin_add]
    ring
  calc circ x u (t - θ) + circ x u (t + θ)
      = (Real.cos (t - θ) + Real.cos (t + θ)) • x +
          (Real.sin (t - θ) + Real.sin (t + θ)) • u := by
        simp only [circ, add_smul]
        abel
    _ = (2 * Real.cos θ) • circ x u t := by
        rw [hc, hs, circ, smul_add, smul_smul, smul_smul]

theorem inner_circ {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    (s t : ℝ) : ⟪circ x u s, circ x u t⟫ = Real.cos (t - s) := by
  rw [circ, circ, inner_comb hx hu hxu, Real.cos_sub]
  ring

/-- The regular m-gon with N vertices on the great circle of (x, u). -/
def regular (N m : ℕ) (x u : Ambient n) (i : ZMod N) : Ambient n :=
  circ x u (2 * π * m / N * i.val)

theorem regular_natCast {N : ℕ} [NeZero N] (m : ℕ) (x u : Ambient n) (k : ℕ) :
    regular N m x u (k : ZMod N) = circ x u (2 * π * m / N * k) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  rw [regular, ZMod.val_natCast]
  have hk : (k : ℝ) = ((k % N : ℕ) : ℝ) + N * ((k / N : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k N).symm
  have h : 2 * π * m / N * k = 2 * π * m / N * ((k % N : ℕ) : ℝ) + ((m * (k / N) : ℕ) : ℝ) * (2 * π) := by
    rw [hk]
    push_cast
    field_simp
    try ring
  rw [h, circ_add_two_pi]

theorem norm_regular {N : ℕ} {m : ℕ} {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1)
    (hxu : ⟪x, u⟫ = 0) (i : ZMod N) : ‖regular N m x u i‖ = 1 :=
  norm_cos_sin hx hu hxu _

/-- Consecutive vertices of a regular polygon have inner product cos(2πm/N). -/
theorem inner_regular {N : ℕ} [NeZero N] {m : ℕ} {x u : Ambient n} (hx : ‖x‖ = 1)
    (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0) (i : ZMod N) :
    ⟪regular N m x u i, regular N m x u (i + 1)⟫ = Real.cos (2 * π * m / N) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ZMod N) = i := ⟨i.val, ZMod.natCast_zmod_val i⟩
  have hk1 : (k : ZMod N) + 1 = ((k + 1 : ℕ) : ZMod N) := by push_cast; rfl
  rw [hk1, regular_natCast, regular_natCast, inner_circ hx hu hxu]
  congr 1
  push_cast
  ring

/-- The neighbours of a vertex of a regular polygon add up to 2 cos θ times the vertex. -/
theorem regular_sub_add {N : ℕ} [NeZero N] (m : ℕ) (x u : Ambient n) (i : ZMod N) :
    regular N m x u (i - 1) + regular N m x u (i + 1) =
      (2 * Real.cos (2 * π * m / N)) • regular N m x u i := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ZMod N) = i := ⟨i.val, ZMod.natCast_zmod_val i⟩
  have hN1 : 1 ≤ N := Nat.pos_of_neZero N
  have hi1 : (k : ZMod N) + 1 = ((k + 1 : ℕ) : ZMod N) := by push_cast; rfl
  have him : (k : ZMod N) - 1 = ((k + (N - 1) : ℕ) : ZMod N) := by
    push_cast [Nat.cast_sub hN1]
    rw [ZMod.natCast_self]
    ring
  rw [hi1, him, regular_natCast, regular_natCast, regular_natCast]
  have hN1 : 1 ≤ N := Nat.pos_of_neZero N
  have e1 : 2 * π * m / N * ((k + (N - 1) : ℕ) : ℝ) =
      (2 * π * m / N * k - 2 * π * m / N) + (m : ℕ) * (2 * π) := by
    push_cast [Nat.cast_sub hN1]
    field_simp
    ring
  have e2 : 2 * π * m / N * ((k + 1 : ℕ) : ℝ) = 2 * π * m / N * k + 2 * π * m / N := by
    push_cast
    ring
  rw [e1, circ_add_two_pi, e2]
  exact circ_sub_add x u _ _

/-- Regular m-gons, 0 < 2m < N, are critical for the round polygon energy. -/
theorem polyCritical_regular {N : ℕ} [NeZero N] {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N)
    {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    {q : ZMod N → Sphere n} (hq : ∀ i, (q i : Ambient n) = regular N m x u i) :
    PolyCritical (roundMetric n) N q := by
  intro c c' hc0 hcn hcd
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hπ : 0 < π := Real.pi_pos
  set θ := 2 * π * m / N with hθ
  have hθ0 : 0 < θ := by
    rw [hθ]
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hθπ : θ < π := by
    rw [hθ, div_lt_iff₀ hN]
    have : (2 * m : ℝ) < N := by exact_mod_cast hmN
    nlinarith
  have hcθ : -1 < Real.cos θ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
    rw [Real.cos_pi] at h
    exact h
  have hQ : ∀ i, c 0 i = regular N m x u i := by
    intro i
    rw [hc0]
    exact hq i
  have hna : ∀ i : ZMod N, ⟪c 0 i, c 0 (i + 1)⟫ ≠ -1 := by
    intro i
    rw [hQ, hQ, inner_regular hx hu hxu]
    exact ne_of_gt hcθ
  have hder := polyEnergy_hasDerivAt hcn hcd hna
  -- the tangent vectors are orthogonal to the vertices
  have hci : ∀ i, HasDerivAt (fun r => c r i) (c' i) 0 := fun i => hasDerivAt_pi.mp hcd i
  have horth : ∀ i, ⟪c' i, c 0 i⟫ = 0 := by
    intro i
    have h1 := HasDerivAt.inner ℝ (hci i) (hci i)
    have h2 : (fun r => ⟪c r i, c r i⟫) = fun _ => (1 : ℝ) := by
      funext r
      rw [real_inner_self_eq_norm_sq, hcn r i, one_pow]
    rw [h2] at h1
    have h3 := h1.unique (hasDerivAt_const 0 (1 : ℝ))
    rw [real_inner_comm (c' i) (c 0 i)] at h3
    linarith
  -- the derivative vanishes
  have hzero : (∑ i : ZMod N, G ⟪c 0 i, c 0 (i + 1)⟫ *
      (⟪c 0 i, c' (i + 1)⟫ + ⟪c' i, c 0 (i + 1)⟫)) = 0 := by
    have hG : ∀ i : ZMod N, G ⟪c 0 i, c 0 (i + 1)⟫ = G (Real.cos θ) := by
      intro i
      rw [hQ, hQ, inner_regular hx hu hxu]
    simp only [hG, ← Finset.mul_sum]
    have hshift : ∑ i : ZMod N, ⟪c 0 i, c' (i + 1)⟫ = ∑ i : ZMod N, ⟪c 0 (i - 1), c' i⟫ := by
      have := Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) (fun i => ⟪c 0 (i - 1), c' i⟫)
      simp only [Equiv.coe_addRight, add_sub_cancel_right] at this
      exact this
    rw [Finset.sum_add_distrib, hshift, ← Finset.sum_add_distrib]
    have hterm : ∀ i : ZMod N, ⟪c 0 (i - 1), c' i⟫ + ⟪c' i, c 0 (i + 1)⟫ = 0 := by
      intro i
      rw [real_inner_comm (c' i) (c 0 (i - 1)), ← inner_add_right, hQ, hQ, regular_sub_add,
        real_inner_smul_right, ← hQ, horth, mul_zero]
    simp [hterm]
  rw [hzero, mul_zero] at hder
  exact hder

/-- The energy of a regular m-gon is (2πm)². -/
theorem polyEnergy_regular {N : ℕ} [NeZero N] {m : ℕ} (hmN : 2 * m < N) {x u : Ambient n}
    (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0) :
    polyEnergy (roundMetric n) N (regular N m x u) = (2 * π * m) ^ 2 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hπ : 0 < π := Real.pi_pos
  set θ := 2 * π * m / N with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθπ : θ < π := by
    rw [hθ, div_lt_iff₀ hN]
    have : (2 * m : ℝ) < N := by exact_mod_cast hmN
    nlinarith
  have hcθ : -1 < Real.cos θ := by
    rcases eq_or_lt_of_le hθ0 with h | h
    · rw [← h, Real.cos_zero]
      norm_num
    · have h' := Real.cos_lt_cos_of_nonneg_of_le_pi h.le le_rfl hθπ
      rw [Real.cos_pi] at h'
      exact h'
  have hna : ∀ i : ZMod N, ⟪regular N m x u i, regular N m x u (i + 1)⟫ ≠ -1 := by
    intro i
    rw [inner_regular hx hu hxu]
    exact ne_of_gt hcθ
  rw [polyEnergy_round (norm_regular hx hu hxu) hna]
  have hterm : ∀ i : ZMod N, ang2 ⟪regular N m x u i, regular N m x u (i + 1)⟫ = θ ^ 2 := by
    intro i
    rw [inner_regular hx hu hxu, ang2, Real.arccos_cos hθ0 hθπ.le]
  simp only [hterm, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [hθ]
  field_simp
  try ring

end

end Finsler.RoundPolygon
