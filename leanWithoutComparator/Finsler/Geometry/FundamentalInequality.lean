module

public import Finsler.Geometry.FiberLegendre
public import Finsler.Analysis.HessianMonotone

/-! The fundamental inequality of Finsler geometry. For a nonnegative even two-homogeneous
differentiable function with positive Hessian away from zero, the derivative is monotone
(segments through zero are handled by homogeneity), the function lies above its tangent planes,
and de(u)ξ ≤ 2√(e(u)e(ξ)) by optimizing a quadratic in the scaling of ξ. For the actual metric
this reads d_vF²(x,u)ξ ≤ 2F(x,u)F(x,ξ) on tangent vectors. -/

@[expose] public section

namespace Finsler.FundamentalInequality

open Set

section Abstract

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {e : V → ℝ} (hdiff : Differentiable ℝ e)
  (hsmooth : ∀ z : V, z ≠ 0 → ContDiffAt ℝ 2 e z)
  (hpos : ∀ z : V, z ≠ 0 → ∀ d : V, d ≠ 0 → 0 < fderiv ℝ (fderiv ℝ e) z d d)
  (hhom : ∀ (r : ℝ) (z : V), e (r • z) = r ^ 2 * e z)
  (hnonneg : ∀ z : V, 0 ≤ e z)

include hdiff hhom in
/-- The derivative of a two-homogeneous function is one-homogeneous. -/
theorem fderiv_smul (r : ℝ) (hr : r ≠ 0) (z : V) : fderiv ℝ e (r • z) = r • fderiv ℝ e z := by
  have h1 : HasFDerivAt (fun y => e (r • y)) ((fderiv ℝ e (r • z)).comp (r • ContinuousLinearMap.id ℝ V)) z :=
    (hdiff (r • z)).hasFDerivAt.comp z
      ((r • ContinuousLinearMap.id ℝ V).hasFDerivAt (x := z))
  have h2 : HasFDerivAt (fun y => e (r • y)) ((r ^ 2) • fderiv ℝ e z) z := by
    have h := ((hdiff z).hasFDerivAt.const_mul (r ^ 2))
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => hhom r y)
  have heq := h1.unique h2
  ext k
  have hk := congrArg (fun L : V →L[ℝ] ℝ => L k) heq
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hk
  simp only [smul_apply, smul_eq_mul]
  have hk' : r * (fderiv ℝ e (r • z) k) = r * (r * fderiv ℝ e z k) := by
    rw [hk]
    ring
  exact mul_left_cancel₀ hr hk'

include hdiff hhom in
theorem euler (z : V) : fderiv ℝ e z z = 2 * e z := by
  have h := (hdiff z).hasFDerivAt.apply_self_eq_nsmul_of_homogeneous (k := 2)
    (fun r v => by simpa only [smul_eq_mul] using hhom r v)
  simpa only [nsmul_eq_mul, Nat.cast_ofNat] using h

include hdiff hsmooth hpos hhom hnonneg in
/-- Monotonicity of the derivative. -/
theorem fderiv_monotone (v w : V) : 0 ≤ (fderiv ℝ e v - fderiv ℝ e w) (v - w) := by
  by_cases hvw : v = w
  · simp [hvw]
  by_cases hseg : ∀ s ∈ Icc (0 : ℝ) 1, w + s • (v - w) ≠ 0
  · exact (Finsler.HessianMonotone.derivative_increment_pos hvw
      (fun s hs => hsmooth _ (hseg s hs)) hseg hpos).le
  push Not at hseg
  obtain ⟨s, hs, hz⟩ := hseg
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · -- w = 0
    rw [← hs0, zero_smul, add_zero] at hz
    rw [hz, sub_zero]
    have hd0 : fderiv ℝ e 0 = 0 := by
      have h := fderiv_smul hdiff hhom 2 (by norm_num) (0 : V)
      rw [smul_zero] at h
      have h2 : (2 : ℝ) • fderiv ℝ e 0 - fderiv ℝ e 0 = 0 := by rw [← h, sub_self]
      rw [two_smul, add_sub_cancel_right] at h2
      exact h2
    rw [hd0, sub_zero, euler hdiff hhom v]
    linarith [hnonneg v]
  rcases eq_or_lt_of_le hs.2 with hs1 | hs1
  · -- v = 0
    rw [hs1, one_smul, add_sub_cancel] at hz
    rw [hz, zero_sub]
    have hd0 : fderiv ℝ e 0 = 0 := by
      have h := fderiv_smul hdiff hhom 2 (by norm_num) (0 : V)
      rw [smul_zero] at h
      have h2 : (2 : ℝ) • fderiv ℝ e 0 - fderiv ℝ e 0 = 0 := by rw [← h, sub_self]
      rw [two_smul, add_sub_cancel_right] at h2
      exact h2
    rw [hd0, zero_sub, map_neg, neg_apply, neg_neg, euler hdiff hhom w]
    linarith [hnonneg w]
  · -- w = -λ v with λ = s / (1 - s)
    have h1s : 0 < 1 - s := by linarith
    set l := s / (1 - s) with hl
    have hl0 : 0 < l := div_pos hs0 h1s
    have hwv : w = (-l) • v := by
      have h' : (1 - s) • w = (-s) • v := by
        have := hz
        rw [smul_sub] at this
        have h2 : (1 - s) • w + s • v = 0 := by
          rw [sub_smul, one_smul]
          rw [← this]
          abel
        rw [neg_smul, eq_neg_iff_add_eq_zero]
        exact h2
      have h1s' : (1 - s) ≠ 0 := h1s.ne'
      calc w = (1 - s)⁻¹ • ((1 - s) • w) := by rw [smul_smul, inv_mul_cancel₀ h1s', one_smul]
        _ = (1 - s)⁻¹ • ((-s) • v) := by rw [h']
        _ = (-l) • v := by rw [smul_smul, hl]; congr 1; field_simp
    rw [hwv, fderiv_smul hdiff hhom (-l) (by linarith) v]
    have hexp : v - (-l) • v = (1 + l) • v := by
      rw [neg_smul, sub_neg_eq_add, add_smul, one_smul]
    rw [hexp, map_smul, smul_eq_mul, sub_apply, smul_apply,
      smul_eq_mul, euler hdiff hhom v]
    have := hnonneg v
    have : 0 ≤ (1 + l) * (2 * e v - -l * (2 * e v)) := by
      apply mul_nonneg (by linarith)
      nlinarith
    exact this

include hdiff hsmooth hpos hhom hnonneg in
/-- The function lies above its tangent planes. -/
theorem tangent_le (z y : V) : e z + fderiv ℝ e z (y - z) ≤ e y := by
  let h : ℝ → ℝ := fun s => e (z + s • (y - z)) - s * fderiv ℝ e z (y - z)
  let h' : ℝ → ℝ := fun s => fderiv ℝ e (z + s • (y - z)) (y - z) - fderiv ℝ e z (y - z)
  have hγ (s : ℝ) : HasDerivAt (fun r : ℝ => z + r • (y - z)) (y - z) s := by
    have h0 := ((hasDerivAt_id' s).smul_const (y - z)).const_add z
    rw [one_smul] at h0
    exact h0
  have hd (s : ℝ) : HasDerivAt h (h' s) s := by
    have h1 := (hdiff (z + s • (y - z))).hasFDerivAt.comp_hasDerivAt s (hγ s)
    have h2 := (hasDerivAt_id' s).mul_const (fderiv ℝ e z (y - z))
    rw [one_mul] at h2
    exact h1.sub h2
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope h h' zero_lt_one
    (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => hd s)
  have hmono := fderiv_monotone hdiff hsmooth hpos hhom hnonneg (z + c • (y - z)) z
  have hsub : z + c • (y - z) - z = c • (y - z) := by abel
  rw [hsub, map_smul, smul_eq_mul] at hmono
  have hc' : 0 ≤ h' c := by
    have h0 : 0 ≤ c * h' c := by
      simp only [h', sub_apply] at hmono ⊢
      rw [mul_sub]
      linarith
    exact (mul_nonneg_iff_of_pos_left hc.1).mp h0
  rw [hslope] at hc'
  have hz1 : z + (1 : ℝ) • (y - z) = y := by rw [one_smul]; abel
  have hz0 : z + (0 : ℝ) • (y - z) = z := by rw [zero_smul, add_zero]
  have hh1 : h 1 = e y - fderiv ℝ e z (y - z) := by
    simp only [h]
    rw [hz1, one_mul]
  have hh0 : h 0 = e z := by
    simp only [h]
    rw [hz0, zero_mul, sub_zero]
  rw [hh1, hh0, sub_zero, div_one] at hc'
  linarith

include hdiff hsmooth hpos hhom hnonneg in
/-- The fundamental inequality: de(u)ξ ≤ 2√(e(u)e(ξ)). -/
theorem fderiv_le (u ξ : V) :
    fderiv ℝ e u ξ ≤ 2 * Real.sqrt (e u) * Real.sqrt (e ξ) := by
  set D := fderiv ℝ e u ξ with hD
  set A := e ξ with hA
  set B := e u with hB
  have hA0 : 0 ≤ A := hnonneg ξ
  have hB0 : 0 ≤ B := hnonneg u
  -- the quadratic t² A − t D + B is nonnegative for t > 0
  have hq : ∀ t : ℝ, 0 < t → t * D ≤ t ^ 2 * A + B := by
    intro t ht
    have h := tangent_le hdiff hsmooth hpos hhom hnonneg u (t • ξ)
    rw [map_sub, map_smul, smul_eq_mul, euler hdiff hhom u, hhom t ξ] at h
    linarith
  have hR : 0 ≤ 2 * Real.sqrt B * Real.sqrt A := by positivity
  by_cases hD0 : D ≤ 0
  · linarith
  push Not at hD0
  by_cases hA0' : A = 0
  · exfalso
    have h := hq ((B + 1) / D) (by positivity)
    rw [hA0', mul_zero, zero_add, div_mul_cancel₀ _ hD0.ne'] at h
    linarith
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA0')
  have h := hq (D / (2 * A)) (by positivity)
  have hkey : D ^ 2 ≤ 4 * A * B := by
    have h' : D / (2 * A) * D ≤ (D / (2 * A)) ^ 2 * A + B := h
    field_simp at h'
    nlinarith
  have hsq : (2 * Real.sqrt B * Real.sqrt A) ^ 2 = 4 * A * B := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hB0, Real.sq_sqrt hA0]
    ring
  nlinarith [hsq, hkey, hR, sq_nonneg (D - 2 * Real.sqrt B * Real.sqrt A),
    sq_nonneg (D + 2 * Real.sqrt B * Real.sqrt A)]

end Abstract


section Ambient

open Finsler.SphereGeometry Finsler.Geometry Finsler.AmbientLagrangian Finsler.FiberLegendre
open Finsler.FiberEnergy
open scoped RealInnerProductSpace

variable {n : ℕ}

theorem halfSquared_fderiv_le (F : ReversibleMetric n) (x : Sphere n) (u ξ : Model n) :
    fderiv ℝ (halfSquared F x) u ξ ≤
      2 * Real.sqrt (halfSquared F x u) * Real.sqrt (halfSquared F x ξ) :=
  fderiv_le (halfSquared_differentiable F x)
    (fun _ hz => (halfSquared_smoothAt F x hz).of_le (by simp))
    (fun _ hz _ hd => halfSquared_hessian_pos F x hz hd) (fun r z => halfSquared_smul F x r z)
    (halfSquared_nonneg F x) u ξ

/-- The fundamental inequality for the ambient Lagrangian on tangent vectors:
d_vF²(q,u)ξ ≤ 2F(q,u)F(q,ξ). -/
theorem velocityDifferential_le (F : ReversibleMetric n) {q u ξ : Ambient n} (hq : ‖q‖ = 1)
    (hu : ⟪q, u⟫ = 0) (hξ : ⟪q, ξ⟫ = 0) :
    velocityDifferential F (q, u) ξ ≤
      2 * Real.sqrt (lagrangian F (q, u)) * Real.sqrt (lagrangian F (q, ξ)) := by
  let x : Sphere n := ⟨q, by simpa using hq⟩
  obtain ⟨u', rfl⟩ := exists_fiber_of_orthogonal x hu
  obtain ⟨ξ', rfl⟩ := exists_fiber_of_orthogonal x hξ
  change velocityDifferential F ((x : Ambient n), ambientMap x u') (ambientMap x ξ') ≤
    2 * Real.sqrt (lagrangian F ((x : Ambient n), ambientMap x u')) *
      Real.sqrt (lagrangian F ((x : Ambient n), ambientMap x ξ'))
  rw [velocityDifferential_fiber, lagrangian_fiber, lagrangian_fiber,
    Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num)]
  have h := halfSquared_fderiv_le F x u' ξ'
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hR : 2 * (Real.sqrt 2 * Real.sqrt (halfSquared F x u')) *
      (Real.sqrt 2 * Real.sqrt (halfSquared F x ξ')) =
      2 * (2 * Real.sqrt (halfSquared F x u') * Real.sqrt (halfSquared F x ξ')) := by
    have : 2 * (Real.sqrt 2 * Real.sqrt (halfSquared F x u')) *
        (Real.sqrt 2 * Real.sqrt (halfSquared F x ξ')) =
        2 * ((Real.sqrt 2 * Real.sqrt 2) * Real.sqrt (halfSquared F x u') *
          Real.sqrt (halfSquared F x ξ')) := by ring
    rw [this, h2]
  rw [hR]
  linarith

end Ambient

end Finsler.FundamentalInequality
