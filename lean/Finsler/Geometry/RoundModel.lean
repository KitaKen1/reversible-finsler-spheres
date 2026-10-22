module

public import Finsler.Geometry.RoundLabel

/-! The model function on the chart: squares of the negative and positive parts.

For a pair z and a fibre vector ξ = (τ, V) let A = negV z V (the normal projection of the low
modes of V). Put

  sqN z ξ = |A|²,   sqP z ξ = |τ|² + |V − A|²,   sqF = sqN + sqP,
  model z ξ = (2πm)² − sqN z ξ + sqP z ξ

(ℓ² norms of polygons). For z ∈ V₂ the projection negV z is idempotent, so along the reflection
line ξ + t J z ξ the negative part is (1 + t) A and the positive part (1 − t)(τ, V − A):

  sqN(ξ + t Jξ) = (1 + t)² sqN ξ,   sqP(ξ + t Jξ) = (1 − t)² sqP ξ.

Hence the derivative of the model along (0, J z ξ) is −2 sqF and that of sqF is 2 sqN − 2 sqP,
of absolute value at most 2 sqF; sqF is comparable to ‖ξ‖² on V₂. -/

@[expose] public section

namespace Finsler.RoundModel

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundPolygon Finsler.RoundHessian
open Finsler.RoundModes Finsler.RoundNondeg Finsler.RoundCoords Finsler.RoundSpectral
open Finsler.RoundPenHess Finsler.RoundPenForm Finsler.AmbientPenalty Finsler.PolygonSmooth
open Finsler.RoundChart Finsler.RoundSplit Finsler.RoundQR Finsler.RoundLabel
open Finset Filter Set Metric
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N] {m : ℕ}

/-! ### Idempotence of the negative projection -/

theorem low_low (hmN : 2 * m < N) (V : ZMod N → Ambient n) : low m (low m V) = low m V := by
  unfold low
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : 2 * j < N := by have := Finset.mem_range.mp hj; omega
  rw [show mode j (∑ j' ∈ range m, mode j' V) = ∑ j' ∈ range m, mode j (mode j' V) by
    have hlin : IsLinearMap ℝ (mode (n := n) (N := N) j) := ⟨mode_add j, fun r V => mode_smul j r V⟩
    exact map_sum (hlin.mk' _) _ _]
  rw [Finset.sum_eq_single j]
  · have e : mode j V = regular N j (coefPair j V).1 (coefPair j V).2 := rfl
    rw [e, mode_regular hj' hj', if_pos rfl]
  · intro j' hj'm hne
    have h2 : 2 * j' < N := by have := Finset.mem_range.mp hj'm; omega
    have e : mode j' V = regular N j' (coefPair j' V).1 (coefPair j' V).2 := rfl
    rw [e, mode_regular hj' h2, if_neg (Ne.symm hne)]
  · intro h
    exact absurd hj h

theorem negV_negV (hmN : 2 * m < N) {z : Ambient n × Ambient n} (hz : z ∈ V2)
    (V : ZMod N → Ambient n) : negV m z (negV m z V) = negV m z V := by
  unfold negV
  rw [low_onVert, low_low hmN]
  exact onVert_projW_idem hz _

theorem negV_add (z : Ambient n × Ambient n) (V W : ZMod N → Ambient n) :
    negV m z (V + W) = negV m z V + negV m z W := by
  unfold negV
  rw [low_add, map_add]

theorem negV_smul (z : Ambient n × Ambient n) (r : ℝ) (V : ZMod N → Ambient n) :
    negV m z (r • V) = r • negV m z V := by
  unfold negV
  rw [low_smul, map_smul]

/-! ### The squares -/

/-- The negative part of a fibre vector as a polygon. -/
def negP (p : (Ambient n × Ambient n) × Fib n N m) : ZMod N → Ambient n :=
  negV m p.1 (p.2.2 : ZMod N → Ambient n)

/-- The square of the negative part. -/
def sqN (p : (Ambient n × Ambient n) × Fib n N m) : ℝ := pair (negP p) (negP p)

/-- The square of the positive part. -/
def sqP (p : (Ambient n × Ambient n) × Fib n N m) : ℝ :=
  p.2.1.1 ^ 2 + p.2.1.2.1 ^ 2 + p.2.1.2.2 ^ 2 +
    pair ((p.2.2 : ZMod N → Ambient n) - negP p) ((p.2.2 : ZMod N → Ambient n) - negP p)

/-- The square of the fibre vector adapted to the splitting. -/
def sqF (p : (Ambient n × Ambient n) × Fib n N m) : ℝ := sqN p + sqP p

variable (m) in
/-- The model function. -/
def model (p : (Ambient n × Ambient n) × Fib n N m) : ℝ := (2 * π * m) ^ 2 - sqN p + sqP p

theorem sqN_nonneg (p : (Ambient n × Ambient n) × Fib n N m) : 0 ≤ sqN p := pair_self_nonneg _

theorem sqP_nonneg (p : (Ambient n × Ambient n) × Fib n N m) : 0 ≤ sqP p := by
  unfold sqP
  have := pair_self_nonneg ((p.2.2 : ZMod N → Ambient n) - negP p)
  positivity

theorem sqF_nonneg (p : (Ambient n × Ambient n) × Fib n N m) : 0 ≤ sqF p :=
  add_nonneg (sqN_nonneg p) (sqP_nonneg p)

theorem pair_smul_smul (r : ℝ) (w : ZMod N → Ambient n) :
    pair (r • w) (r • w) = r ^ 2 * pair w w := by
  simp only [pair, Pi.smul_apply, real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem negV_sub (z : Ambient n × Ambient n) (V W : ZMod N → Ambient n) :
    negV m z (V - W) = negV m z V - negV m z W := by
  rw [sub_eq_add_neg, negV_add, ← neg_one_smul ℝ W, negV_smul, neg_one_smul, ← sub_eq_add_neg]

section Line

variable (hm : 0 < m) (hmN : 2 * m < N) {z : Ambient n × Ambient n} (hz : z ∈ V2)
include hz

theorem fib_line_V (ξ : Fib n N m) (t : ℝ) :
    (((ξ + t • J hm hmN z ξ).2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) =
      (ξ.2 : ZMod N → Ambient n) + t • ((2 : ℝ) • negV m z (ξ.2 : ZMod N → Ambient n) -
        (ξ.2 : ZMod N → Ambient n)) := by
  rw [← (J_apply hm hmN z ξ).2]
  rfl

theorem negP_line (ξ : Fib n N m) (t : ℝ) :
    negP (z, ξ + t • J hm hmN z ξ) = (1 + t) • negP (z, ξ) := by
  unfold negP
  rw [fib_line_V hm hmN hz ξ t, negV_add, negV_smul, negV_sub, negV_smul, negV_negV hmN hz]
  rw [add_smul, one_smul, two_smul]
  abel

theorem pos_line (ξ : Fib n N m) (t : ℝ) :
    (((ξ + t • J hm hmN z ξ).2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) -
        negP (z, ξ + t • J hm hmN z ξ) =
      (1 - t) • ((ξ.2 : ZMod N → Ambient n) - negP (z, ξ)) := by
  rw [negP_line hm hmN hz ξ t, fib_line_V hm hmN hz ξ t]
  unfold negP
  simp only [smul_sub, sub_smul, add_smul, one_smul, two_smul, smul_add]
  abel

theorem tau_line (ξ : Fib n N m) (t : ℝ) :
    (ξ + t • J hm hmN z ξ).1 = (1 - t) • ξ.1 := by
  change ξ.1 + t • (J hm hmN z ξ).1 = (1 - t) • ξ.1
  rw [(J_apply hm hmN z ξ).1, sub_smul, one_smul, smul_neg, sub_eq_add_neg]

theorem sqN_line (ξ : Fib n N m) (t : ℝ) :
    sqN (z, ξ + t • J hm hmN z ξ) = (1 + t) ^ 2 * sqN (z, ξ) := by
  unfold sqN
  rw [negP_line hm hmN hz ξ t, pair_smul_smul]

theorem sqP_line (ξ : Fib n N m) (t : ℝ) :
    sqP (z, ξ + t • J hm hmN z ξ) = (1 - t) ^ 2 * sqP (z, ξ) := by
  unfold sqP
  have h := tau_line hm hmN hz ξ t
  have h1 : (ξ + t • J hm hmN z ξ).1.1 = (1 - t) * ξ.1.1 := by rw [h]; rfl
  have h2 : (ξ + t • J hm hmN z ξ).1.2.1 = (1 - t) * ξ.1.2.1 := by rw [h]; rfl
  have h3 : (ξ + t • J hm hmN z ξ).1.2.2 = (1 - t) * ξ.1.2.2 := by rw [h]; rfl
  change ((ξ + t • J hm hmN z ξ).1.1) ^ 2 + ((ξ + t • J hm hmN z ξ).1.2.1) ^ 2 +
      ((ξ + t • J hm hmN z ξ).1.2.2) ^ 2 +
      pair ((((ξ + t • J hm hmN z ξ).2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) -
        negP (z, ξ + t • J hm hmN z ξ))
        ((((ξ + t • J hm hmN z ξ).2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) -
        negP (z, ξ + t • J hm hmN z ξ)) = _
  rw [h1, h2, h3, pos_line hm hmN hz ξ t, pair_smul_smul]
  ring

end Line

/-! ### Smoothness -/

theorem negV_contDiff : ContDiff ℝ ∞ fun q : (Ambient n × Ambient n) × (ZMod N → Ambient n) =>
    negV m q.1 q.2 := by
  have hlow : ContDiff ℝ ∞ (low (n := n) (N := N) m) := by
    have hlin : IsLinearMap ℝ (low (n := n) (N := N) m) := ⟨low_add m, fun r V => low_smul m r V⟩
    exact (LinearMap.toContinuousLinearMap (hlin.mk' _)).contDiff
  rw [contDiff_pi]
  intro i
  have hli : ContDiff ℝ ∞ fun q : (Ambient n × Ambient n) × (ZMod N → Ambient n) => low m q.2 i :=
    (contDiff_apply ℝ (Ambient n) i).comp (hlow.comp contDiff_snd)
  have hx : ContDiff ℝ ∞ fun q : (Ambient n × Ambient n) × (ZMod N → Ambient n) => q.1.1 :=
    contDiff_fst.comp contDiff_fst
  have hu : ContDiff ℝ ∞ fun q : (Ambient n × Ambient n) × (ZMod N → Ambient n) => q.1.2 :=
    contDiff_snd.comp contDiff_fst
  change ContDiff ℝ ∞ fun q : (Ambient n × Ambient n) × (ZMod N → Ambient n) =>
    low m q.2 i - (⟪q.1.1, low m q.2 i⟫ • q.1.1 + ⟪q.1.2, low m q.2 i⟫ • q.1.2)
  exact hli.sub (((hx.inner ℝ hli).smul hx).add ((hu.inner ℝ hli).smul hu))

theorem fibV_contDiff : ContDiff ℝ ∞ fun p : (Ambient n × Ambient n) × Fib n N m =>
    ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) :=
  (kern (n := n) (N := N) m).subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd)

theorem negP_contDiff : ContDiff ℝ ∞ (negP (n := n) (N := N) (m := m)) :=
  ContDiff.comp (g := fun q : (Ambient n × Ambient n) × (ZMod N → Ambient n) => negV m q.1 q.2)
    (f := fun p : (Ambient n × Ambient n) × Fib n N m =>
      (p.1, ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n)))
    negV_contDiff (contDiff_fst.prodMk fibV_contDiff)

theorem pair_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ZMod N → Ambient n} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun x => pair (f x) (g x) := by
  unfold pair
  refine ContDiff.sum fun i _ => ?_
  exact ((contDiff_apply ℝ (Ambient n) i).comp hf).inner ℝ ((contDiff_apply ℝ (Ambient n) i).comp hg)

theorem sqN_contDiff : ContDiff ℝ ∞ (sqN (n := n) (N := N) (m := m)) :=
  pair_contDiff (negP_contDiff (n := n) (N := N) (m := m)) (negP_contDiff (n := n) (N := N) (m := m))

theorem sqP_contDiff : ContDiff ℝ ∞ (sqP (n := n) (N := N) (m := m)) := by
  unfold sqP
  have h1 : ContDiff ℝ ∞ fun p : (Ambient n × Ambient n) × Fib n N m => p.2.1.1 :=
    contDiff_fst.comp (contDiff_fst.comp contDiff_snd)
  have h2 : ContDiff ℝ ∞ fun p : (Ambient n × Ambient n) × Fib n N m => p.2.1.2.1 :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_fst.comp contDiff_snd))
  have h3 : ContDiff ℝ ∞ fun p : (Ambient n × Ambient n) × Fib n N m => p.2.1.2.2 :=
    contDiff_snd.comp (contDiff_snd.comp (contDiff_fst.comp contDiff_snd))
  have hd : ContDiff ℝ ∞ fun p : (Ambient n × Ambient n) × Fib n N m =>
      ((p.2.2 : kern (n := n) (N := N) m) : ZMod N → Ambient n) - negP p :=
    (fibV_contDiff (n := n) (N := N) (m := m)).sub (negP_contDiff (n := n) (N := N) (m := m))
  exact (((h1.pow 2).add (h2.pow 2)).add (h3.pow 2)).add (pair_contDiff hd hd)

theorem sqF_contDiff : ContDiff ℝ ∞ (sqF (n := n) (N := N) (m := m)) :=
  (sqN_contDiff (n := n) (N := N) (m := m)).add (sqP_contDiff (n := n) (N := N) (m := m))

theorem model_contDiff : ContDiff ℝ ∞ (model (n := n) (N := N) m) :=
  (contDiff_const.sub (sqN_contDiff (n := n) (N := N) (m := m))).add
    (sqP_contDiff (n := n) (N := N) (m := m))

/-! ### Derivatives along the reflection -/

/-- The fibre derivative is the derivative along fibre lines. -/
theorem hasDerivAt_fibre_line {f : (Ambient n × Ambient n) × Fib n N m → ℝ}
    {z : Ambient n × Ambient n} {ξ : Fib n N m} (hf : DifferentiableAt ℝ f (z, ξ))
    (v : Fib n N m) :
    HasDerivAt (fun t : ℝ => f (z, ξ + t • v)) (fderiv ℝ f (z, ξ) (0, v)) 0 := by
  have hl : HasDerivAt (fun t : ℝ => ((z, ξ + t • v) : (Ambient n × Ambient n) × Fib n N m))
      ((0 : Ambient n × Ambient n), v) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => ξ + t • v) v 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ξ
      rwa [one_smul] at this
    exact (hasDerivAt_const (0 : ℝ) z).prodMk h2
  exact hf.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)

section Derivs

variable (hm : 0 < m) (hmN : 2 * m < N) {z : Ambient n × Ambient n} (hz : z ∈ V2)
include hz

theorem fderiv_sqN_J (ξ : Fib n N m) :
    fderiv ℝ (sqN (n := n) (N := N) (m := m)) (z, ξ) (0, J hm hmN z ξ) = 2 * sqN (z, ξ) := by
  have h1 := hasDerivAt_fibre_line ((sqN_contDiff (m := m)).differentiable (by simp) (z, ξ))
    (J hm hmN z ξ)
  have h2 : HasDerivAt (fun t : ℝ => sqN (z, ξ + t • J hm hmN z ξ)) (2 * sqN (z, ξ)) 0 := by
    have e : (fun t : ℝ => sqN (z, ξ + t • J hm hmN z ξ)) = fun t => (1 + t) ^ 2 * sqN (z, ξ) :=
      funext fun t => sqN_line hm hmN hz ξ t
    rw [e]
    have h4 : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
    have h5 := (h4.pow 2).mul_const (sqN (z, ξ))
    convert h5 using 1
    norm_num
  exact h1.unique h2

theorem fderiv_sqP_J (ξ : Fib n N m) :
    fderiv ℝ (sqP (n := n) (N := N) (m := m)) (z, ξ) (0, J hm hmN z ξ) = -(2 * sqP (z, ξ)) := by
  have h1 := hasDerivAt_fibre_line ((sqP_contDiff (m := m)).differentiable (by simp) (z, ξ))
    (J hm hmN z ξ)
  have h2 : HasDerivAt (fun t : ℝ => sqP (z, ξ + t • J hm hmN z ξ)) (-(2 * sqP (z, ξ))) 0 := by
    have e : (fun t : ℝ => sqP (z, ξ + t • J hm hmN z ξ)) = fun t => (1 - t) ^ 2 * sqP (z, ξ) :=
      funext fun t => sqP_line hm hmN hz ξ t
    rw [e]
    have h4 : HasDerivAt (fun t : ℝ => 1 - t) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
    have h5 := (h4.pow 2).mul_const (sqP (z, ξ))
    convert h5 using 1
    norm_num
  exact h1.unique h2

theorem fderiv_sqF_J (ξ : Fib n N m) :
    fderiv ℝ (sqF (n := n) (N := N) (m := m)) (z, ξ) (0, J hm hmN z ξ) =
      2 * sqN (z, ξ) - 2 * sqP (z, ξ) := by
  have hN := (sqN_contDiff (m := m)).differentiable (by simp) (z, ξ)
  have hP := (sqP_contDiff (m := m)).differentiable (by simp) (z, ξ)
  have h : fderiv ℝ (sqF (n := n) (N := N) (m := m)) (z, ξ) =
      fderiv ℝ sqN (z, ξ) + fderiv ℝ sqP (z, ξ) := (hN.hasFDerivAt.add hP.hasFDerivAt).fderiv
  rw [h, ContinuousLinearMap.add_apply, fderiv_sqN_J hm hmN hz, fderiv_sqP_J hm hmN hz]
  ring

theorem abs_fderiv_sqF_J (ξ : Fib n N m) :
    |fderiv ℝ (sqF (n := n) (N := N) (m := m)) (z, ξ) (0, J hm hmN z ξ)| ≤ 2 * sqF (z, ξ) := by
  rw [fderiv_sqF_J hm hmN hz, abs_le]
  have h1 := sqN_nonneg (z, ξ)
  have h2 := sqP_nonneg (z, ξ)
  unfold sqF
  constructor <;> linarith

theorem fderiv_model_J (ξ : Fib n N m) :
    fderiv ℝ (model (n := n) (N := N) m) (z, ξ) (0, J hm hmN z ξ) = -(2 * sqF (z, ξ)) := by
  have hN := (sqN_contDiff (m := m)).differentiable (by simp) (z, ξ)
  have hP := (sqP_contDiff (m := m)).differentiable (by simp) (z, ξ)
  have h : fderiv ℝ (model (n := n) (N := N) m) (z, ξ) =
      0 - fderiv ℝ sqN (z, ξ) + fderiv ℝ sqP (z, ξ) :=
    (((hasFDerivAt_const ((2 * π * m) ^ 2) (z, ξ)).sub hN.hasFDerivAt).add hP.hasFDerivAt).fderiv
  rw [h, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply, fderiv_sqN_J hm hmN hz, fderiv_sqP_J hm hmN hz]
  unfold sqF
  ring

end Derivs

/-! ### Comparison with the norm -/

theorem exists_uniform_bound_sq {E₀ X : Type*} [NormedAddCommGroup E₀] [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] {K : Set E₀} (hK : IsCompact K) {F : E₀ → X → ℝ}
    (hc : ContinuousOn (fun p : E₀ × X => F p.1 p.2) (K ×ˢ univ))
    (hhom : ∀ z ξ (t : ℝ), F z (t • ξ) = t ^ 2 * F z ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ ξ, F z ξ ≤ C * ‖ξ‖ ^ 2 := by
  have hS : IsCompact (K ×ˢ sphere (0 : X) 1) := hK.prod (isCompact_sphere 0 1)
  obtain ⟨C₀, hC₀⟩ := hS.exists_bound_of_continuousOn (f := fun p : E₀ × X => F p.1 p.2)
    (hc.mono (prod_mono subset_rfl (subset_univ _)))
  refine ⟨max C₀ 0, le_max_right _ _, fun z hz ξ => ?_⟩
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 := hhom z 0 0
    rw [zero_smul] at h0
    rw [h0, norm_zero]
    simp
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hmem : (z, ‖ξ‖⁻¹ • ξ) ∈ K ×ˢ sphere (0 : X) 1 := by
      refine ⟨hz, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have h1 : ‖F z (‖ξ‖⁻¹ • ξ)‖ ≤ C₀ := hC₀ _ hmem
    have h2 := hhom z (‖ξ‖⁻¹ • ξ) ‖ξ‖
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul] at h2
    have h3 : F z (‖ξ‖⁻¹ • ξ) ≤ max C₀ 0 :=
      (le_abs_self _).trans ((Real.norm_eq_abs (F z (‖ξ‖⁻¹ • ξ))).symm.le.trans
        (h1.trans (le_max_left _ _)))
    calc F z ξ = ‖ξ‖ ^ 2 * F z (‖ξ‖⁻¹ • ξ) := h2
      _ ≤ ‖ξ‖ ^ 2 * max C₀ 0 := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = max C₀ 0 * ‖ξ‖ ^ 2 := mul_comm _ _

theorem negP_smul (z : Ambient n × Ambient n) (ξ : Fib n N m) (t : ℝ) :
    negP (z, t • ξ) = t • negP (z, ξ) := by
  unfold negP
  rw [← negV_smul]
  rfl

theorem sqF_hom (z : Ambient n × Ambient n) (ξ : Fib n N m) (t : ℝ) :
    sqF (z, t • ξ) = t ^ 2 * sqF (z, ξ) := by
  unfold sqF sqN sqP
  rw [negP_smul]
  have e : ((t • ξ).2 : ZMod N → Ambient n) - t • negP (z, ξ) =
      t • ((ξ.2 : ZMod N → Ambient n) - negP (z, ξ)) := by
    rw [smul_sub]
    rfl
  change pair (t • negP (z, ξ)) (t • negP (z, ξ)) + ((t * ξ.1.1) ^ 2 + (t * ξ.1.2.1) ^ 2 +
      (t * ξ.1.2.2) ^ 2 + pair (((t • ξ).2 : ZMod N → Ambient n) - t • negP (z, ξ))
        (((t • ξ).2 : ZMod N → Ambient n) - t • negP (z, ξ))) = _
  rw [e, pair_smul_smul, pair_smul_smul]
  ring

theorem sqF_pos {z : Ambient n × Ambient n} (ξ : Fib n N m) (hξ : ξ ≠ 0) : 0 < sqF (z, ξ) := by
  rcases (sqF_nonneg (z, ξ)).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hξ
    have hN := sqN_nonneg (z, ξ)
    have hP := sqP_nonneg (z, ξ)
    unfold sqF at h
    have hN0 : sqN (z, ξ) = 0 := by linarith
    have hP0 : sqP (z, ξ) = 0 := by linarith
    have hA : negP (z, ξ) = 0 := pair_eq_zero hN0
    unfold sqP at hP0
    have hq := pair_self_nonneg ((ξ.2 : ZMod N → Ambient n) - negP (z, ξ))
    have h1 : ξ.1.1 = 0 := by nlinarith [sq_nonneg ξ.1.1, sq_nonneg ξ.1.2.1, sq_nonneg ξ.1.2.2]
    have h2 : ξ.1.2.1 = 0 := by nlinarith [sq_nonneg ξ.1.1, sq_nonneg ξ.1.2.1, sq_nonneg ξ.1.2.2]
    have h3 : ξ.1.2.2 = 0 := by nlinarith [sq_nonneg ξ.1.1, sq_nonneg ξ.1.2.1, sq_nonneg ξ.1.2.2]
    have hq0 : pair ((ξ.2 : ZMod N → Ambient n) - negP (z, ξ))
        ((ξ.2 : ZMod N → Ambient n) - negP (z, ξ)) = 0 := by
      rw [h1, h2, h3] at hP0
      linarith
    have hV := pair_eq_zero hq0
    rw [hA, sub_zero] at hV
    exact Prod.ext (Prod.ext h1 (Prod.ext h2 h3)) (Subtype.ext hV)

/-- **sqF is comparable to the square of the norm on the critical manifold.** -/
theorem exists_sqF_bounds : ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ ∀ z ∈ V2 (n := n), ∀ ξ : Fib n N m,
    c * ‖ξ‖ ^ 2 ≤ sqF (z, ξ) ∧ sqF (z, ξ) ≤ C * ‖ξ‖ ^ 2 := by
  have hc : ContinuousOn (fun p : (Ambient n × Ambient n) × Fib n N m => sqF (p.1, p.2))
      (V2 ×ˢ univ) := (sqF_contDiff (n := n) (N := N) (m := m)).continuous.continuousOn
  obtain ⟨c, hc0, hcb⟩ := exists_uniform_pos (F := fun z ξ => sqF (n := n) (N := N) (m := m) (z, ξ))
    isCompact_V2 hc (fun z ξ t => sqF_hom z ξ t) (fun z _ ξ hξ => sqF_pos ξ hξ)
  obtain ⟨C, hC0, hCb⟩ := exists_uniform_bound_sq
    (F := fun z ξ => sqF (n := n) (N := N) (m := m) (z, ξ)) isCompact_V2 hc
    (fun z ξ t => sqF_hom z ξ t)
  exact ⟨c, C, hc0, hC0, fun z hz ξ => ⟨hcb z hz ξ, hCb z hz ξ⟩⟩

end

end Finsler.RoundModel
