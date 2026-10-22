module

public import Finsler.Geometry.RoundPolygon
public import Finsler.Geometry.PolygonSmooth
public import Finsler.Geometry.AmbientPenalty
public import Finsler.Analysis.IndexComparison

/-! The second variation of the round polygon energy at the regular m-gons, normal part.

For an ambient polygon Q of unit vectors and an increment w orthogonal to every vertex, the
normalized edge inner products along the line Q + t w are ψ(t²) with
ψ(s) = (c + s σ) / √((1 + s a)(1 + s b)), c = ⟪Q_i, Q_{i+1}⟫, σ = ⟪w_i, w_{i+1}⟫,
a = ‖w_i‖², b = ‖w_{i+1}‖². The energy is therefore a function of t² along such lines, and its
increment divided by t² tends to the s-derivative N Σ G(c_i)(σ_i − c_i (a_i + b_i)/2) at s = 0;
only first derivatives are needed. At a regular m-gon all c_i equal cos θ, θ = 2πm/N, the polygon
energy with normalized vertices is critical in the ambient space (each vertex is invariant under
rescaling and the polygon is critical along curves of sphere polygons), and by the second-order
expansion at a critical point

  D²E(Q)(w, w) = 2 N G(cos θ) (Σ ⟪w_i, w_{i+1}⟫ − cos θ Σ ‖w_i‖²),  G(cos θ) = −2θ / sin θ. -/

@[expose] public section

namespace Finsler.RoundHessian

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundEnergy Finsler.RoundPolygon
open Finsler.PolygonCritical Finsler.PolygonIterate Finsler.PolygonSmooth Finsler.PolygonLoop
open Finsler.EnergySphereSmooth Finsler.SphereRetraction Finsler.AmbientPenalty
open Finsler.IndexComparison
open Finsler.SphereDistance (minEnergy)
open Set Filter
open scoped Topology RealInnerProductSpace Real

noncomputable section

variable {n : ℕ}

/-! ### The normalized inner product along normal lines -/

/-- ψ(s) = (c + s σ) / √((1 + s a)(1 + s b)). -/
def psiN (c σ a b s : ℝ) : ℝ := (c + s * σ) / Real.sqrt ((1 + s * a) * (1 + s * b))

theorem psiN_zero (c σ a b : ℝ) : psiN c σ a b 0 = c := by
  simp [psiN]

theorem psiN_hasDerivAt (c σ a b : ℝ) :
    HasDerivAt (psiN c σ a b) (σ - c * (a + b) / 2) 0 := by
  have hnum : HasDerivAt (fun s : ℝ => c + s * σ) σ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const σ).const_add c
  have h1 : HasDerivAt (fun s : ℝ => 1 + s * a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add 1
  have h2 : HasDerivAt (fun s : ℝ => 1 + s * b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add 1
  have hin : HasDerivAt (fun s : ℝ => (1 + s * a) * (1 + s * b)) (a + b) 0 := by
    have h := h1.mul h2
    convert h using 1
    simp
  have hsq : HasDerivAt (fun s : ℝ => Real.sqrt ((1 + s * a) * (1 + s * b))) ((a + b) / 2) 0 := by
    have h := hin.sqrt (by simp)
    convert h using 1
    simp
  have h := hnum.div hsq (by simp)
  have hval : (σ * Real.sqrt ((1 + 0 * a) * (1 + 0 * b)) - (c + 0 * σ) * ((a + b) / 2)) /
      Real.sqrt ((1 + 0 * a) * (1 + 0 * b)) ^ 2 = σ - c * (a + b) / 2 := by
    simp
    ring
  rw [hval] at h
  exact h

theorem norm_add_smul_sq {P w : Ambient n} (hP : ‖P‖ = 1) (hPw : ⟪P, w⟫ = 0) (t : ℝ) :
    ‖P + t • w‖ ^ 2 = 1 + t ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, hPw, norm_smul, hP, Real.norm_eq_abs, mul_pow,
    sq_abs]
  ring

theorem add_smul_ne_zero {P w : Ambient n} (hP : ‖P‖ = 1) (hPw : ⟪P, w⟫ = 0) (t : ℝ) :
    P + t • w ≠ 0 := by
  intro h
  have h1 := norm_add_smul_sq hP hPw t
  rw [h, norm_zero] at h1
  nlinarith [sq_nonneg t, sq_nonneg ‖w‖, mul_nonneg (sq_nonneg t) (sq_nonneg ‖w‖)]

/-- Along normal lines the normalized edge inner products are ψ(t²). -/
theorem inner_normalize_normal {P P' w w' : Ambient n} (hP : ‖P‖ = 1) (hP' : ‖P'‖ = 1)
    (hPw : ⟪P, w⟫ = 0) (hP'w' : ⟪P', w'⟫ = 0) (hPw' : ⟪P, w'⟫ = 0) (hP'w : ⟪P', w⟫ = 0)
    (t : ℝ) :
    ⟪((normalize (P + t • w) : Sphere n) : Ambient n), (normalize (P' + t • w') : Ambient n)⟫ =
      psiN ⟪P, P'⟫ ⟪w, w'⟫ (‖w‖ ^ 2) (‖w'‖ ^ 2) (t ^ 2) := by
  rw [coe_normalize (add_smul_ne_zero hP hPw t), coe_normalize (add_smul_ne_zero hP' hP'w' t),
    real_inner_smul_left, real_inner_smul_right]
  have hinner : ⟪P + t • w, P' + t • w'⟫ = ⟪P, P'⟫ + t ^ 2 * ⟪w, w'⟫ := by
    have hwP' : ⟪w, P'⟫ = 0 := by rw [real_inner_comm, hP'w]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hPw', hwP']
    ring
  have hn1 : ‖P + t • w‖ = Real.sqrt (1 + t ^ 2 * ‖w‖ ^ 2) := by
    rw [← norm_add_smul_sq hP hPw t, Real.sqrt_sq (norm_nonneg _)]
  have hn2 : ‖P' + t • w'‖ = Real.sqrt (1 + t ^ 2 * ‖w'‖ ^ 2) := by
    rw [← norm_add_smul_sq hP' hP'w' t, Real.sqrt_sq (norm_nonneg _)]
  rw [hinner, hn1, hn2, psiN, Real.sqrt_mul (by positivity)]
  field_simp

/-! ### The energy along normal lines -/

/-- The round polygon energy with normalized vertices in terms of normalized inner products. -/
theorem polyEnergyN_round {N : ℕ} [NeZero N] (Q : ZMod N → Ambient n)
    (hna : ∀ i : ZMod N, ⟪((normalize (Q i) : Sphere n) : Ambient n),
      (normalize (Q (i + 1)) : Ambient n)⟫ ≠ -1) :
    polyEnergyN (roundMetric n) N Q = N * ∑ i : ZMod N,
      ang2 ⟪((normalize (Q i) : Sphere n) : Ambient n), (normalize (Q (i + 1)) : Ambient n)⟫ := by
  unfold polyEnergyN
  rw [sum_univ_eq_sum_range (fun i : ZMod N => ang2 ⟪((normalize (Q i) : Sphere n) : Ambient n),
    (normalize (Q (i + 1)) : Ambient n)⟫)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold ambientMinEnergy
  exact minEnergy_round (mem_sphere_zero_iff_norm.mp (normalize _).2)
    (mem_sphere_zero_iff_norm.mp (normalize _).2) (hna _)

/-- The increment of the energy along a normal line divided by t². -/
theorem tendsto_normal {N : ℕ} [NeZero N] {Q w : ZMod N → Ambient n} (hQ : ∀ i, ‖Q i‖ = 1)
    (hperp : ∀ i j, ⟪Q i, w j⟫ = 0) (hc0 : ∀ i, ⟪Q i, Q (i + 1)⟫ ≠ -1)
    (hc1 : ∀ i, ⟪Q i, Q (i + 1)⟫ ≠ 1) :
    Tendsto (fun t : ℝ => (polyEnergyN (roundMetric n) N (Q + t • w) -
        polyEnergyN (roundMetric n) N Q) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (N * ∑ i : ZMod N, G ⟪Q i, Q (i + 1)⟫ *
        (⟪w i, w (i + 1)⟫ - ⟪Q i, Q (i + 1)⟫ * (‖w i‖ ^ 2 + ‖w (i + 1)‖ ^ 2) / 2))) := by
  set c : ZMod N → ℝ := fun i => ⟪Q i, Q (i + 1)⟫ with hcdef
  set ψ : ZMod N → ℝ → ℝ := fun i => psiN (c i) ⟪w i, w (i + 1)⟫ (‖w i‖ ^ 2) (‖w (i + 1)‖ ^ 2)
    with hψdef
  set Ψ : ℝ → ℝ := fun s => N * ∑ i : ZMod N, ang2 (ψ i s) with hΨdef
  have hψ0 : ∀ i, ψ i 0 = c i := fun i => psiN_zero _ _ _ _
  have hΨd : HasDerivAt Ψ (N * ∑ i : ZMod N, G (c i) *
      (⟪w i, w (i + 1)⟫ - c i * (‖w i‖ ^ 2 + ‖w (i + 1)‖ ^ 2) / 2)) 0 := by
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro i _
    have ha : HasDerivAt ang2 (G (c i)) (ψ i 0) := by
      rw [hψ0]
      exact ang2_hasDerivAt (hc0 i) (hc1 i)
    exact ha.comp 0 (psiN_hasDerivAt _ _ _ _)
  -- the energy along the line is Ψ(t²) near t = 0
  have hcont : ∀ i, ContinuousAt (ψ i) 0 := fun i => (psiN_hasDerivAt _ _ _ _).continuousAt
  have hz : ∀ i : ZMod N, ψ i ((0 : ℝ) ^ 2) ≠ -1 := by
    intro i
    rw [show ((0 : ℝ)) ^ 2 = 0 by norm_num, hψ0]
    exact hc0 i
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : ZMod N, ψ i (t ^ 2) ≠ -1 := by
    rw [eventually_all]
    intro i
    have h2 : ContinuousAt (fun t : ℝ => ψ i (t ^ 2)) 0 :=
      ContinuousAt.comp_of_eq (hcont i) (continuous_pow 2).continuousAt (by norm_num)
    exact h2.eventually_ne (hz i)
  have hline : ∀ t : ℝ, (∀ i : ZMod N, ψ i (t ^ 2) ≠ -1) →
      polyEnergyN (roundMetric n) N (Q + t • w) = Ψ (t ^ 2) := by
    intro t ht
    have heq : ∀ i : ZMod N, ⟪((normalize ((Q + t • w) i) : Sphere n) : Ambient n),
        (normalize ((Q + t • w) (i + 1)) : Ambient n)⟫ = ψ i (t ^ 2) := by
      intro i
      simp only [Pi.add_apply, Pi.smul_apply]
      exact inner_normalize_normal (hQ i) (hQ (i + 1)) (hperp i i) (hperp (i + 1) (i + 1))
        (hperp i (i + 1)) (hperp (i + 1) i) t
    rw [polyEnergyN_round _ (fun i => by rw [heq]; exact ht i)]
    simp only [hΨdef, heq]
  have hQ0 : polyEnergyN (roundMetric n) N Q = Ψ 0 := by
    have h := hline 0 hz
    rw [zero_smul, add_zero, show ((0 : ℝ)) ^ 2 = 0 by norm_num] at h
    exact h
  -- the slope of Ψ at 0 along s = t²
  have hslope := hΨd.tendsto_slope_zero
  have hsq : Tendsto (fun t : ℝ => t ^ 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun t : ℝ => t ^ 2) (𝓝 0) (𝓝 0) := by
        simpa using ((continuous_pow 2).tendsto (0 : ℝ))
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact pow_ne_zero 2 ht
  have hcomp := hslope.comp hsq
  have hfinal : (fun t : ℝ => (polyEnergyN (roundMetric n) N (Q + t • w) -
      polyEnergyN (roundMetric n) N Q) / t ^ 2) =ᶠ[𝓝[≠] 0]
      ((fun s : ℝ => s⁻¹ • (Ψ (0 + s) - Ψ 0)) ∘ fun t : ℝ => t ^ 2) := by
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with t ht
    simp only [Function.comp_apply, zero_add, smul_eq_mul]
    rw [hline t ht, hQ0]
    ring
  exact hcomp.congr' hfinal.symm

/-! ### Ambient criticality of the regular polygons -/

/-- The derivative of the normalized line t ↦ normalize(P + t V) at a unit vector P. -/
theorem hasDerivAt_normalize_line {P V : Ambient n} (hP : ‖P‖ = 1) :
    HasDerivAt (fun t : ℝ => ((normalize (P + t • V) : Sphere n) : Ambient n))
      (V - ⟪P, V⟫ • P) 0 := by
  have hl : HasDerivAt (fun t : ℝ => P + t • V) V 0 := hasDerivAt_line P V
  have hg : HasDerivAt (fun t : ℝ => ‖P + t • V‖ ^ 2) (2 * ⟪P, V⟫) 0 := by
    have h := hl.norm_sq
    simpa using h
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (‖P + t • V‖ ^ 2)) ⟪P, V⟫ 0 := by
    have h := hg.sqrt (by simp [hP])
    convert h using 1
    simp [hP]
  have hn : (fun t : ℝ => Real.sqrt (‖P + t • V‖ ^ 2)) = fun t => ‖P + t • V‖ :=
    funext fun t => Real.sqrt_sq (norm_nonneg _)
  rw [hn] at hs
  have hi : HasDerivAt (fun t : ℝ => ‖P + t • V‖⁻¹) (-⟪P, V⟫) 0 := by
    have h := hs.inv (by simp [hP])
    convert h using 1
    simp [hP]
  have hm := hi.smul hl
  have hval : ‖P + (0 : ℝ) • V‖⁻¹ • V + (-⟪P, V⟫) • (P + (0 : ℝ) • V) = V - ⟪P, V⟫ • P := by
    simp [hP, sub_eq_add_neg]
  rw [hval] at hm
  have hne : ∀ᶠ t in 𝓝 (0 : ℝ), P + t • V ≠ 0 := by
    have hc : ContinuousAt (fun t : ℝ => P + t • V) 0 := hl.continuousAt
    have h0 : (fun t : ℝ => P + t • V) 0 ≠ 0 := by
      intro h
      simp only [zero_smul, add_zero] at h
      rw [h, norm_zero] at hP
      exact zero_ne_one hP
    exact hc.eventually_ne h0
  refine hm.congr_of_eventuallyEq ?_
  filter_upwards [hne] with t ht
  exact coe_normalize ht

/-- A regular m-gon is critical for the polygon energy with normalized vertices. -/
theorem fderiv_regular_eq_zero {N : ℕ} [NeZero N] {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N)
    {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    (hdiff : DifferentiableAt ℝ (polyEnergyN (roundMetric n) N) (regular N m x u)) :
    fderiv ℝ (polyEnergyN (roundMetric n) N) (regular N m x u) = 0 := by
  set Q := regular N m x u with hQdef
  have hQ : ∀ i, ‖Q i‖ = 1 := norm_regular hx hu hxu
  let q : ZMod N → Sphere n := fun i => ⟨Q i, mem_sphere_zero_iff_norm.mpr (hQ i)⟩
  have hcrit : PolyCritical (roundMetric n) N q :=
    polyCritical_regular hm hmN hx hu hxu (fun i => rfl)
  ext V
  change fderiv ℝ (polyEnergyN (roundMetric n) N) Q V = 0
  set c : ℝ → ZMod N → Ambient n := fun t i => ((normalize (Q i + t • V i) : Sphere n) : Ambient n)
    with hcdef
  have hc0 : c 0 = fun i => (q i : Ambient n) := by
    funext i
    simp only [hcdef, zero_smul, add_zero]
    exact coe_normalize_of_norm (hQ i)
  have hcn : ∀ r i, ‖c r i‖ = 1 := fun r i => mem_sphere_zero_iff_norm.mp (normalize _).2
  have hcd : HasDerivAt c (fun i => V i - ⟪Q i, V i⟫ • Q i) 0 := by
    rw [hasDerivAt_pi]
    intro i
    exact hasDerivAt_normalize_line (hQ i)
  have h1 := hcrit c _ hc0 hcn hcd
  have h2 : HasDerivAt (fun t : ℝ => polyEnergyN (roundMetric n) N (Q + t • V))
      (fderiv ℝ (polyEnergyN (roundMetric n) N) Q V) 0 := by
    have hl : HasDerivAt (fun t : ℝ => Q + t • V) V 0 := hasDerivAt_line Q V
    have hd : HasFDerivAt (polyEnergyN (roundMetric n) N)
        (fderiv ℝ (polyEnergyN (roundMetric n) N) Q) ((fun t : ℝ => Q + t • V) 0) := by
      simpa using hdiff.hasFDerivAt
    exact hd.comp_hasDerivAt 0 hl
  have heq : (fun t : ℝ => polyEnergyN (roundMetric n) N (Q + t • V)) =
      fun r => polyEnergy (roundMetric n) N (c r) := by
    funext t
    rw [polyEnergyN_eq_normalize]
    rfl
  rw [heq] at h2
  exact h2.unique h1

/-! ### The normal second variation at the regular polygons -/

theorem sum_shift_norm {N : ℕ} [NeZero N] (w : ZMod N → Ambient n) :
    ∑ i : ZMod N, ‖w (i + 1)‖ ^ 2 = ∑ i : ZMod N, ‖w i‖ ^ 2 :=
  Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) (fun i => ‖w i‖ ^ 2)

/-- The second variation of the round polygon energy at a regular m-gon in a direction normal
to its plane. -/
theorem hessian_normal {N : ℕ} [NeZero N] {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N)
    {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    (hC2 : ContDiffAt ℝ 2 (polyEnergyN (roundMetric n) N) (regular N m x u))
    (w : ZMod N → Ambient n) (hwx : ∀ i, ⟪x, w i⟫ = 0) (hwu : ∀ i, ⟪u, w i⟫ = 0) :
    fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) (regular N m x u) w w =
      2 * (N * G (Real.cos (2 * π * m / N)) *
        (∑ i : ZMod N, ⟪w i, w (i + 1)⟫ - Real.cos (2 * π * m / N) * ∑ i : ZMod N, ‖w i‖ ^ 2)) := by
  set Q := regular N m x u with hQdef
  set θ := 2 * π * m / N with hθ
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hπ : 0 < π := Real.pi_pos
  have hθ0 : 0 < θ := by
    rw [hθ]
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hθπ : θ < π := by
    rw [hθ, div_lt_iff₀ hN]
    have : (2 * m : ℝ) < N := by exact_mod_cast hmN
    nlinarith
  have hcθ0 : -1 < Real.cos θ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ0.le le_rfl hθπ
    rw [Real.cos_pi] at h
    exact h
  have hcθ1 : Real.cos θ < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
    rw [Real.cos_zero] at h
    exact h
  have hQ : ∀ i, ‖Q i‖ = 1 := norm_regular hx hu hxu
  have hinner : ∀ i, ⟪Q i, Q (i + 1)⟫ = Real.cos θ := inner_regular hx hu hxu
  have hperp : ∀ i j, ⟪Q i, w j⟫ = 0 := by
    intro i j
    rw [hQdef, regular, circ, inner_add_left, real_inner_smul_left, real_inner_smul_left, hwx, hwu]
    ring
  have hT := tendsto_normal hQ hperp (fun i => by rw [hinner]; exact ne_of_gt hcθ0)
    (fun i => by rw [hinner]; exact ne_of_lt hcθ1)
  have hcrit := fderiv_regular_eq_zero hm hmN hx hu hxu (hC2.differentiableAt (by norm_num))
  have hT2 := tendsto_div_sq hC2 hcrit (hasDerivAt_line Q w) (by simp)
  have huniq := tendsto_nhds_unique hT2 hT
  simp only [hinner] at huniq
  have hsum : ∑ i : ZMod N, G (Real.cos θ) *
      (⟪w i, w (i + 1)⟫ - Real.cos θ * (‖w i‖ ^ 2 + ‖w (i + 1)‖ ^ 2) / 2) =
      G (Real.cos θ) * (∑ i : ZMod N, ⟪w i, w (i + 1)⟫ - Real.cos θ * ∑ i : ZMod N, ‖w i‖ ^ 2) := by
    rw [← Finset.mul_sum]
    congr 1
    have h1 : ∀ i : ZMod N, ⟪w i, w (i + 1)⟫ - Real.cos θ * (‖w i‖ ^ 2 + ‖w (i + 1)‖ ^ 2) / 2 =
        ⟪w i, w (i + 1)⟫ - Real.cos θ / 2 * ‖w i‖ ^ 2 - Real.cos θ / 2 * ‖w (i + 1)‖ ^ 2 := by
      intro i
      ring
    simp only [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_shift_norm]
    ring
  rw [hsum] at huniq
  linarith

/-! ### The in-plane second variation -/

theorem circ_add (x u : Ambient n) (φ α : ℝ) :
    circ x u (φ + α) = Real.cos α • circ x u φ + Real.sin α • circ x u (φ + π / 2) := by
  have hc : Real.cos (φ + π / 2) = -Real.sin φ := by
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hs : Real.sin (φ + π / 2) = Real.cos φ := by
    rw [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  simp only [circ]
  rw [hc, hs, Real.cos_add, Real.sin_add]
  module

/-- Normalizing a step along the tangent of a great circle moves along the circle. -/
theorem normalize_inplane {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    (φ s : ℝ) :
    ((normalize (circ x u φ + s • circ x u (φ + π / 2)) : Sphere n) : Ambient n) =
      circ x u (φ + Real.arctan s) := by
  have h1 : ‖circ x u φ‖ = 1 := norm_cos_sin hx hu hxu φ
  have h2 : ‖circ x u (φ + π / 2)‖ = 1 := norm_cos_sin hx hu hxu _
  have h12 : ⟪circ x u φ, circ x u (φ + π / 2)⟫ = 0 := by
    rw [inner_circ hx hu hxu, show φ + π / 2 - φ = π / 2 by ring, Real.cos_pi_div_two]
  have hn2 : ‖circ x u φ + s • circ x u (φ + π / 2)‖ ^ 2 = 1 + s ^ 2 := by
    have h := norm_sq_comb h1 h2 h12 1 s
    rw [one_smul] at h
    rw [h]
    ring
  have hpos : 0 < 1 + s ^ 2 := by positivity
  have hn : ‖circ x u φ + s • circ x u (φ + π / 2)‖ = Real.sqrt (1 + s ^ 2) := by
    rw [← hn2, Real.sqrt_sq (norm_nonneg _)]
  have hne : circ x u φ + s • circ x u (φ + π / 2) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    have := Real.sqrt_pos.mpr hpos
    linarith
  rw [coe_normalize hne, hn]
  conv_rhs => rw [circ_add]
  rw [Real.cos_arctan, Real.sin_arctan, smul_add, smul_smul, one_div]
  congr 2
  ring

/-- The unit tangents of a regular polygon. -/
def tang (N m : ℕ) (x u : Ambient n) (i : ZMod N) : Ambient n :=
  circ x u (2 * π * m / N * i.val + π / 2)

theorem tang_natCast {N : ℕ} [NeZero N] (m : ℕ) (x u : Ambient n) (k : ℕ) :
    tang N m x u (k : ZMod N) = circ x u (2 * π * m / N * k + π / 2) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  rw [tang, ZMod.val_natCast]
  have hk : (k : ℝ) = ((k % N : ℕ) : ℝ) + N * ((k / N : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mod_add_div k N).symm
  have h : 2 * π * m / N * k + π / 2 = (2 * π * m / N * ((k % N : ℕ) : ℝ) + π / 2) +
      ((m * (k / N) : ℕ) : ℝ) * (2 * π) := by
    rw [hk]
    push_cast
    field_simp
    ring
  rw [h, circ_add_two_pi]

/-- Along in-plane lines the energy of a regular polygon is N Σ (θ + Δ_i)². -/
theorem polyEnergyN_inplane {N : ℕ} [NeZero N] {m : ℕ} {x u : Ambient n} (hx : ‖x‖ = 1)
    (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0) (β : ZMod N → ℝ) (t : ℝ)
    (hsmall : ∀ i : ZMod N, 0 ≤ 2 * π * m / N + (Real.arctan (t * β (i + 1)) -
        Real.arctan (t * β i)) ∧
      2 * π * m / N + (Real.arctan (t * β (i + 1)) - Real.arctan (t * β i)) < π) :
    polyEnergyN (roundMetric n) N (regular N m x u + t • fun i => β i • tang N m x u i) =
      N * ∑ i : ZMod N, (2 * π * m / N + (Real.arctan (t * β (i + 1)) -
        Real.arctan (t * β i))) ^ 2 := by
  set θ := 2 * π * m / N with hθ
  have hvert : ∀ k : ℕ, ((normalize ((regular N m x u + t • fun i => β i • tang N m x u i)
      (k : ZMod N)) : Sphere n) : Ambient n) = circ x u (θ * k + Real.arctan (t * β k)) := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_smul]
    rw [regular_natCast, tang_natCast]
    exact normalize_inplane hx hu hxu _ _
  have hinner : ∀ i : ZMod N, ⟪((normalize ((regular N m x u + t • fun i => β i • tang N m x u i)
      i) : Sphere n) : Ambient n), (normalize ((regular N m x u + t • fun i => β i •
        tang N m x u i) (i + 1)) : Ambient n)⟫ =
      Real.cos (θ + (Real.arctan (t * β (i + 1)) - Real.arctan (t * β i))) := by
    intro i
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ZMod N) = i := ⟨i.val, ZMod.natCast_zmod_val i⟩
    have hk1 : (k : ZMod N) + 1 = ((k + 1 : ℕ) : ZMod N) := by push_cast; rfl
    rw [hk1, hvert, hvert, inner_circ hx hu hxu]
    congr 1
    push_cast
    ring
  have hna : ∀ i : ZMod N, ⟪((normalize ((regular N m x u + t • fun i => β i • tang N m x u i)
      i) : Sphere n) : Ambient n), (normalize ((regular N m x u + t • fun i => β i •
        tang N m x u i) (i + 1)) : Ambient n)⟫ ≠ -1 := by
    intro i
    rw [hinner]
    intro h
    obtain ⟨h0, hπ⟩ := hsmall i
    have h' := Real.arccos_cos h0 hπ.le
    rw [h, Real.arccos_neg_one] at h'
    linarith
  rw [polyEnergyN_round _ hna]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hinner, ang2, Real.arccos_cos (hsmall i).1 (hsmall i).2.le]

theorem tendsto_arctan_div (b : ℝ) :
    Tendsto (fun t : ℝ => Real.arctan (t * b) / t) (𝓝[≠] 0) (𝓝 b) := by
  have h : HasDerivAt (fun t : ℝ => Real.arctan (t * b)) b 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t * b) b 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const b
    have h2 := (Real.hasDerivAt_arctan ((fun t : ℝ => t * b) 0)).comp 0 h1
    have hv : 1 / (1 + ((fun t : ℝ => t * b) 0) ^ 2) * b = b := by simp
    rw [hv] at h2
    exact h2
  have hs := h.tendsto_slope_zero
  refine hs.congr' ?_
  filter_upwards with t
  simp [Real.arctan_zero, div_eq_inv_mul]

/-- The in-plane second variation: 2N Σ (β_{i+1} − β_i)². -/
theorem hessian_inplane {N : ℕ} [NeZero N] {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N)
    {x u : Ambient n} (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0)
    (hC2 : ContDiffAt ℝ 2 (polyEnergyN (roundMetric n) N) (regular N m x u)) (β : ZMod N → ℝ) :
    fderiv ℝ (fderiv ℝ (polyEnergyN (roundMetric n) N)) (regular N m x u)
        (fun i => β i • tang N m x u i) (fun i => β i • tang N m x u i) =
      2 * (N * ∑ i : ZMod N, (β (i + 1) - β i) ^ 2) := by
  set θ := 2 * π * m / N with hθ
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have hπ : 0 < π := Real.pi_pos
  have hθ0 : 0 < θ := by
    rw [hθ]
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hθπ : θ < π := by
    rw [hθ, div_lt_iff₀ hN]
    have : (2 * m : ℝ) < N := by exact_mod_cast hmN
    nlinarith
  set V : ZMod N → Ambient n := fun i => β i • tang N m x u i with hV
  set Δ : ZMod N → ℝ → ℝ := fun i t => Real.arctan (t * β (i + 1)) - Real.arctan (t * β i)
    with hΔ
  -- Δ is small near 0
  have hΔc : ∀ i, ContinuousAt (Δ i) 0 := fun i => by
    apply ContinuousAt.sub <;> exact (Real.continuous_arctan.comp
      (continuous_id.mul continuous_const)).continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i : ZMod N, 0 ≤ θ + Δ i t ∧ θ + Δ i t < π := by
    rw [eventually_all]
    intro i
    have h0 : Δ i 0 = 0 := by simp [hΔ, Real.arctan_zero]
    have hlo : ∀ᶠ t in 𝓝 (0 : ℝ), -θ < Δ i t := by
      have := (hΔc i).eventually (lt_mem_nhds (show -θ < Δ i 0 by rw [h0]; linarith))
      exact this
    have hhi : ∀ᶠ t in 𝓝 (0 : ℝ), Δ i t < π - θ := by
      have := (hΔc i).eventually (gt_mem_nhds (show Δ i 0 < π - θ by rw [h0]; linarith))
      exact this
    filter_upwards [hlo, hhi] with t h1 h2
    constructor <;> linarith
  have hE : ∀ t : ℝ, (∀ i : ZMod N, 0 ≤ θ + Δ i t ∧ θ + Δ i t < π) →
      polyEnergyN (roundMetric n) N (regular N m x u + t • V) = N * ∑ i : ZMod N, (θ + Δ i t) ^ 2 :=
    fun t ht => polyEnergyN_inplane hx hu hxu β t ht
  have hsum0 : ∀ t : ℝ, ∑ i : ZMod N, Δ i t = 0 := by
    intro t
    simp only [hΔ, Finset.sum_sub_distrib]
    have h := Equiv.sum_comp (Equiv.addRight (1 : ZMod N)) (fun i => Real.arctan (t * β i))
    simp only [Equiv.coe_addRight] at h
    rw [h]
    ring
  have hE0 : polyEnergyN (roundMetric n) N (regular N m x u) = N * ∑ i : ZMod N, θ ^ 2 := by
    have h := hE 0 (fun i => by simp [hΔ, Real.arctan_zero]; exact ⟨hθ0.le, hθπ⟩)
    simp only [zero_smul, add_zero, hΔ, zero_mul, Real.arctan_zero, sub_self] at h
    exact h
  have hdiff : ∀ t : ℝ, (∀ i : ZMod N, 0 ≤ θ + Δ i t ∧ θ + Δ i t < π) →
      polyEnergyN (roundMetric n) N (regular N m x u + t • V) -
        polyEnergyN (roundMetric n) N (regular N m x u) = N * ∑ i : ZMod N, Δ i t ^ 2 := by
    intro t ht
    rw [hE t ht, hE0, ← mul_sub, ← Finset.sum_sub_distrib]
    have h : ∑ i : ZMod N, ((θ + Δ i t) ^ 2 - θ ^ 2) =
        2 * θ * ∑ i : ZMod N, Δ i t + ∑ i : ZMod N, Δ i t ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h, hsum0, mul_zero, zero_add]
  have hlim : Tendsto (fun t : ℝ => N * ∑ i : ZMod N, (Δ i t / t) ^ 2) (𝓝[≠] 0)
      (𝓝 (N * ∑ i : ZMod N, (β (i + 1) - β i) ^ 2)) := by
    apply Tendsto.const_mul
    apply tendsto_finsetSum
    intro i _
    have h := (tendsto_arctan_div (β (i + 1))).sub (tendsto_arctan_div (β i))
    have h' : Tendsto (fun t : ℝ => Δ i t / t) (𝓝[≠] 0) (𝓝 (β (i + 1) - β i)) := by
      refine h.congr' ?_
      filter_upwards with t
      simp only [hΔ, sub_div]
    exact h'.pow 2
  have hT : Tendsto (fun t : ℝ => (polyEnergyN (roundMetric n) N (regular N m x u + t • V) -
      polyEnergyN (roundMetric n) N (regular N m x u)) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (N * ∑ i : ZMod N, (β (i + 1) - β i) ^ 2)) := by
    refine hlim.congr' ?_
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht ht0
    rw [hdiff t ht, mul_div_assoc, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow]
  have hcrit := fderiv_regular_eq_zero hm hmN hx hu hxu (hC2.differentiableAt (by norm_num))
  have hT2 := tendsto_div_sq hC2 hcrit (hasDerivAt_line (regular N m x u) V) (by simp)
  have huniq := tendsto_nhds_unique hT2 hT
  linarith

end

end Finsler.RoundHessian
