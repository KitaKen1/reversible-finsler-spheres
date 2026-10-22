module

public import Finsler.Topology.BorelK
public import Finsler.Analysis.IntervalH1CircleAction
public import Finsler.Analysis.IntervalH1Reverse
public import Finsler.Geometry.RoundCoords
public import Finsler.Geometry.PolygonModel
public import Finsler.Analysis.IntervalH1GeodesicCritical

/-! Fourier coefficients of sphere loops.

The m-th cosine and sine coefficients of a loop u are
A_m(u) = 2 ∫₀¹ cos(2πmt) u(t) dt and B_m(u) = 2 ∫₀¹ sin(2πmt) u(t) dt (continuous representative).
They are continuous: they move by at most twice the uniform distance of the loops. The reversal
u ↦ u(1 − t) fixes A_m and changes the sign of B_m; the half rotation multiplies both by (−1)^m.
Riemann sums: with N samples u(k/N), the coefficients differ from the discrete coefficients of
the sample polygon (`RoundCoords.coefA`, `coefB`) by at most 2(2πm/N + ε), where ε bounds the
oscillation of u on intervals of length 1/N. -/

@[expose] public section

namespace Finsler.RoundLoopFourier

open Set Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevReverse
open Finsler.SobolevCircleRepresentative Finsler.SobolevCircleAction Finsler.BorelK
open Finsler.RoundCoords Finsler.Geometry Finsler.PolygonCritical Finsler.PolygonSampling
open Finsler.SobolevCurveVariation
open scoped RealInnerProductSpace Real

noncomputable section

local notation "Circ" => Finsler.SobolevCircleRepresentative.Circle

variable {n : ℕ}

/-- The continuous representative of a loop. -/
abbrev rep (u : SphereLoop n) (t : ℝ) : Ambient n := continuousRepresentative (u.data : Space n) t

theorem rep_continuousOn (u : SphereLoop n) : ContinuousOn (rep u) (Icc 0 1) :=
  continuousRepresentative_continuousOn _

theorem norm_rep (u : SphereLoop n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖rep u t‖ = 1 :=
  u.sphere_constraint ⟨t, ht⟩

theorem rep_eq_circle (u : SphereLoop n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rep u t = (sphereCircleMap u (t : Circ) : Ambient n) := by
  have h := sphereCircleMap_coe u ⟨t, ht⟩
  rw [h]
  rfl

/-- The m-th cosine Fourier coefficient. -/
def cosCoef (m : ℕ) (u : SphereLoop n) : Ambient n :=
  (2 : ℝ) • ∫ t in (0 : ℝ)..1, Real.cos (2 * π * m * t) • rep u t

/-- The m-th sine Fourier coefficient. -/
def sinCoef (m : ℕ) (u : SphereLoop n) : Ambient n :=
  (2 : ℝ) • ∫ t in (0 : ℝ)..1, Real.sin (2 * π * m * t) • rep u t

theorem trig_integrable (f : ℝ → ℝ) (hf : Continuous f) (u : SphereLoop n) (a b : ℝ)
    (hab : uIcc a b ⊆ Icc 0 1) :
    IntervalIntegrable (fun t => f t • rep u t) MeasureTheory.volume a b :=
  ((hf.continuousOn.smul (rep_continuousOn u)).mono hab).intervalIntegrable

/-! ### Continuity -/

/-- The coefficients move by at most twice the uniform distance on [0, 1]. -/
theorem norm_coef_sub_le (f : ℝ → ℝ) (hf : Continuous f) (hf1 : ∀ t, |f t| ≤ 1)
    (u v : SphereLoop n) {r : ℝ} (hr : ∀ t ∈ Icc (0 : ℝ) 1, ‖rep u t - rep v t‖ ≤ r) :
    ‖(2 : ℝ) • (∫ t in (0 : ℝ)..1, f t • rep u t) - (2 : ℝ) • ∫ t in (0 : ℝ)..1, f t • rep v t‖ ≤
      2 * r := by
  have hu := trig_integrable f hf u 0 1 (by rw [uIcc_of_le zero_le_one])
  have hv := trig_integrable f hf v 0 1 (by rw [uIcc_of_le zero_le_one])
  rw [← smul_sub, ← intervalIntegral.integral_sub hu hv, norm_smul, Real.norm_two]
  have hbound : ∀ t ∈ uIoc (0 : ℝ) 1, ‖f t • rep u t - f t • rep v t‖ ≤ r := by
    intro t ht
    rw [uIoc_of_le zero_le_one] at ht
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    calc |f t| * ‖rep u t - rep v t‖ ≤ 1 * r :=
          mul_le_mul (hf1 t) (hr t ⟨ht.1.le, ht.2⟩) (norm_nonneg _) zero_le_one
      _ = r := one_mul r
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_one, mul_one] at h
  linarith

theorem norm_cosCoef_sub_le (m : ℕ) (u v : SphereLoop n) {r : ℝ}
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, ‖rep u t - rep v t‖ ≤ r) :
    ‖cosCoef m u - cosCoef m v‖ ≤ 2 * r :=
  norm_coef_sub_le (fun t => Real.cos (2 * π * m * t)) (by fun_prop)
    (fun t => Real.abs_cos_le_one _) u v hr

theorem norm_sinCoef_sub_le (m : ℕ) (u v : SphereLoop n) {r : ℝ}
    (hr : ∀ t ∈ Icc (0 : ℝ) 1, ‖rep u t - rep v t‖ ≤ r) :
    ‖sinCoef m u - sinCoef m v‖ ≤ 2 * r :=
  norm_coef_sub_le (fun t => Real.sin (2 * π * m * t)) (by fun_prop)
    (fun t => Real.abs_sin_le_one _) u v hr

theorem rep_sub_le_dist (u v : SphereLoop n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖rep u t - rep v t‖ ≤ dist (sphereCircleMap u) (sphereCircleMap v) := by
  rw [rep_eq_circle u ht, rep_eq_circle v ht, ← dist_eq_norm, ← Subtype.dist_eq]
  exact ContinuousMap.dist_apply_le_dist _

theorem continuous_coef (f : ℝ → ℝ) (hf : Continuous f) (hf1 : ∀ t, |f t| ≤ 1) :
    Continuous (fun u : SphereLoop n => (2 : ℝ) • ∫ t in (0 : ℝ)..1, f t • rep u t) := by
  rw [Metric.continuous_iff]
  intro u₀ ε hε
  have hc := (sphereCircleMap_continuous n).continuousAt (x := u₀)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδε⟩ := hc (ε / 4) (by positivity)
  refine ⟨δ, hδ, fun u hu => ?_⟩
  rw [dist_eq_norm]
  have hd := hδε hu
  calc ‖(2 : ℝ) • (∫ t in (0 : ℝ)..1, f t • rep u t) - (2 : ℝ) • ∫ t in (0 : ℝ)..1, f t • rep u₀ t‖
      ≤ 2 * dist (sphereCircleMap u) (sphereCircleMap u₀) :=
        norm_coef_sub_le f hf hf1 u u₀ fun t ht => rep_sub_le_dist u u₀ ht
    _ ≤ 2 * (ε / 4) := by linarith
    _ < ε := by linarith

theorem continuous_cosCoef (m : ℕ) : Continuous (cosCoef (n := n) m) :=
  continuous_coef (fun t => Real.cos (2 * π * m * t)) (by fun_prop)
    (fun t => Real.abs_cos_le_one _)

theorem continuous_sinCoef (m : ℕ) : Continuous (sinCoef (n := n) m) :=
  continuous_coef (fun t => Real.sin (2 * π * m * t)) (by fun_prop)
    (fun t => Real.abs_sin_le_one _)

/-! ### Symmetries -/

theorem cos_two_pi_nat (m : ℕ) : Real.cos (2 * π * m) = 1 := by
  rw [show 2 * π * (m : ℝ) = (m : ℝ) * (2 * π) by ring]
  exact Real.cos_nat_mul_two_pi m

theorem sin_two_pi_nat (m : ℕ) : Real.sin (2 * π * m) = 0 := by
  rw [show 2 * π * (m : ℝ) = ((2 * m : ℕ) : ℝ) * π by push_cast; ring]
  exact Real.sin_nat_mul_pi _

theorem rep_reverse (u : SphereLoop n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rep (reverseSphere u) t = rep u (1 - t) := by
  change continuousRepresentative (reverseData (u.data : Space n)) t = _
  rw [representative_reverseData _ ht]
  rfl

theorem integral_reverse (f : ℝ → ℝ) (u : SphereLoop n) :
    ∫ t in (0 : ℝ)..1, f t • rep (reverseSphere u) t =
      ∫ t in (0 : ℝ)..1, f (1 - t) • rep u t := by
  have h1 : ∫ t in (0 : ℝ)..1, f t • rep (reverseSphere u) t =
      ∫ t in (0 : ℝ)..1, f t • rep u (1 - t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    rw [rep_reverse u ht]
  rw [h1]
  have h2 := intervalIntegral.integral_comp_sub_left
    (fun s => f (1 - s) • rep u s) (1 : ℝ) (a := 0) (b := 1)
  simp only [sub_sub_cancel, sub_zero, sub_self] at h2
  exact h2

/-- The reversal fixes the cosine coefficients. -/
theorem cosCoef_reverse (m : ℕ) (u : SphereLoop n) : cosCoef m (reverseSphere u) = cosCoef m u := by
  unfold cosCoef
  rw [integral_reverse]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  show Real.cos (2 * π * m * (1 - t)) • rep u t = Real.cos (2 * π * m * t) • rep u t
  rw [show 2 * π * m * (1 - t) = 2 * π * m - 2 * π * m * t by ring, Real.cos_sub,
    cos_two_pi_nat, sin_two_pi_nat]
  ring_nf

/-- The reversal changes the sign of the sine coefficients. -/
theorem sinCoef_reverse (m : ℕ) (u : SphereLoop n) :
    sinCoef m (reverseSphere u) = -sinCoef m u := by
  unfold sinCoef
  rw [integral_reverse, ← smul_neg, ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  show Real.sin (2 * π * m * (1 - t)) • rep u t = -(Real.sin (2 * π * m * t) • rep u t)
  rw [show 2 * π * m * (1 - t) = 2 * π * m - 2 * π * m * t by ring, Real.sin_sub,
    cos_two_pi_nat, sin_two_pi_nat, ← neg_smul]
  ring_nf

/-- The circle values of a loop as a periodic function on the line. -/
def circVal (u : SphereLoop n) (s : ℝ) : Ambient n := (sphereCircleMap u (s : Circ) : Ambient n)

theorem circ_periodic (u : SphereLoop n) : Function.Periodic (circVal u) 1 := by
  intro s
  unfold circVal
  rw [AddCircle.coe_add_period]

theorem circ_continuous (u : SphereLoop n) : Continuous (circVal u) :=
  continuous_subtype_val.comp ((sphereCircleMap u).continuous.comp (AddCircle.continuous_mk' 1))

theorem rep_vadd (a : ℝ) (u : SphereLoop n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rep ((a : Circ) +ᵥ u) t = circVal u (t + a) := by
  rw [rep_eq_circle _ ht, sphereCircleMap_vadd]
  unfold circVal
  rw [add_comm t a, AddCircle.coe_add]

theorem integral_circ (f : ℝ → ℝ) (u : SphereLoop n) :
    ∫ t in (0 : ℝ)..1, f t • rep u t = ∫ t in (0 : ℝ)..1, f t • circVal u t := by
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  show f t • rep u t = f t • circVal u t
  rw [rep_eq_circle u ht]
  rfl

theorem cos_sub_half (m : ℕ) (t : ℝ) :
    Real.cos (2 * π * m * (t - 1 / 2)) = (-1 : ℝ) ^ m * Real.cos (2 * π * m * t) := by
  rw [show 2 * π * m * (t - 1 / 2) = 2 * π * m * t - m * π by ring]
  exact Real.cos_sub_nat_mul_pi _ m

theorem sin_sub_half (m : ℕ) (t : ℝ) :
    Real.sin (2 * π * m * (t - 1 / 2)) = (-1 : ℝ) ^ m * Real.sin (2 * π * m * t) := by
  rw [show 2 * π * m * (t - 1 / 2) = 2 * π * m * t - m * π by ring]
  exact Real.sin_sub_nat_mul_pi _ m

/-- The half rotation of an integral against a 1-periodic weight. -/
theorem integral_half (f : ℝ → ℝ) (hf : Continuous f) (hfp : Function.Periodic f 1)
    (u : SphereLoop n) :
    ∫ t in (0 : ℝ)..1, f t • rep (half +ᵥ u) t =
      ∫ t in (0 : ℝ)..1, f (t - 1 / 2) • rep u t := by
  have h1 : ∫ t in (0 : ℝ)..1, f t • rep (half +ᵥ u) t =
      ∫ t in (0 : ℝ)..1, f t • circVal u (t + 1 / 2) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    show f t • rep (half +ᵥ u) t = f t • circVal u (t + 1 / 2)
    rw [show (half : Circ) = (((1 / 2 : ℝ)) : Circ) from rfl, rep_vadd _ u ht]
  rw [h1]
  have h2 := intervalIntegral.integral_comp_add_right
    (fun s => f (s - 1 / 2) • circVal u s) (1 / 2 : ℝ) (a := 0) (b := 1)
  simp only [add_sub_cancel_right] at h2
  rw [h2]
  have hper : Function.Periodic (fun s => f (s - 1 / 2) • circVal u s) 1 := by
    intro s
    show f (s + 1 - 1 / 2) • circVal u (s + 1) = f (s - 1 / 2) • circVal u s
    rw [show s + 1 - 1 / 2 = (s - 1 / 2) + 1 by ring, hfp, circ_periodic u s]
  have h3 := hper.intervalIntegral_add_eq (0 + 1 / 2) 0
  rw [show (0 : ℝ) + 1 / 2 + 1 = 1 + 1 / 2 by ring, zero_add] at h3
  rw [show (0 : ℝ) + 1 / 2 = 1 / 2 by ring, h3, zero_add]
  exact (integral_circ (fun t => f (t - 1 / 2)) u).symm

/-- The half rotation multiplies the cosine coefficients by (−1)^m. -/
theorem cosCoef_half (m : ℕ) (u : SphereLoop n) :
    cosCoef m (half +ᵥ u) = (-1 : ℝ) ^ m • cosCoef m u := by
  have hp : Function.Periodic (fun t : ℝ => Real.cos (2 * π * m * t)) 1 := fun t => by
    show Real.cos (2 * π * m * (t + 1)) = Real.cos (2 * π * m * t)
    rw [show 2 * π * m * (t + 1) = 2 * π * m * t + (m : ℕ) * (2 * π) by ring]
    exact Real.cos_add_nat_mul_two_pi _ m
  have h := integral_half (fun t => Real.cos (2 * π * m * t)) (by fun_prop) hp u
  have h2 : ∫ t in (0 : ℝ)..1, Real.cos (2 * π * m * (t - 1 / 2)) • rep u t =
      (-1 : ℝ) ^ m • ∫ t in (0 : ℝ)..1, Real.cos (2 * π * m * t) • rep u t := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show Real.cos (2 * π * m * (t - 1 / 2)) • rep u t =
      (-1 : ℝ) ^ m • Real.cos (2 * π * m * t) • rep u t
    rw [cos_sub_half, smul_smul]
  unfold cosCoef
  rw [h, h2, smul_comm]

/-- The half rotation multiplies the sine coefficients by (−1)^m. -/
theorem sinCoef_half (m : ℕ) (u : SphereLoop n) :
    sinCoef m (half +ᵥ u) = (-1 : ℝ) ^ m • sinCoef m u := by
  have hp : Function.Periodic (fun t : ℝ => Real.sin (2 * π * m * t)) 1 := fun t => by
    show Real.sin (2 * π * m * (t + 1)) = Real.sin (2 * π * m * t)
    rw [show 2 * π * m * (t + 1) = 2 * π * m * t + (m : ℕ) * (2 * π) by ring]
    exact Real.sin_add_nat_mul_two_pi _ m
  have h := integral_half (fun t => Real.sin (2 * π * m * t)) (by fun_prop) hp u
  have h2 : ∫ t in (0 : ℝ)..1, Real.sin (2 * π * m * (t - 1 / 2)) • rep u t =
      (-1 : ℝ) ^ m • ∫ t in (0 : ℝ)..1, Real.sin (2 * π * m * t) • rep u t := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show Real.sin (2 * π * m * (t - 1 / 2)) • rep u t =
      (-1 : ℝ) ^ m • Real.sin (2 * π * m * t) • rep u t
    rw [sin_sub_half, smul_smul]
  unfold sinCoef
  rw [h, h2, smul_comm]

/-! ### Riemann sums -/

/-- Riemann sums with N samples approximate the integral of w · u for a Lipschitz weight w
bounded by one, up to L/N + ε, where ε bounds the oscillation of u on intervals of length
1/N. -/
theorem norm_riemann_le (w : ℝ → ℝ) (hw : Continuous w) (hw1 : ∀ t, |w t| ≤ 1) {L : ℝ}
    (hwL : ∀ s t, |w t - w s| ≤ L * |t - s|) (N : ℕ) (hN : 0 < N) (u : SphereLoop n) {ε : ℝ}
    (hε : ∀ s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖rep u t - rep u s‖ ≤ ε) :
    ‖(∫ t in (0 : ℝ)..1, w t • rep u t) -
        (1 / N : ℝ) • ∑ k ∈ Finset.range N, w (k / N) • rep u (k / N)‖ ≤ L / N + ε := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set f : ℝ → Ambient n := fun t => w t • rep u t with hf
  set a : ℕ → ℝ := fun k => (k : ℝ) / N with ha
  have hak : ∀ k, k < N → Icc (a k) (a (k + 1)) ⊆ Icc 0 1 := by
    intro k hk t ht
    have h1 : (0 : ℝ) ≤ a k := by rw [ha]; positivity
    have h2 : a (k + 1) ≤ 1 := by
      rw [ha]
      simp only
      rw [div_le_one hNr]
      exact_mod_cast hk
    exact ⟨h1.trans ht.1, ht.2.trans h2⟩
  have hle : ∀ k, a k ≤ a (k + 1) := fun k => by
    rw [ha]
    simp only
    gcongr
    push_cast
    linarith
  have hint : ∀ k < N, IntervalIntegrable f MeasureTheory.volume (a k) (a (k + 1)) := by
    intro k hk
    exact trig_integrable w hw u _ _ (by rw [uIcc_of_le (hle k)]; exact hak k hk)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint
  have ha0 : a 0 = 0 := by rw [ha]; simp
  have haN : a N = 1 := by rw [ha]; simp only; exact div_self hNr.ne'
  rw [ha0, haN] at hsum
  have hconst : ∀ k, (1 / N : ℝ) • f (a k) = ∫ t in (a k)..(a (k + 1)), f (a k) := by
    intro k
    rw [intervalIntegral.integral_const]
    congr 1
    rw [ha]
    push_cast
    field_simp
    ring
  have hdiff : (∫ t in (0 : ℝ)..1, f t) - (1 / N : ℝ) • ∑ k ∈ Finset.range N, f (a k) =
      ∑ k ∈ Finset.range N, ∫ t in (a k)..(a (k + 1)), (f t - f (a k)) := by
    rw [← hsum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hconst k, intervalIntegral.integral_sub (hint k (Finset.mem_range.mp hk))
      intervalIntegrable_const]
  have hbound : ∀ k ∈ Finset.range N,
      ‖∫ t in (a k)..(a (k + 1)), (f t - f (a k))‖ ≤ (L / N + ε) * (1 / N) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hpt : ∀ t ∈ uIoc (a k) (a (k + 1)), ‖f t - f (a k)‖ ≤ L / N + ε := by
      intro t ht
      rw [uIoc_of_le (hle k)] at ht
      have htI : t ∈ Icc (0 : ℝ) 1 := hak k hk' ⟨ht.1.le, ht.2⟩
      have hkI : a k ∈ Icc (0 : ℝ) 1 := hak k hk' ⟨le_rfl, hle k⟩
      have hdist : |t - a k| ≤ 1 / N := by
        have h1 : a (k + 1) - a k = 1 / N := by
          rw [ha]
          push_cast
          field_simp
          ring
        rw [abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2]
      have hsplit : f t - f (a k) = (w t - w (a k)) • rep u t + w (a k) • (rep u t - rep u (a k)) := by
        rw [hf]
        simp only
        rw [sub_smul, smul_sub]
        abel
      rw [hsplit]
      calc ‖(w t - w (a k)) • rep u t + w (a k) • (rep u t - rep u (a k))‖
          ≤ ‖(w t - w (a k)) • rep u t‖ + ‖w (a k) • (rep u t - rep u (a k))‖ := norm_add_le _ _
        _ = |w t - w (a k)| * 1 + |w (a k)| * ‖rep u t - rep u (a k)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, norm_rep u htI]
        _ ≤ L * (1 / N) * 1 + 1 * ε := by
          gcongr
          · exact (hwL _ _).trans (mul_le_mul_of_nonneg_left hdist
              (le_trans (abs_nonneg _) ((hwL (a k) (a k + 1)).trans (by
                rw [show a k + 1 - a k = 1 by ring, abs_one, mul_one])) |>.trans le_rfl))
          · exact hw1 _
          · exact hε _ _ hkI htI hdist
        _ = L / N + ε := by ring
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have hlen : |a (k + 1) - a k| = 1 / N := by
      rw [abs_of_nonneg (by linarith [hle k]), ha]
      push_cast
      field_simp
      ring
    rw [hlen] at h
    exact h
  rw [hdiff]
  calc ‖∑ k ∈ Finset.range N, ∫ t in (a k)..(a (k + 1)), (f t - f (a k))‖
      ≤ ∑ k ∈ Finset.range N, ‖∫ t in (a k)..(a (k + 1)), (f t - f (a k))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, (L / N + ε) * (1 / N) := Finset.sum_le_sum hbound
    _ = L / N + ε := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

/-! ### Comparison with the discrete coefficients of the samples -/

theorem abs_trig_sub_le (f : ℝ → ℝ) (hf : ∀ a b, |f a - f b| ≤ |a - b|) (m : ℕ) (s t : ℝ) :
    |f (2 * π * m * t) - f (2 * π * m * s)| ≤ (2 * π * m) * |t - s| := by
  calc _ ≤ |2 * π * m * t - 2 * π * m * s| := hf _ _
    _ = (2 * π * m) * |t - s| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]

/-- The cosine coefficient of a loop and the discrete cosine coefficient of its samples. -/
theorem norm_cosCoef_sub_coefA_le (m N : ℕ) [NeZero N] (u : SphereLoop n) {ε : ℝ}
    (hε : ∀ s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖rep u t - rep u s‖ ≤ ε) :
    ‖cosCoef m u - coefA m (sampleN N u)‖ ≤ 2 * (2 * π * m / N + ε) := by
  have hN := Nat.pos_of_neZero N
  have hcoef : coefA m (sampleN N u) = (2 : ℝ) • ((1 / N : ℝ) • ∑ k ∈ Finset.range N,
      Real.cos (2 * π * m * (k / N)) • rep u (k / N)) := by
    unfold coefA
    rw [smul_smul, show (2 : ℝ) * (1 / N) = 2 / N by ring]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [sampleN_natCast u (Finset.mem_range.mp hk),
      show 2 * π * m / N * k = 2 * π * m * (k / N) by ring]
  have h := norm_riemann_le (fun t => Real.cos (2 * π * m * t)) (by fun_prop)
    (fun t => Real.abs_cos_le_one _) (abs_trig_sub_le Real.cos Real.abs_cos_sub_cos_le m) N hN u hε
  rw [cosCoef, hcoef, ← smul_sub, norm_smul, Real.norm_two]
  linarith

/-- The sine coefficient of a loop and the discrete sine coefficient of its samples. -/
theorem norm_sinCoef_sub_coefB_le (m N : ℕ) [NeZero N] (u : SphereLoop n) {ε : ℝ}
    (hε : ∀ s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖rep u t - rep u s‖ ≤ ε) :
    ‖sinCoef m u - coefB m (sampleN N u)‖ ≤ 2 * (2 * π * m / N + ε) := by
  have hN := Nat.pos_of_neZero N
  have hcoef : coefB m (sampleN N u) = (2 : ℝ) • ((1 / N : ℝ) • ∑ k ∈ Finset.range N,
      Real.sin (2 * π * m * (k / N)) • rep u (k / N)) := by
    unfold coefB
    rw [smul_smul, show (2 : ℝ) * (1 / N) = 2 / N by ring]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [sampleN_natCast u (Finset.mem_range.mp hk),
      show 2 * π * m / N * k = 2 * π * m * (k / N) by ring]
  have h := norm_riemann_le (fun t => Real.sin (2 * π * m * t)) (by fun_prop)
    (fun t => Real.abs_sin_le_one _) (abs_trig_sub_le Real.sin Real.abs_sin_sub_sin_le m) N hN u hε
  rw [sinCoef, hcoef, ← smul_sub, norm_smul, Real.norm_two]
  linarith

/-! ### Critical loops of the round metric -/

/-- The m-th Fourier coefficients of a tangent critical loop of the round metric with energy
(2πm)² have norm at least 3/4. Fine samples of the loop form a critical polygon, hence a
regular m'-gon whose energy (2πm')² is the energy of the loop, so m' = m; the discrete
coefficients of the samples are the two orthonormal vectors of the plane, and the Riemann sum
estimate transfers them to the loop. -/
theorem coef_ge_of_critical {m : ℕ} (hm : 0 < m) {u : SphereLoop n}
    (hu : TangentCritical (roundMetric n) u)
    (hE : SobolevEnergy.energy (roundMetric n) u = (2 * π * m) ^ 2) :
    3 / 4 ≤ ‖cosCoef m u‖ ∧ 3 / 4 ≤ ‖sinCoef m u‖ := by
  have hπ : 0 < π := Real.pi_pos
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hEpos : 0 < SobolevEnergy.energy (roundMetric n) u := by rw [hE]; positivity
  obtain ⟨g, rfl⟩ :=
    (SobolevGeodesicCritical.tangentCritical_iff_closedGeodesic _ u hEpos).mp hu
  set v := SmoothSobolev.ofSmooth g.loop with hv
  obtain ⟨S⟩ := PolygonModel.exists_segmentData (roundMetric n)
  obtain ⟨N₀, hN₀⟩ := PolygonModel.sample_closedGeodesic S g
  have huc : UniformContinuousOn (rep v) (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (rep_continuousOn v)
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.mp huc (1 / 16) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max (N₀ : ℝ) (1 / δ)) (max (64 * π * m) (2 * m)))
  have hN1 : (N₀ : ℝ) < N := lt_of_le_of_lt (le_max_left _ _ |>.trans (le_max_left _ _)) hN
  have hN2 : 1 / δ < N := lt_of_le_of_lt (le_max_right _ _ |>.trans (le_max_left _ _)) hN
  have hN3 : 64 * π * m < N := lt_of_le_of_lt (le_max_left _ _ |>.trans (le_max_right _ _)) hN
  have hN4 : (2 * m : ℝ) < N := lt_of_le_of_lt (le_max_right _ _ |>.trans (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN3
  have hNnat : 0 < N := by exact_mod_cast hNpos
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨-, hcrit, hpE⟩ := hN₀ N (by exact_mod_cast hN1.le)
  -- oscillation on intervals of length 1/N
  have hosc : ∀ s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖rep v t - rep v s‖ ≤ 1 / 16 := by
    intro s t hs ht hst
    have hlt : dist t s < δ := by
      rw [Real.dist_eq]
      have : 1 / (N : ℝ) < δ := by
        rw [div_lt_iff₀ hNpos]
        rw [div_lt_iff₀ hδ] at hN2
        linarith
      linarith
    have := hδc t ht s hs hlt
    rw [dist_eq_norm] at this
    exact this.le
  -- the samples are a short polygon without antipodal edges
  have hsamp : ∀ i : ZMod N, (samplePoly N v i : Ambient n) = sampleN N v i := fun _ => rfl
  have hna : ∀ i : ZMod N, ⟪(samplePoly N v i : Ambient n), samplePoly N v (i + 1)⟫ ≠ -1 := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k < N ∧ (k : ZMod N) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    rw [hsamp, hsamp, sampleN_natCast v hk, sampleN_natCast_succ v hk] at hi
    have hkN : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by
      rw [div_le_one hNpos]; exact_mod_cast hk.le⟩
    have hk1N : ((k : ℝ) + 1) / N ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by
      rw [div_le_one hNpos]; exact_mod_cast hk⟩
    have hd : ‖rep v (((k : ℝ) + 1) / N) - rep v ((k : ℝ) / N)‖ ≤ 1 / 16 := by
      apply hosc _ _ hkN hk1N
      rw [show ((k : ℝ) + 1) / N - k / N = 1 / N by field_simp; ring,
        abs_of_pos (by positivity)]
    have h1 := norm_rep v hkN
    have h2 := norm_rep v hk1N
    have hsq : ‖rep v (((k : ℝ) + 1) / N) - rep v ((k : ℝ) / N)‖ ^ 2 = 4 := by
      rw [@norm_sub_sq_real, h1, h2, real_inner_comm, hi]
      ring
    nlinarith [norm_nonneg (rep v (((k : ℝ) + 1) / N) - rep v ((k : ℝ) / N))]
  have hEN : polyEnergy (roundMetric n) N (fun i => (samplePoly N v i : Ambient n)) =
      (2 * π * m) ^ 2 := by
    rw [samplePoly_coe, hpE, hE]
  obtain ⟨x, y, m', hx, hy, hxy, hm', hm'N, hq⟩ :=
    RoundPolygon.regular_of_polyCritical hna hcrit (by rw [hEN]; positivity)
  have hreg : sampleN N v = RoundPolygon.regular N m' x y := by
    funext i
    obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k < N ∧ (k : ZMod N) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    rw [← hsamp, hq k, RoundPolygon.regular_natCast]
    rfl
  have hmm : m' = m := by
    have h1 := RoundPolygon.polyEnergy_regular (N := N) hm'N hx hy hxy
    rw [← hreg, ← samplePoly_coe, hEN] at h1
    have h2 : (m : ℝ) = m' := by
      have h3 : (2 * π * m) = 2 * π * m' := (sq_eq_sq₀ (by positivity) (by positivity)).mp h1
      have h4 : (2 * π) * (m : ℝ) = (2 * π) * m' := by linarith
      exact mul_left_cancel₀ (by positivity) h4
    exact_mod_cast h2.symm
  subst hmm
  have hA : coefA m' (sampleN N v) = x := by
    rw [hreg, coefA_regular hm' hm'N hm'N, if_pos rfl]
  have hB : coefB m' (sampleN N v) = y := by
    rw [hreg, coefB_regular hm' hm'N hm'N, if_pos rfl]
  have hsmall : 2 * π * m' / N ≤ 1 / 32 := by
    rw [div_le_iff₀ hNpos]
    linarith
  have hcA := norm_cosCoef_sub_coefA_le m' N v hosc
  have hcB := norm_sinCoef_sub_coefB_le m' N v hosc
  rw [hA] at hcA
  rw [hB] at hcB
  constructor
  · have := norm_sub_norm_le x (x - cosCoef m' v)
    rw [sub_sub_cancel, hx] at this
    have h' : ‖x - cosCoef m' v‖ = ‖cosCoef m' v - x‖ := norm_sub_rev _ _
    linarith
  · have := norm_sub_norm_le y (y - sinCoef m' v)
    rw [sub_sub_cancel, hy] at this
    have h' : ‖y - sinCoef m' v‖ = ‖sinCoef m' v - y‖ := norm_sub_rev _ _
    linarith

/-- The energy of a tangent critical loop of the round metric with positive energy is (2πm)² for
some m ≥ 1. -/
theorem energy_eq_of_critical {u : SphereLoop n} (hu : TangentCritical (roundMetric n) u)
    (hEpos : 0 < SobolevEnergy.energy (roundMetric n) u) :
    ∃ m : ℕ, 0 < m ∧ SobolevEnergy.energy (roundMetric n) u = (2 * π * m) ^ 2 := by
  obtain ⟨g, rfl⟩ :=
    (SobolevGeodesicCritical.tangentCritical_iff_closedGeodesic _ u hEpos).mp hu
  set v := SmoothSobolev.ofSmooth g.loop with hv
  obtain ⟨S⟩ := PolygonModel.exists_segmentData (roundMetric n)
  obtain ⟨N₀, hN₀⟩ := PolygonModel.sample_closedGeodesic S g
  have huc : UniformContinuousOn (rep v) (Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (rep_continuousOn v)
  obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuousOn_iff.mp huc (1 / 16) (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (N₀ : ℝ) (max (1 / δ) 1))
  have hN1 : (N₀ : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN2 : 1 / δ < N := lt_of_le_of_lt (le_max_left _ _ |>.trans (le_max_right _ _)) hN
  have hN3 : (1 : ℝ) < N := lt_of_le_of_lt (le_max_right _ _ |>.trans (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := lt_trans one_pos hN3
  have hNnat : 0 < N := by exact_mod_cast hNpos
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨-, hcrit, hpE⟩ := hN₀ N (by exact_mod_cast hN1.le)
  have hosc : ∀ s t, s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 → |t - s| ≤ 1 / N →
      ‖rep v t - rep v s‖ ≤ 1 / 16 := by
    intro s t hs ht hst
    have hlt : dist t s < δ := by
      rw [Real.dist_eq]
      have : 1 / (N : ℝ) < δ := by
        rw [div_lt_iff₀ hNpos]
        rw [div_lt_iff₀ hδ] at hN2
        linarith
      linarith
    have := hδc t ht s hs hlt
    rw [dist_eq_norm] at this
    exact this.le
  have hsamp : ∀ i : ZMod N, (samplePoly N v i : Ambient n) = sampleN N v i := fun _ => rfl
  have hna : ∀ i : ZMod N, ⟪(samplePoly N v i : Ambient n), samplePoly N v (i + 1)⟫ ≠ -1 := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k < N ∧ (k : ZMod N) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    rw [hsamp, hsamp, sampleN_natCast v hk, sampleN_natCast_succ v hk] at hi
    have hkN : (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by
      rw [div_le_one hNpos]; exact_mod_cast hk.le⟩
    have hk1N : ((k : ℝ) + 1) / N ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by
      rw [div_le_one hNpos]; exact_mod_cast hk⟩
    have hd : ‖rep v (((k : ℝ) + 1) / N) - rep v ((k : ℝ) / N)‖ ≤ 1 / 16 := by
      apply hosc _ _ hkN hk1N
      rw [show ((k : ℝ) + 1) / N - k / N = 1 / N by field_simp; ring,
        abs_of_pos (by positivity)]
    have h1 := norm_rep v hkN
    have h2 := norm_rep v hk1N
    have hsq : ‖rep v (((k : ℝ) + 1) / N) - rep v ((k : ℝ) / N)‖ ^ 2 = 4 := by
      rw [@norm_sub_sq_real, h1, h2, real_inner_comm, hi]
      ring
    nlinarith [norm_nonneg (rep v (((k : ℝ) + 1) / N) - rep v ((k : ℝ) / N))]
  have hEN : polyEnergy (roundMetric n) N (fun i => (samplePoly N v i : Ambient n)) =
      SobolevEnergy.energy (roundMetric n) v := by
    rw [samplePoly_coe, hpE]
  obtain ⟨x, y, m', hx, hy, hxy, hm', hm'N, hq⟩ :=
    RoundPolygon.regular_of_polyCritical hna hcrit (by rw [hEN]; exact hEpos)
  have hreg : sampleN N v = RoundPolygon.regular N m' x y := by
    funext i
    obtain ⟨k, hk, rfl⟩ : ∃ k : ℕ, k < N ∧ (k : ZMod N) = i :=
      ⟨i.val, ZMod.val_lt i, ZMod.natCast_zmod_val i⟩
    rw [← hsamp, hq k, RoundPolygon.regular_natCast]
    rfl
  refine ⟨m', hm', ?_⟩
  have h1 := RoundPolygon.polyEnergy_regular (N := N) hm'N hx hy hxy
  rw [← hreg, ← samplePoly_coe, hEN] at h1
  exact h1

end

end Finsler.RoundLoopFourier
