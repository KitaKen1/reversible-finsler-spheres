module

public import Finsler.Geometry.CoordinateEnergyRegularity

/-! Derivative growth of a genuinely C¹ velocity-quadratic density. Unlike
the slit-velocity smoothness criterion, these estimates allow nonzero ambient
velocities to be annihilated by a geometric retraction. -/

@[expose] public section

namespace Finsler.C1QuadraticGrowth

open Finsler.ParametricQuadratic Function Metric
open scoped ContDiff Topology

noncomputable section

variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {f : B × V → ℝ} {U K : Set B}

theorem differential_scale_apply
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hc : ∀ z : B × V, z.1 ∈ U → ContDiffAt ℝ 1 f z)
    {x : B} (hx : x ∈ U) (v : V) (r : ℝ) (hr : r ≠ 0) (a : B × V) :
    fderiv ℝ f (x, r • v) a = r ^ 2 * fderiv ℝ f (x, v) (a.1, r⁻¹ • a.2) := by
  have hl := ((hc (x, r • v) hx).differentiableAt (by norm_num)).hasFDerivAt.comp
    (x, v) (velocityScale r).hasFDerivAt
  have he : (f ∘ velocityScale r) = r ^ 2 • f := by
    funext z
    simpa only [comp_apply, velocityScale_apply, Pi.smul_apply, smul_eq_mul] using hh z.1 r z.2
  rw [he] at hl
  have h := hl.unique (((hc (x, v) hx).differentiableAt (by norm_num)).hasFDerivAt.const_smul (r ^ 2))
  have ha := congrArg (fun L : B × V →L[ℝ] ℝ => L (a.1, r⁻¹ • a.2)) h
  simpa only [ContinuousLinearMap.comp_apply, velocityScale_apply, smul_smul,
    mul_inv_cancel₀ hr, one_smul, Prod.mk.eta, smul_apply, smul_eq_mul] using ha

theorem fderiv_zero
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hc : ∀ z : B × V, z.1 ∈ U → ContDiffAt ℝ 1 f z)
    {x : B} (hx : x ∈ U) : fderiv ℝ f (x, 0) = 0 := by
  have hp (a : B) : fderiv ℝ f (x, 0) (a, 0) = 0 := by
    have h := differential_scale_apply hh hc hx (0 : V) 2 (by norm_num) (a, 0)
    simp only [smul_zero] at h
    norm_num at h
    linarith
  have hv (b : V) : fderiv ℝ f (x, 0) (0, b) = 0 := by
    have h := differential_scale_apply hh hc hx (0 : V) 2 (by norm_num) (0, b)
    simp only [smul_zero] at h
    have he : ((0 : B), (2 : ℝ)⁻¹ • b) = (2 : ℝ)⁻¹ • ((0 : B), b) := by simp
    rw [he, map_smul, smul_eq_mul] at h
    norm_num at h
    linarith
  apply ContinuousLinearMap.ext
  intro a
  change fderiv ℝ f (x, 0) a = 0
  have he : a = (a.1, 0) + (0, a.2) := by simp
  rw [he, map_add, hp, hv, add_zero]

theorem exists_unit_bounds [FiniteDimensional ℝ V] (hK : IsCompact K)
    (hKU : K ⊆ U)
    (hc : ∀ z : B × V, z.1 ∈ U → ContDiffAt ℝ 1 f z) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K ×ˢ Metric.sphere (0 : V) 1,
      ‖f z‖ ≤ C ∧ ‖fderiv ℝ f z‖ ≤ C := by
  have hcont : ContinuousOn (fun z : B × V => ‖f z‖ + ‖fderiv ℝ f z‖)
      (K ×ˢ Metric.sphere (0 : V) 1) := by
    intro z hz
    have h := hc z (hKU hz.1)
    exact (h.continuousAt.norm.add
      (h.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  obtain ⟨C, hb⟩ := (hK.prod (isCompact_sphere (0 : V) 1)).bddAbove_image hcont
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  intro z hz
  have h := (hb ⟨z, hz, rfl⟩).trans (le_max_left C 1)
  constructor <;> nlinarith [norm_nonneg (f z), norm_nonneg (fderiv ℝ f z)]

theorem partial_differential_bounds_on_compact
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hc : ∀ z : B × V, z.1 ∈ U → ContDiffAt ℝ 1 f z)
    (hKU : K ⊆ U) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z ∈ K ×ˢ Metric.sphere (0 : V) 1, ‖fderiv ℝ f z‖ ≤ C)
    {x : B} (hx : x ∈ K) (v : V) :
    ‖(fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inl ℝ B V)‖ ≤ C * ‖v‖ ^ 2 ∧
    ‖(fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inr ℝ B V)‖ ≤ C * ‖v‖ := by
  by_cases hv : v = 0
  · rw [hv, fderiv_zero hh hc (hKU hx)]
    simp
  have hn := norm_ne_zero_iff.mpr hv
  let w : V := ‖v‖⁻¹ • v
  have hw : w ∈ Metric.sphere (0 : V) 1 := by simp [w, norm_smul, inv_mul_cancel₀ hn]
  have he : ‖v‖ • w = v := by simp [w, smul_smul, mul_inv_cancel₀ hn]
  have hb' (a : B × V) : ‖fderiv ℝ f (x, w) a‖ ≤ C * ‖a‖ :=
    ((fderiv ℝ f (x, w)).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (hb (x, w) ⟨hx, hw⟩) (norm_nonneg a))
  constructor
  · apply ((fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inl ℝ B V)).opNorm_le_bound
      (mul_nonneg hC (sq_nonneg _))
    intro a
    have hd := differential_scale_apply hh hc (hKU hx) w ‖v‖ hn (a, 0)
    rw [he] at hd
    change ‖fderiv ℝ f (x, v) (a, 0)‖ ≤ _
    rw [hd, smul_zero, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖v‖ ^ 2 * (C * ‖(a, (0 : V))‖) :=
        mul_le_mul_of_nonneg_left (hb' (a, 0)) (sq_nonneg _)
      _ = (C * ‖v‖ ^ 2) * ‖a‖ := by simp [Prod.norm_def]; ring
  · apply ((fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inr ℝ B V)).opNorm_le_bound
      (mul_nonneg hC (norm_nonneg _))
    intro a
    have hd := differential_scale_apply hh hc (hKU hx) w ‖v‖ hn (0, a)
    rw [he] at hd
    change ‖fderiv ℝ f (x, v) (0, a)‖ ≤ _
    rw [hd, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ‖v‖ ^ 2 * (C * ‖((0 : B), ‖v‖⁻¹ • a)‖) :=
        mul_le_mul_of_nonneg_left (hb' (0, ‖v‖⁻¹ • a)) (sq_nonneg _)
      _ = (C * ‖v‖) * ‖a‖ := by
        simp only [Prod.norm_def, norm_zero, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
        rw [max_eq_right (mul_nonneg (inv_nonneg.mpr (norm_nonneg v)) (norm_nonneg a))]
        field_simp [hn]

theorem exists_partial_bounds_on_compact [FiniteDimensional ℝ V]
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hh : ∀ (x : B) (r : ℝ) (v : V), f (x, r • v) = r ^ 2 * f (x, v))
    (hc : ∀ z : B × V, z.1 ∈ U → ContDiffAt ℝ 1 f z) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ v : V,
      ‖f (x, v)‖ ≤ C * ‖v‖ ^ 2 ∧
      ‖(fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inl ℝ B V)‖ ≤ C * ‖v‖ ^ 2 ∧
      ‖(fderiv ℝ f (x, v)).comp (ContinuousLinearMap.inr ℝ B V)‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC, hb⟩ := exists_unit_bounds hK hKU hc
  refine ⟨C, hC, fun x hx v => ⟨?_, ?_⟩⟩
  · exact quadratic_bound_on_compact hh hC.le (fun z hz => (hb z hz).1) hx v
  · exact partial_differential_bounds_on_compact hh hc hKU hC.le
      (fun z hz => (hb z hz).2) hx v

end

end Finsler.C1QuadraticGrowth
