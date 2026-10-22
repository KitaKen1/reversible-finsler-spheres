module

public import Finsler.Analysis.IntervalH1CurveFamily

/-! Realization of every periodic tangent field by an actual H¹ sphere curve. The H¹
distance between the rational sphere curve through u in direction h and the straight
line u + r h is O(r²): pointwise the value error is O(r²) uniformly and the velocity
error is O(r²) times the velocities, so both L² norms are O(r²). Hence the curve has
derivative h at r = 0, and tangent criticality is equivalent to stationarity of the
actual energy along every actual H¹ sphere curve. All norm manipulations are done in
generic lemmas over arbitrary graph elements, so no rewriting happens under the
nonlinear curve. No chart or normalization is used. -/

@[expose] public section

namespace Finsler.SobolevCurveRealization

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.SobolevTangent
open Finsler.SobolevCurveVariation Finsler.RationalSphereCurve Finsler.SobolevCurveFamily
open MeasureTheory Set Filter Asymptotics
open scoped Topology RealInnerProductSpace ENNReal NNReal

noncomputable section

set_option maxHeartbeats 400000

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

theorem value_comb (a b c : Space n) (r : ℝ) :
    value (a - b - r • c) = value a - value b - r • value c := by
  change valueL n (a - b - r • c) = valueL n a - valueL n b - r • valueL n c
  rw [(valueL n).map_sub, (valueL n).map_sub, (valueL n).map_smul]

theorem velocity_comb (a b c : Space n) (r : ℝ) :
    velocity (a - b - r • c) = velocity a - velocity b - r • velocity c := by
  change velocityL n (a - b - r • c) = velocityL n a - velocityL n b - r • velocityL n c
  rw [(velocityL n).map_sub, (velocityL n).map_sub, (velocityL n).map_smul]

theorem measureUnivNNReal_interval : measureUnivNNReal intervalMeasure = 1 := by
  change (volume.restrict (Ioo (0 : ℝ) 1) univ).toNNReal = 1
  simp [Measure.restrict_apply MeasurableSet.univ, Real.volume_Ioo]

theorem coeFn_comb (f a b : ValueLp n) (c : ℝ) :
    ⇑(f - a - c • b) =ᵐ[intervalMeasure] fun t => f t - a t - c • b t := by
  filter_upwards [Lp.coeFn_sub (f - a) (c • b), Lp.coeFn_sub f a, Lp.coeFn_smul c b]
    with t h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.sub_apply, h3, Pi.smul_apply]

theorem valueLp_norm_le_of_ae_bound {f : ValueLp n} {C : ℝ} (hC : 0 ≤ C)
    (hfC : ∀ᵐ t ∂intervalMeasure, ‖f t‖ ≤ C) : ‖f‖ ≤ C := by
  have hb := Lp.norm_le_of_ae_bound hC hfC
  rwa [measureUnivNNReal_interval, NNReal.coe_one, Real.one_rpow, one_mul] at hb

/-- Value control of a combination from almost-everywhere representatives. -/
theorem value_comb_norm_le {X Y Z : Space n} {r C : ℝ} {x y z : ℝ → Ambient n} (hC : 0 ≤ C)
    (hx : value X =ᵐ[intervalMeasure] x) (hy : value Y =ᵐ[intervalMeasure] y)
    (hz : value Z =ᵐ[intervalMeasure] z)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, ‖x t - y t - r • z t‖ ≤ C) :
    ‖value (X - Y - r • Z)‖ ≤ C := by
  rw [value_comb]
  apply valueLp_norm_le_of_ae_bound hC
  filter_upwards [coeFn_comb (value X) (value Y) (value Z) r, hx, hy, hz,
    ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3 h4 ht
  rw [h1, h2, h3, h4]
  exact h t ht

/-- Velocity control of a combination from almost-everywhere representatives. -/
theorem velocity_comb_norm_le {X Y Z : Space n} {r c : ℝ} {x y z : ℝ → Ambient n}
    {g : Lp ℝ 2 intervalMeasure} {gf : ℝ → ℝ}
    (hx : velocity X =ᵐ[intervalMeasure] x) (hy : velocity Y =ᵐ[intervalMeasure] y)
    (hz : velocity Z =ᵐ[intervalMeasure] z) (hg : g =ᵐ[intervalMeasure] gf)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, ‖x t - y t - r • z t‖ ≤ c * ‖gf t‖) :
    ‖velocity (X - Y - r • Z)‖ ≤ c * ‖g‖ := by
  rw [velocity_comb]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_comb (velocity X) (velocity Y) (velocity Z) r, hx, hy, hz, hg,
    ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3 h4 h5 ht
  rw [h1, h2, h3, h4, h5]
  exact h t ht

/-- Norm control in the original graph from value and velocity control. -/
theorem norm_le_of_value_velocity {w : Space n} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : ‖value w‖ ≤ A) (h2 : ‖velocity w‖ ≤ B) : ‖w‖ ≤ A + B := by
  have hsq := norm_sq_eq w
  have ha := norm_nonneg (value w)
  have hb := norm_nonneg (velocity w)
  have hX := norm_nonneg w
  have hle : ‖w‖ ^ 2 ≤ (A + B) ^ 2 := by
    rw [hsq]
    nlinarith [mul_le_mul h1 h1 ha hA, mul_le_mul h2 h2 hb hB]
  exact (pow_le_pow_iff_left₀ hX (add_nonneg hA hB) (by norm_num : (2 : ℕ) ≠ 0)).mp hle

/-- A quadratic remainder bound near zero gives a derivative at zero. -/
theorem hasDerivAt_of_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {x v : E} {K : ℝ} (h0 : f 0 = x)
    (h : ∀ r : ℝ, |r| ≤ 1 → ‖f r - x - r • v‖ ≤ K * r ^ 2) : HasDerivAt f v 0 := by
  subst h0
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), |r| ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℝ) one_pos] with r hr
    simpa [Real.dist_eq] using hr
  have hO : (fun r : ℝ => f (0 + r) - f 0 - r • v) =O[𝓝 0] fun r => r ^ 2 := by
    apply IsBigO.of_bound K
    filter_upwards [hev] with r hr
    rw [zero_add, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    exact h r hr
  exact hO.trans_isLittleO (isLittleO_pow_id (by norm_num))

theorem exists_direction_bound (h : Space n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc (0 : ℝ) 1, ‖continuousRepresentative h t‖ ≤ M := by
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (continuousRepresentative_continuousOn h)
  exact ⟨C, (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩), hC⟩

theorem coeff_le_one {M : ℝ} (hM : 0 ≤ M) : M ^ 2 / 2 ≤ M ^ 2 + M := by
  nlinarith [sq_nonneg M]

theorem coeff_le_two (M : ℝ) : M ^ 2 / 4 + M ≤ M ^ 2 + M := by
  nlinarith [sq_nonneg M]

theorem curveVelocity_sub_pointwise (u : SphereLoop n) (h : TangentSpace u) {r M : ℝ}
    (hr : |r| ≤ 1) (hM : 0 ≤ M)
    (hk : ∀ t ∈ Icc (0 : ℝ) 1, ‖continuousRepresentative (h : Space n) t‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖curveVelocityFun r (u.data : Space n) (h : Space n) t -
        velocity (u.data : Space n) t - r • velocity (h : Space n) t‖ ≤
      r ^ 2 * (M ^ 2 + M) *
        ‖‖velocity (u.data : Space n) t‖ + ‖velocity (h : Space n) t‖‖ := by
  have hb := ratDeriv_sub_bound hr (u.sphere_constraint ⟨t, ht⟩)
    (((mem_tangentSubmodule_iff u h).mp h.property).2 ⟨t, ht⟩) hM (hk t ht)
    (velocity (u.data : Space n) t) (velocity (h : Space n) t)
  have hα := norm_nonneg (velocity (u.data : Space n) t)
  have hβ := norm_nonneg (velocity (h : Space n) t)
  have hle : r ^ 2 * (M ^ 2 / 2 * ‖velocity (u.data : Space n) t‖ +
        (M ^ 2 / 4 + M) * ‖velocity (h : Space n) t‖) ≤
      r ^ 2 * ((M ^ 2 + M) * ‖velocity (u.data : Space n) t‖ +
        (M ^ 2 + M) * ‖velocity (h : Space n) t‖) :=
    mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right (coeff_le_one hM) hα)
      (mul_le_mul_of_nonneg_right (coeff_le_two M) hβ)) (sq_nonneg r)
  have heq : r ^ 2 * ((M ^ 2 + M) * ‖velocity (u.data : Space n) t‖ +
        (M ^ 2 + M) * ‖velocity (h : Space n) t‖) =
      r ^ 2 * (M ^ 2 + M) *
        ‖‖velocity (u.data : Space n) t‖ + ‖velocity (h : Space n) t‖‖ := by
    rw [Real.norm_of_nonneg (add_nonneg hα hβ)]
    ring
  exact (hb.trans hle).trans_eq heq

/-- The scalar L² control of the pair of velocities. -/
def velocitySumLp (u h : Space n) : Lp ℝ 2 intervalMeasure :=
  (velocitySum_memLp u h).toLp _

theorem curveData_value_sub_le (u : SphereLoop n) (h : TangentSpace u) {r M : ℝ}
    (hr : |r| ≤ 1) (hM : 0 ≤ M)
    (hk : ∀ t ∈ Icc (0 : ℝ) 1, ‖continuousRepresentative (h : Space n) t‖ ≤ M) :
    ‖value (curveData r (u.data : Space n) h - (u.data : Space n) - r • (h : Space n))‖ ≤
      r ^ 2 * (M ^ 2 / 2 + M ^ 3 / 4) :=
  value_comb_norm_le (by positivity) (value_curveData_ae r (u.data : Space n) h)
    (value_ae_continuousRepresentative (u.data : Space n))
    (value_ae_continuousRepresentative (h : Space n))
    (fun t ht => ratMap_sub_bound hr (u.sphere_constraint ⟨t, Ioo_subset_Icc_self ht⟩) hM
      (hk t (Ioo_subset_Icc_self ht)))

theorem curveData_velocity_sub_le (u : SphereLoop n) (h : TangentSpace u) {r M : ℝ}
    (hr : |r| ≤ 1) (hM : 0 ≤ M)
    (hk : ∀ t ∈ Icc (0 : ℝ) 1, ‖continuousRepresentative (h : Space n) t‖ ≤ M) :
    ‖velocity (curveData r (u.data : Space n) h - (u.data : Space n) - r • (h : Space n))‖ ≤
      r ^ 2 * (M ^ 2 + M) * ‖velocitySumLp (u.data : Space n) (h : Space n)‖ :=
  velocity_comb_norm_le (velocity_curveData_ae r (u.data : Space n) h)
    (Filter.EventuallyEq.refl _ _) (Filter.EventuallyEq.refl _ _)
    (velocitySum_memLp (u.data : Space n) (h : Space n)).coeFn_toLp
    (fun _ ht => curveVelocity_sub_pointwise u h hr hM hk (Ioo_subset_Icc_self ht))

/-- The realizing curve differs from the straight line u + r h by O(r²) in H¹. -/
theorem curveData_sub_le (u : SphereLoop n) (h : TangentSpace u) :
    ∃ K : ℝ, ∀ r : ℝ, |r| ≤ 1 →
      ‖curveData r (u.data : Space n) h - (u.data : Space n) - r • (h : Space n)‖ ≤
        K * r ^ 2 := by
  obtain ⟨M, hM, hk⟩ := exists_direction_bound (h : Space n)
  refine ⟨(M ^ 2 / 2 + M ^ 3 / 4) +
    (M ^ 2 + M) * ‖velocitySumLp (u.data : Space n) (h : Space n)‖, fun r hr => ?_⟩
  have hb := norm_le_of_value_velocity (by positivity) (by positivity)
    (curveData_value_sub_le u h hr hM hk) (curveData_velocity_sub_le u h hr hM hk)
  exact hb.trans_eq (by ring)

theorem curveData_hasDerivAt (u : SphereLoop n) (h : TangentSpace u) :
    HasDerivAt (fun r => curveData r (u.data : Space n) (h : Space n)) (h : Space n) 0 := by
  obtain ⟨K, hK⟩ := curveData_sub_le u h
  exact hasDerivAt_of_sub_le (curveData_zero (u.data : Space n) (h : Space n)) hK

theorem curveLoop_hasDerivAt (u : SphereLoop n) (h : TangentSpace u) :
    HasDerivAt (fun r => ((curveLoop u h r).data : Space n)) (h : Space n) 0 :=
  curveData_hasDerivAt u h

/-- Every periodic tangent field is the derivative of an actual sphere-valued H¹ curve. -/
theorem exists_curve_realization (u : SphereLoop n) (h : TangentSpace u) :
    ∃ γ : ℝ → SphereLoop n, γ 0 = u ∧
      HasDerivAt (fun r => ((γ r).data : Space n)) (h : Space n) 0 :=
  ⟨curveLoop u h, curveLoop_zero u h, curveLoop_hasDerivAt u h⟩

/-- Tangent criticality is exactly stationarity of the energy along every H¹ sphere curve. -/
theorem tangentCritical_iff_curve_stationary (F : ReversibleMetric n) (u : SphereLoop n) :
    TangentCritical F u ↔ ∀ (γ : ℝ → SphereLoop n) (h : Space n), γ 0 = u →
      HasDerivAt (fun r => ((γ r).data : Space n)) h 0 →
      HasDerivAt (fun r => Finsler.SobolevEnergy.energy F (γ r)) 0 0 := by
  constructor
  · intro hc γ h hγ hd
    exact tangentCritical_curve_stationary F γ (by rw [hγ]; exact hc) hd
  · intro hs
    exact tangentCritical_of_curve_realization F u (exists_curve_realization u) hs

end

end Finsler.SobolevCurveRealization
