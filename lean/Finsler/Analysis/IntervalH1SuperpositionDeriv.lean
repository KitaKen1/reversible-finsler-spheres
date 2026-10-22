module

public import Finsler.Analysis.IntervalH1TripleMap

/-! Fréchet differentiability of superposition operators. For a C³ map Γ of pairs of
ambient vectors and a fixed graph element u, the operator h ↦ Γ(u, h) on the original weak
H¹ graph is Fréchet differentiable, with derivative the superposition of the partial
derivative of Γ in its second slot. The candidate derivative is linear and bounded (shell
bound from a bound on the unit ball), and the remainder is O(‖b‖²): pointwise second-order
Taylor bounds for Γ and its derivative on a compact ball, the symmetry of the second
derivative, and L² Minkowski control. Continuity of the derivative in h is not asserted. -/

@[expose] public section

namespace Finsler.SobolevSuperpositionDeriv

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevPairMap
open Finsler.SobolevTripleMap Finsler.SobolevCurveRealization Finsler.SobolevCurveFamily
open MeasureTheory Set Filter Asymptotics
open scoped Topology

noncomputable section

set_option maxHeartbeats 400000

/-- Second-order Taylor bound from a Lipschitz bound on the derivative over a convex set. -/
theorem taylor_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) {a d : E} (ha : a ∈ s) (had : a + d ∈ s) {C : ℝ}
    (hC : ∀ z ∈ s, ‖fderiv ℝ f z - fderiv ℝ f a‖ ≤ C * ‖z - a‖) (hC0 : 0 ≤ C) :
    ‖f (a + d) - f a - fderiv ℝ f a d‖ ≤ C * ‖d‖ ^ 2 := by
  have hseg : segment ℝ a (a + d) ⊆ s := hs.segment_subset ha had
  have hderiv : ∀ z ∈ segment ℝ a (a + d), HasFDerivWithinAt (fun z => f z - fderiv ℝ f a z)
      (fderiv ℝ f z - fderiv ℝ f a) (segment ℝ a (a + d)) z :=
    fun z hz => ((hf z (hseg hz)).hasFDerivAt.sub (fderiv ℝ f a).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ segment ℝ a (a + d), ‖fderiv ℝ f z - fderiv ℝ f a‖ ≤ C * ‖d‖ := by
    intro z hz
    refine (hC z (hseg hz)).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hz
    have e : p • a + q • (a + d) - a = q • d := by
      have hp' : p = 1 - q := by linarith
      rw [hp', smul_add, sub_smul, one_smul]
      abel
    rw [e, norm_smul, Real.norm_of_nonneg hq]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have h := (convex_segment a (a + d)).norm_image_sub_le_of_norm_hasFDerivWithin_le hderiv hbound
    (left_mem_segment ℝ a (a + d)) (right_mem_segment ℝ a (a + d))
  have e2 : f (a + d) - fderiv ℝ f a (a + d) - (f a - fderiv ℝ f a a) =
      f (a + d) - f a - fderiv ℝ f a d := by
    rw [map_add]
    abel
  rw [e2, add_sub_cancel_left] at h
  calc _ ≤ C * ‖d‖ * ‖d‖ := h
    _ = C * ‖d‖ ^ 2 := by ring

/-- A quadratic remainder bound near zero gives a Fréchet derivative. -/
theorem hasFDerivAt_of_quadratic {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {L : E →L[ℝ] F} {x : E} {K : ℝ}
    (h : ∀ d : E, ‖d‖ ≤ 1 → ‖f (x + d) - f x - L d‖ ≤ K * ‖d‖ ^ 2) : HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hev : ∀ᶠ d in 𝓝 (0 : E), ‖d‖ ≤ 1 := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : E) one_pos] with d hd
    simpa using hd
  have hO : (fun d => f (x + d) - f x - L d) =O[𝓝 0] fun d => ‖d‖ ^ 2 := by
    apply IsBigO.of_bound K
    filter_upwards [hev] with d hd
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact h d hd
  exact hO.trans_isLittleO (isLittleO_norm_pow_id (by norm_num))

variable {n : ℕ} {Γ : Ambient n × Ambient n → Ambient n}

/-- The partial derivative of Γ in its second slot, as a map of triples. -/
def partialMap (Γ : Ambient n × Ambient n → Ambient n) (z : E3 n) : Ambient n :=
  fderiv ℝ Γ (z.1, z.2.1) (0, z.2.2)

theorem partialMap_contDiff (hΓ : ContDiff ℝ 3 Γ) : ContDiff ℝ 2 (partialMap Γ) := by
  have h1 : ContDiff ℝ 2 (fun z : E3 n => fderiv ℝ Γ (z.1, z.2.1)) :=
    (hΓ.fderiv_right (m := 2) (by norm_num)).comp
      (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
  have h2 : ContDiff ℝ 2 (fun z : E3 n => ((0 : Ambient n), z.2.2)) :=
    contDiff_const.prodMk (contDiff_snd.comp contDiff_snd)
  exact h1.clm_apply h2

theorem partialMap_hasFDerivAt (hΓ : ContDiff ℝ 3 Γ) (z : E3 n) :
    HasFDerivAt (partialMap Γ)
      ((fderiv ℝ Γ (z.1, z.2.1)).comp
          ((0 : E3 n →L[ℝ] Ambient n).prod
            ((ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)).comp
              (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n × Ambient n)))) +
        (((fderiv ℝ (fderiv ℝ Γ) (z.1, z.2.1)).comp
          ((ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n × Ambient n)).prod
            ((ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n)).comp
              (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n × Ambient n))))).flip
          ((0 : Ambient n), z.2.2))) z := by
  have hd2 : Differentiable ℝ (fderiv ℝ Γ) :=
    (hΓ.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)
  have hL : HasFDerivAt (fun z : E3 n => (z.1, z.2.1))
      ((ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n × Ambient n)).prod
        ((ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n)).comp
          (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n × Ambient n)))) z :=
    ((ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n × Ambient n)).prod
        ((ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n)).comp
          (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n × Ambient n)))).hasFDerivAt
  have hc : HasFDerivAt (fun z : E3 n => fderiv ℝ Γ (z.1, z.2.1))
      ((fderiv ℝ (fderiv ℝ Γ) (z.1, z.2.1)).comp
        ((ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n × Ambient n)).prod
          ((ContinuousLinearMap.fst ℝ (Ambient n) (Ambient n)).comp
            (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n × Ambient n))))) z :=
    (hd2 _).hasFDerivAt.comp z hL
  have hu : HasFDerivAt (fun z : E3 n => ((0 : Ambient n), z.2.2))
      ((0 : E3 n →L[ℝ] Ambient n).prod
        ((ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)).comp
          (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n × Ambient n)))) z :=
    ((0 : E3 n →L[ℝ] Ambient n).prod
        ((ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n)).comp
          (ContinuousLinearMap.snd ℝ (Ambient n) (Ambient n × Ambient n)))).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun w => by simp)
  exact hc.clm_apply hu

theorem partialMap_fderiv_apply (hΓ : ContDiff ℝ 3 Γ) (z X : E3 n) :
    fderiv ℝ (partialMap Γ) z X =
      fderiv ℝ Γ (z.1, z.2.1) (0, X.2.2) + fderiv ℝ (fderiv ℝ Γ) (z.1, z.2.1) (X.1, X.2.1) (0, z.2.2) := by
  rw [(partialMap_hasFDerivAt hΓ z).fderiv]
  simp

local instance : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

theorem partialMap_contDiff_one (hΓ : ContDiff ℝ 3 Γ) : ContDiff ℝ 1 (partialMap Γ) :=
  (partialMap_contDiff hΓ).of_le (by norm_num)

/-- The candidate derivative in the second argument: the partial derivative of Γ applied to
the direction, as a superposition of three graph elements. -/
def derivData (hΓ : ContDiff ℝ 3 Γ) (u h b : Space n) : Space n :=
  tripleData (partialMap_contDiff_one hΓ) u h b

theorem representative_derivData (hΓ : ContDiff ℝ 3 Γ) (u h b : Space n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (derivData hΓ u h b) t =
      fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)
        (0, continuousRepresentative b t) :=
  representative_tripleData _ _ _ _ ht

theorem value_derivData_ae (hΓ : ContDiff ℝ 3 Γ) (u h b : Space n) :
    value (derivData hΓ u h b) =ᵐ[intervalMeasure] fun t => partialMap Γ (tripleRep u h b t) :=
  value_tripleData_ae (partialMap_contDiff_one hΓ) u h b

theorem velocity_derivData_ae (hΓ : ContDiff ℝ 3 Γ) (u h b : Space n) :
    velocity (derivData hΓ u h b) =ᵐ[intervalMeasure]
      fun t => fderiv ℝ (partialMap Γ) (tripleRep u h b t) (tripleVel u h b t) :=
  velocity_tripleData_ae (partialMap_contDiff_one hΓ) u h b

theorem derivData_add (hΓ : ContDiff ℝ 3 Γ) (u h b b' : Space n) :
    derivData hΓ u h (b + b') = derivData hΓ u h b + derivData hΓ u h b' := by
  apply Finsler.SobolevEnergy.h1_eq_of_representative_eq
  intro t
  rw [continuousRepresentative_add _ _ t.property, representative_derivData hΓ _ _ _ t.property,
    representative_derivData hΓ _ _ _ t.property, representative_derivData hΓ _ _ _ t.property,
    continuousRepresentative_add _ _ t.property, ← map_add]
  congr 1
  ext <;> simp

theorem derivData_smul (hΓ : ContDiff ℝ 3 Γ) (u h b : Space n) (c : ℝ) :
    derivData hΓ u h (c • b) = c • derivData hΓ u h b := by
  apply Finsler.SobolevEnergy.h1_eq_of_representative_eq
  intro t
  rw [continuousRepresentative_smul _ _ t.property, representative_derivData hΓ _ _ _ t.property,
    representative_derivData hΓ _ _ _ t.property, continuousRepresentative_smul _ _ t.property,
    ← map_smul]
  congr 1
  ext <;> simp

/-- The candidate derivative as a linear map. -/
def derivLinear (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) : Space n →ₗ[ℝ] Space n where
  toFun := derivData hΓ u h
  map_add' := derivData_add hΓ u h
  map_smul' c b := derivData_smul hΓ u h b c

theorem tripleRep_norm_le (u h b : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖tripleRep u h b t‖ ≤ 2 * (‖u‖ + ‖h‖ + ‖b‖) := by
  have hu := continuousRepresentative_norm_le_two u ht
  have hh := continuousRepresentative_norm_le_two h ht
  have hb := continuousRepresentative_norm_le_two b ht
  have hu0 := norm_nonneg u
  have hh0 := norm_nonneg h
  have hb0 := norm_nonneg b
  refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
  · change ‖continuousRepresentative u t‖ ≤ _
    linarith
  · change ‖continuousRepresentative h t‖ ≤ _
    linarith
  · change ‖continuousRepresentative b t‖ ≤ _
    linarith

theorem derivData_norm_le (hΓ : ContDiff ℝ 3 Γ) (u h b : Space n) {R B₀ B₁ : ℝ}
    (hR : 2 * (‖u‖ + ‖h‖ + ‖b‖) ≤ R)
    (hB₀ : ∀ z ∈ Metric.closedBall (0 : E3 n) R, ‖partialMap Γ z‖ ≤ B₀)
    (hB₁ : ∀ z ∈ Metric.closedBall (0 : E3 n) R, ‖fderiv ℝ (partialMap Γ) z‖ ≤ B₁)
    (hB₀0 : 0 ≤ B₀) (hB₁0 : 0 ≤ B₁) :
    ‖derivData hΓ u h b‖ ≤
      B₀ + B₁ * ((‖velocity u‖ + ‖velocity h‖) + (‖velocity b‖ + ‖(0 : ValueLp n)‖)) := by
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, tripleRep u h b t ∈ Metric.closedBall (0 : E3 n) R :=
    fun t ht => mem_closedBall_zero_iff.mpr ((tripleRep_norm_le u h b ht).trans hR)
  have hval : ‖value (derivData hΓ u h b)‖ ≤ B₀ := by
    apply valueLp_norm_le_of_ae_bound hB₀0
    filter_upwards [value_derivData_ae hΓ u h b,
      ae_restrict_mem measurableSet_Ioo] with t h1 ht
    rw [h1]
    exact hB₀ _ (hmem t (Ioo_subset_Icc_self ht))
  have hvel : ‖velocity (derivData hΓ u h b)‖ ≤
      B₁ * (‖velocity u‖ + ‖velocity h‖) + B₁ * (‖velocity b‖ + ‖(0 : ValueLp n)‖) := by
    apply norm_le_of_ae_le_sum hB₁0 hB₁0
    filter_upwards [velocity_derivData_ae hΓ u h b,
      Lp.coeFn_zero (E := Ambient n) (p := 2) (μ := intervalMeasure),
      ae_restrict_mem measurableSet_Ioo] with t h1 h0 ht
    rw [h1, h0, Pi.zero_apply, norm_zero, add_zero]
    calc ‖fderiv ℝ (partialMap Γ) (tripleRep u h b t) (tripleVel u h b t)‖
        ≤ ‖fderiv ℝ (partialMap Γ) (tripleRep u h b t)‖ * ‖tripleVel u h b t‖ :=
          (fderiv ℝ (partialMap Γ) _).le_opNorm _
      _ ≤ B₁ * (‖velocity u t‖ + ‖velocity h t‖ + ‖velocity b t‖) :=
          mul_le_mul (hB₁ _ (hmem t (Ioo_subset_Icc_self ht))) (norm_tripleVel_le u h b t)
            (norm_nonneg _) hB₁0
      _ = B₁ * (‖velocity u t‖ + ‖velocity h t‖) + B₁ * ‖velocity b t‖ := by ring
  have hnorm := norm_le_of_value_velocity hB₀0 (by positivity) hval hvel
  calc _ ≤ B₀ + (B₁ * (‖velocity u‖ + ‖velocity h‖) + B₁ * (‖velocity b‖ + ‖(0 : ValueLp n)‖)) :=
      hnorm
    _ = _ := by ring

theorem exists_derivData_bound (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ b : Space n, ‖derivData hΓ u h b‖ ≤ K * ‖b‖ := by
  set R : ℝ := 2 * (‖u‖ + ‖h‖ + 1) with hRdef
  have hc0 : ContinuousOn (partialMap Γ) (Metric.closedBall (0 : E3 n) R) :=
    (partialMap_contDiff hΓ).continuous.continuousOn
  have hc1 : ContinuousOn (fderiv ℝ (partialMap Γ)) (Metric.closedBall (0 : E3 n) R) :=
    ((partialMap_contDiff hΓ).continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : E3 n) R).exists_bound_of_continuousOn hc0
  obtain ⟨B₁, hB₁⟩ := (isCompact_closedBall (0 : E3 n) R).exists_bound_of_continuousOn hc1
  have hRpos : 0 ≤ R := by positivity
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0 (Metric.mem_closedBall_self hRpos))
  have hB₁0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB₁ 0 (Metric.mem_closedBall_self hRpos))
  have hK0 : 0 ≤ B₀ + B₁ * (‖u‖ + ‖h‖ + 1) := by positivity
  refine ⟨2 * (B₀ + B₁ * (‖u‖ + ‖h‖ + 1)), by positivity, fun b => ?_⟩
  have hshell := (derivLinear hΓ u h).bound_of_shell (ε := 1) (C := 2 * (B₀ + B₁ * (‖u‖ + ‖h‖ + 1)))
    one_pos (c := (2 : ℝ)) (by norm_num) (fun x hx1 hx2 => ?_) b
  · exact hshell
  · have hxle : ‖x‖ ≤ 1 := hx2.le
    have hR' : 2 * (‖u‖ + ‖h‖ + ‖x‖) ≤ R := by
      rw [hRdef]
      linarith
    have hunit := derivData_norm_le hΓ u h x hR' hB₀ hB₁ hB₀0 hB₁0
    have hvu := velocity_norm_le u
    have hvh := velocity_norm_le h
    have hvx : ‖velocity x‖ ≤ 1 := (velocity_norm_le x).trans hxle
    have hunit' : ‖(derivLinear hΓ u h) x‖ ≤ B₀ + B₁ * (‖u‖ + ‖h‖ + 1) := by
      refine hunit.trans ?_
      rw [norm_zero, add_zero]
      gcongr
    have hhalf : 1 / 2 ≤ ‖x‖ := by
      have h2 : ‖(2 : ℝ)‖ = 2 := by norm_num
      rw [h2] at hx1
      exact hx1
    calc ‖(derivLinear hΓ u h) x‖ ≤ B₀ + B₁ * (‖u‖ + ‖h‖ + 1) := hunit'
      _ = 2 * (B₀ + B₁ * (‖u‖ + ‖h‖ + 1)) * (1 / 2) := by ring
      _ ≤ 2 * (B₀ + B₁ * (‖u‖ + ‖h‖ + 1)) * ‖x‖ := by gcongr

/-- The derivative of the superposition operator in its second argument. -/
def derivL (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) : Space n →L[ℝ] Space n :=
  (derivLinear hΓ u h).mkContinuousOfExistsBound
    (let ⟨K, _, hK⟩ := exists_derivData_bound hΓ u h; ⟨K, hK⟩)

theorem derivL_apply (hΓ : ContDiff ℝ 3 Γ) (u h b : Space n) :
    derivL hΓ u h b = derivData hΓ u h b := rfl

theorem value_sub3 (X Y Z : Space n) : value (X - Y - Z) = value X - value Y - value Z := by
  change valueL n (X - Y - Z) = valueL n X - valueL n Y - valueL n Z
  rw [(valueL n).map_sub, (valueL n).map_sub]

theorem velocity_sub3 (X Y Z : Space n) :
    velocity (X - Y - Z) = velocity X - velocity Y - velocity Z := by
  change velocityL n (X - Y - Z) = velocityL n X - velocityL n Y - velocityL n Z
  rw [(velocityL n).map_sub, (velocityL n).map_sub]

theorem velocity_add (X Y : Space n) : velocity (X + Y) = velocity X + velocity Y := by
  change velocityL n (X + Y) = velocityL n X + velocityL n Y
  exact (velocityL n).map_add X Y

theorem coeFn_sub3 (f a b : ValueLp n) :
    ⇑(f - a - b) =ᵐ[intervalMeasure] fun t => f t - a t - b t := by
  filter_upwards [Lp.coeFn_sub (f - a) b, Lp.coeFn_sub f a] with t h1 h2
  rw [h1, Pi.sub_apply, h2, Pi.sub_apply]

theorem value_sub3_norm_le {X Y Z : Space n} {x y z : ℝ → Ambient n} {C : ℝ} (hC : 0 ≤ C)
    (hx : value X =ᵐ[intervalMeasure] x) (hy : value Y =ᵐ[intervalMeasure] y)
    (hz : value Z =ᵐ[intervalMeasure] z)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, ‖x t - y t - z t‖ ≤ C) : ‖value (X - Y - Z)‖ ≤ C := by
  rw [value_sub3]
  apply valueLp_norm_le_of_ae_bound hC
  filter_upwards [coeFn_sub3 (value X) (value Y) (value Z), hx, hy, hz,
    ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3 h4 ht
  rw [h1, h2, h3, h4]
  exact h t ht

theorem velocity_sub3_norm_le {X Y Z : Space n} {x y z : ℝ → Ambient n} {a b c d : ValueLp n}
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hx : velocity X =ᵐ[intervalMeasure] x) (hy : velocity Y =ᵐ[intervalMeasure] y)
    (hz : velocity Z =ᵐ[intervalMeasure] z)
    (h : ∀ᵐ t ∂intervalMeasure,
      ‖x t - y t - z t‖ ≤ c₁ * (‖a t‖ + ‖b t‖) + c₂ * (‖c t‖ + ‖d t‖)) :
    ‖velocity (X - Y - Z)‖ ≤ c₁ * (‖a‖ + ‖b‖) + c₂ * (‖c‖ + ‖d‖) := by
  rw [velocity_sub3]
  apply norm_le_of_ae_le_sum hc₁ hc₂
  filter_upwards [coeFn_sub3 (velocity X) (velocity Y) (velocity Z), hx, hy, hz, h]
    with t h1 h2 h3 h4 h5
  rw [h1, h2, h3, h4]
  exact h5

/-- Pointwise algebra of the velocity remainder. -/
theorem velocity_remainder_identity {A A₀ : Ambient n × Ambient n →L[ℝ] Ambient n}
    {H : Ambient n × Ambient n →L[ℝ] (Ambient n × Ambient n →L[ℝ] Ambient n)}
    (X Y D D' : Ambient n) (hsymm : H (X, Y) (0, D) = H (0, D) (X, Y)) :
    A (X, Y + D') - A₀ (X, Y) - (A₀ (0, D') + H (X, Y) (0, D)) =
      (A - A₀ - H (0, D)) (X, Y) + (A - A₀) (0, D') := by
  have e : ((X, Y + D') : Ambient n × Ambient n) = (X, Y) + (0, D') := by
    ext <;> simp
  rw [e, map_add, hsymm]
  simp only [sub_apply]
  abel

/-- The superposition operator of a C³ map, in its second argument. -/
def superposition (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) : Space n :=
  mapData (hΓ.of_le (by norm_num)) u h

theorem velocity_derivL_ae (hΓ : ContDiff ℝ 3 Γ) (u h b : Space n) :
    velocity (derivL hΓ u h b) =ᵐ[intervalMeasure]
      fun t => fderiv ℝ (partialMap Γ) (tripleRep u h b t) (tripleVel u h b t) :=
  velocity_derivData_ae hΓ u h b

theorem value_superposition_ae (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) :
    value (superposition hΓ u h) =ᵐ[intervalMeasure] fun t => Γ (pairRep u h t) :=
  value_mapData_ae _ u h

theorem velocity_superposition_ae (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) :
    velocity (superposition hΓ u h) =ᵐ[intervalMeasure]
      fun t => fderiv ℝ Γ (pairRep u h t) (pairVel u h t) :=
  velocity_mapData_ae _ u h

theorem norm_zero_fst_le (D : Ambient n) : ‖((0 : Ambient n), D)‖ ≤ ‖D‖ :=
  norm_prod_le_iff.mpr ⟨by simp, le_rfl⟩

theorem norm_pair_le (X Y : Ambient n) : ‖((X, Y) : Ambient n × Ambient n)‖ ≤ ‖X‖ + ‖Y‖ :=
  norm_prod_le_iff.mpr ⟨le_add_of_nonneg_right (norm_nonneg _),
    le_add_of_nonneg_left (norm_nonneg _)⟩

set_option maxHeartbeats 3200000 in
theorem superposition_remainder_le (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) :
    ∃ K : ℝ, ∀ b : Space n, ‖b‖ ≤ 1 →
      ‖superposition hΓ u (h + b) - superposition hΓ u h - derivL hΓ u h b‖ ≤ K * ‖b‖ ^ 2 := by
  set R : ℝ := 2 * (‖u‖ + ‖h‖ + 1) with hRdef
  have hD1 : ContDiff ℝ 2 (fderiv ℝ Γ) := hΓ.fderiv_right (m := 2) (by norm_num)
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ Γ)) := hD1.fderiv_right (m := 1) (by norm_num)
  obtain ⟨L₂, hL₂⟩ := ((hD1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffOn
    (s := Metric.closedBall (0 : Ambient n × Ambient n) R)).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨L₃, hL₃⟩ := (hD2.contDiffOn (s := Metric.closedBall (0 : Ambient n × Ambient n) R)).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨4 * (L₂ : ℝ) + (4 * (L₃ : ℝ) * (‖u‖ + ‖h‖) + 2 * (L₂ : ℝ)), fun b hb => ?_⟩
  have hb0 := norm_nonneg b
  -- membership of the relevant points in the ball
  have hmemA : ∀ t ∈ Icc (0 : ℝ) 1, ((continuousRepresentative u t, continuousRepresentative h t) :
      Ambient n × Ambient n) ∈ Metric.closedBall (0 : Ambient n × Ambient n) R := by
    intro t ht
    rw [mem_closedBall_zero_iff]
    have hu := continuousRepresentative_norm_le_two u ht
    have hh := continuousRepresentative_norm_le_two h ht
    have hu0 := norm_nonneg u
    have hh0 := norm_nonneg h
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · change ‖continuousRepresentative u t‖ ≤ R
      rw [hRdef]
      linarith
    · change ‖continuousRepresentative h t‖ ≤ R
      rw [hRdef]
      linarith
  have hmemB : ∀ t ∈ Icc (0 : ℝ) 1, ((continuousRepresentative u t, continuousRepresentative h t) +
      ((0 : Ambient n), continuousRepresentative b t) : Ambient n × Ambient n) ∈
        Metric.closedBall (0 : Ambient n × Ambient n) R := by
    intro t ht
    rw [mem_closedBall_zero_iff, Prod.mk_add_mk, add_zero]
    have hu := continuousRepresentative_norm_le_two u ht
    have hh := continuousRepresentative_norm_le_two h ht
    have hbb := continuousRepresentative_norm_le_two b ht
    have htri := norm_add_le (continuousRepresentative h t) (continuousRepresentative b t)
    have hu0 := norm_nonneg u
    have hh0 := norm_nonneg h
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · change ‖continuousRepresentative u t‖ ≤ R
      rw [hRdef]
      linarith
    · change ‖continuousRepresentative h t + continuousRepresentative b t‖ ≤ R
      rw [hRdef]
      linarith
  -- Lipschitz and Taylor bounds in norm form
  have hLip₂ : ∀ z ∈ Metric.closedBall (0 : Ambient n × Ambient n) R,
      ∀ w ∈ Metric.closedBall (0 : Ambient n × Ambient n) R,
        ‖fderiv ℝ Γ z - fderiv ℝ Γ w‖ ≤ L₂ * ‖z - w‖ := by
    intro z hz w hw
    have := hL₂.dist_le_mul z hz w hw
    rwa [dist_eq_norm, dist_eq_norm] at this
  have hLip₃ : ∀ z ∈ Metric.closedBall (0 : Ambient n × Ambient n) R,
      ∀ w ∈ Metric.closedBall (0 : Ambient n × Ambient n) R,
        ‖fderiv ℝ (fderiv ℝ Γ) z - fderiv ℝ (fderiv ℝ Γ) w‖ ≤ L₃ * ‖z - w‖ := by
    intro z hz w hw
    have := hL₃.dist_le_mul z hz w hw
    rwa [dist_eq_norm, dist_eq_norm] at this
  have hΓdiff : ∀ z ∈ Metric.closedBall (0 : Ambient n × Ambient n) R, DifferentiableAt ℝ Γ z :=
    fun z _ => (hΓ.differentiable (by norm_num)) z
  have hD1diff : ∀ z ∈ Metric.closedBall (0 : Ambient n × Ambient n) R,
      DifferentiableAt ℝ (fderiv ℝ Γ) z :=
    fun z _ => (hD1.differentiable (by norm_num)) z
  have hsymm : ∀ z v w : Ambient n × Ambient n,
      fderiv ℝ (fderiv ℝ Γ) z v w = fderiv ℝ (fderiv ℝ Γ) z w v :=
    fun z v w => (hΓ.contDiffAt.isSymmSndFDerivAt (by simp; norm_num)) v w
  have e : ∀ t : ℝ, ((continuousRepresentative u t, continuousRepresentative h t) +
      ((0 : Ambient n), continuousRepresentative b t) : Ambient n × Ambient n) =
        (continuousRepresentative u t, continuousRepresentative h t + continuousRepresentative b t) :=
    fun t => by rw [Prod.mk_add_mk, add_zero]
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, ‖((0 : Ambient n), continuousRepresentative b t)‖ ≤ 2 * ‖b‖ :=
    fun t ht => (norm_zero_fst_le _).trans (continuousRepresentative_norm_le_two b ht)
  -- pointwise value bound
  have hval_pt : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖Γ (continuousRepresentative u t, continuousRepresentative h t + continuousRepresentative b t) -
        Γ (continuousRepresentative u t, continuousRepresentative h t) -
        fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)
          (0, continuousRepresentative b t)‖ ≤ 4 * L₂ * ‖b‖ ^ 2 := by
    intro t ht
    have hT := taylor_bound (convex_closedBall (0 : Ambient n × Ambient n) R) hΓdiff
      (hmemA t ht) (hmemB t ht) (C := L₂) (fun z hz => hLip₂ z hz _ (hmemA t ht)) L₂.2
    rw [e t] at hT
    calc _ ≤ (L₂ : ℝ) * ‖((0 : Ambient n), continuousRepresentative b t)‖ ^ 2 := hT
      _ ≤ (L₂ : ℝ) * (2 * ‖b‖) ^ 2 := by gcongr; exact hd t ht
      _ = 4 * L₂ * ‖b‖ ^ 2 := by ring
  -- pointwise velocity bound
  have hvel_pt : ∀ t ∈ Icc (0 : ℝ) 1, ∀ X Y D' : Ambient n,
      ‖fderiv ℝ Γ (continuousRepresentative u t,
          continuousRepresentative h t + continuousRepresentative b t) (X, Y + D') -
        fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t) (X, Y) -
        (fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t) (0, D') +
          fderiv ℝ (fderiv ℝ Γ) (continuousRepresentative u t, continuousRepresentative h t) (X, Y)
            (0, continuousRepresentative b t))‖ ≤
        (4 * L₃ * ‖b‖ ^ 2) * (‖X‖ + ‖Y‖) + (2 * L₂ * ‖b‖) * (‖D'‖ + 0) := by
    intro t ht X Y D'
    rw [velocity_remainder_identity X Y (continuousRepresentative b t) D' (hsymm _ _ _)]
    have hT := taylor_bound (f := fderiv ℝ Γ) (convex_closedBall (0 : Ambient n × Ambient n) R)
      hD1diff (hmemA t ht) (hmemB t ht) (C := L₃) (fun z hz => hLip₃ z hz _ (hmemA t ht)) L₃.2
    rw [e t] at hT
    have hA := hLip₂ _ (hmemB t ht) _ (hmemA t ht)
    rw [add_sub_cancel_left, e t] at hA
    have hT' : ‖fderiv ℝ Γ (continuousRepresentative u t,
        continuousRepresentative h t + continuousRepresentative b t) -
        fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t) -
        fderiv ℝ (fderiv ℝ Γ) (continuousRepresentative u t, continuousRepresentative h t)
          (0, continuousRepresentative b t)‖ ≤ 4 * L₃ * ‖b‖ ^ 2 :=
      calc _ ≤ (L₃ : ℝ) * ‖((0 : Ambient n), continuousRepresentative b t)‖ ^ 2 := hT
        _ ≤ (L₃ : ℝ) * (2 * ‖b‖) ^ 2 := by gcongr; exact hd t ht
        _ = 4 * L₃ * ‖b‖ ^ 2 := by ring
    have hA' : ‖fderiv ℝ Γ (continuousRepresentative u t,
        continuousRepresentative h t + continuousRepresentative b t) -
        fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)‖ ≤ 2 * L₂ * ‖b‖ :=
      calc _ ≤ (L₂ : ℝ) * ‖((0 : Ambient n), continuousRepresentative b t)‖ := hA
        _ ≤ (L₂ : ℝ) * (2 * ‖b‖) := by gcongr; exact hd t ht
        _ = 2 * L₂ * ‖b‖ := by ring
    calc _ ≤ ‖(fderiv ℝ Γ (continuousRepresentative u t,
          continuousRepresentative h t + continuousRepresentative b t) -
          fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t) -
          fderiv ℝ (fderiv ℝ Γ) (continuousRepresentative u t, continuousRepresentative h t)
            (0, continuousRepresentative b t)) (X, Y)‖ +
        ‖(fderiv ℝ Γ (continuousRepresentative u t,
          continuousRepresentative h t + continuousRepresentative b t) -
          fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)) (0, D')‖ :=
          norm_add_le _ _
      _ ≤ (4 * L₃ * ‖b‖ ^ 2) * (‖X‖ + ‖Y‖) + (2 * L₂ * ‖b‖) * ‖D'‖ := by
          gcongr
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hT' (norm_pair_le X Y) (norm_nonneg _) (by positivity))
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hA' (norm_zero_fst_le D') (norm_nonneg _) (by positivity))
      _ = _ := by ring
  -- L² value bound
  have hval : ‖value (superposition hΓ u (h + b) - superposition hΓ u h - derivL hΓ u h b)‖ ≤
      4 * L₂ * ‖b‖ ^ 2 := by
    apply value_sub3_norm_le (by positivity)
      (x := fun t => Γ (continuousRepresentative u t,
        continuousRepresentative h t + continuousRepresentative b t))
      (y := fun t => Γ (continuousRepresentative u t, continuousRepresentative h t))
      (z := fun t => fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)
        (0, continuousRepresentative b t))
    · filter_upwards [value_superposition_ae hΓ u (h + b),
        ae_restrict_mem measurableSet_Ioo] with t h1 ht
      rw [h1]
      change Γ (continuousRepresentative u t, continuousRepresentative (h + b) t) = _
      rw [continuousRepresentative_add h b (Ioo_subset_Icc_self ht)]
    · exact value_superposition_ae hΓ u h
    · exact value_derivData_ae hΓ u h b
    · intro t ht
      exact hval_pt t (Ioo_subset_Icc_self ht)
  -- L² velocity bound
  have hvel : ‖velocity (superposition hΓ u (h + b) - superposition hΓ u h - derivL hΓ u h b)‖ ≤
      (4 * L₃ * ‖b‖ ^ 2) * (‖velocity u‖ + ‖velocity h‖) +
        (2 * L₂ * ‖b‖) * (‖velocity b‖ + ‖(0 : ValueLp n)‖) := by
    apply velocity_sub3_norm_le (by positivity) (by positivity)
      (x := fun t => fderiv ℝ Γ (continuousRepresentative u t,
        continuousRepresentative h t + continuousRepresentative b t)
          (velocity u t, velocity h t + velocity b t))
      (y := fun t => fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)
        (velocity u t, velocity h t))
      (z := fun t => fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)
          (0, velocity b t) +
        fderiv ℝ (fderiv ℝ Γ) (continuousRepresentative u t, continuousRepresentative h t)
          (velocity u t, velocity h t) (0, continuousRepresentative b t))
    · have hadd : velocity (h + b) = velocity h + velocity b := velocity_add h b
      filter_upwards [velocity_superposition_ae hΓ u (h + b),
        Lp.coeFn_add (velocity h) (velocity b), ae_restrict_mem measurableSet_Ioo] with t h1 h2 ht
      rw [h1]
      change fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative (h + b) t)
        (velocity u t, velocity (h + b) t) = _
      rw [continuousRepresentative_add h b (Ioo_subset_Icc_self ht), hadd, h2, Pi.add_apply]
    · exact velocity_superposition_ae hΓ u h
    · filter_upwards [velocity_derivL_ae hΓ u h b] with t h1
      rw [h1, partialMap_fderiv_apply hΓ]
      rfl
    · filter_upwards [Lp.coeFn_zero (E := Ambient n) (p := 2) (μ := intervalMeasure),
        ae_restrict_mem measurableSet_Ioo] with t h0 ht
      rw [h0, Pi.zero_apply, norm_zero]
      exact hvel_pt t (Ioo_subset_Icc_self ht) _ _ _
  have hnorm := norm_le_of_value_velocity (by positivity) (by positivity) hval hvel
  have hvu := velocity_norm_le u
  have hvh := velocity_norm_le h
  have hvb := velocity_norm_le b
  calc _ ≤ 4 * L₂ * ‖b‖ ^ 2 + ((4 * L₃ * ‖b‖ ^ 2) * (‖velocity u‖ + ‖velocity h‖) +
        (2 * L₂ * ‖b‖) * (‖velocity b‖ + ‖(0 : ValueLp n)‖)) := hnorm
    _ ≤ 4 * L₂ * ‖b‖ ^ 2 + ((4 * L₃ * ‖b‖ ^ 2) * (‖u‖ + ‖h‖) + (2 * L₂ * ‖b‖) * (‖b‖ + 0)) := by
        rw [norm_zero]
        gcongr
    _ = _ := by ring

/-- Superposition operators of C³ maps are Fréchet differentiable in the original H¹
topology, with derivative the superposition of the partial derivative. -/
theorem superposition_hasFDerivAt (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) :
    HasFDerivAt (fun h' => superposition hΓ u h') (derivL hΓ u h) h := by
  obtain ⟨K, hK⟩ := superposition_remainder_le hΓ u h
  exact hasFDerivAt_of_quadratic hK

end

end Finsler.SobolevSuperpositionDeriv
