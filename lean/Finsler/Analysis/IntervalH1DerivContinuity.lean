module

public import Finsler.Analysis.IntervalH1ChartSmooth

/-! Continuity of the Fréchet derivative of superposition operators. For a C³ map Γ and a
fixed u, the derivative of h ↦ Γ(u, h) depends Lipschitz-continuously on h in operator norm:
on the unit ball of directions the difference of derivatives is controlled pointwise by the
Lipschitz constants of DΓ and D²Γ and a bound of D²Γ on a compact ball, integrated by L²
Minkowski control, and the shell lemma passes to the operator norm. Hence such
superposition operators are C¹ on the original weak H¹ graph, and so are the stereographic
charts, the inverse chart operators, all chart transitions and radial normalization. -/

@[expose] public section

namespace Finsler.SobolevDerivContinuity

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevPairMap
open Finsler.SobolevTripleMap Finsler.SobolevCurveRealization Finsler.SobolevCurveFamily
open Finsler.SobolevSuperpositionDeriv Finsler.SobolevChartSmooth Finsler.SobolevSphereChart
open Finsler.SobolevRadialRetraction
open MeasureTheory Set Filter
open scoped Topology

noncomputable section

set_option maxHeartbeats 400000

variable {n : ℕ}

local instance : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

/-- Minkowski control from a three-term pointwise bound. -/
theorem norm_le_of_ae_le_sum3 {f a b c d : ValueLp n} {c₁ c₂ c₃ : ℝ} (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (h : ∀ᵐ t ∂intervalMeasure, ‖f t‖ ≤ c₁ * (‖a t‖ + ‖b t‖) + c₂ * ‖c t‖ + c₃ * ‖d t‖) :
    ‖f‖ ≤ c₁ * (‖a‖ + ‖b‖) + c₂ * ‖c‖ + c₃ * ‖d‖ := by
  have hG : ∀ᵐ t ∂intervalMeasure,
      (c₁ • (normLp a + normLp b) + c₂ • normLp c + c₃ • normLp d : Lp ℝ 2 intervalMeasure) t =
        c₁ * (‖a t‖ + ‖b t‖) + c₂ * ‖c t‖ + c₃ * ‖d t‖ := by
    filter_upwards [Lp.coeFn_add (c₁ • (normLp a + normLp b) + c₂ • normLp c) (c₃ • normLp d),
      Lp.coeFn_add (c₁ • (normLp a + normLp b)) (c₂ • normLp c),
      Lp.coeFn_smul c₁ (normLp a + normLp b), Lp.coeFn_smul c₂ (normLp c),
      Lp.coeFn_smul c₃ (normLp d), Lp.coeFn_add (normLp a) (normLp b),
      normLp_ae a, normLp_ae b, normLp_ae c, normLp_ae d] with t h1 h2 h3 h4 h5 h6 ha hb hc hd
    rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5, Pi.smul_apply, Pi.smul_apply,
      Pi.smul_apply, h6, Pi.add_apply, ha, hb, hc, hd, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  have hle : ‖f‖ ≤ ‖(c₁ • (normLp a + normLp b) + c₂ • normLp c + c₃ • normLp d :
      Lp ℝ 2 intervalMeasure)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h, hG] with t ht hGt
    rw [hGt, Real.norm_of_nonneg (by positivity)]
    exact ht
  refine hle.trans ((norm_add_le _ _).trans ?_)
  refine (add_le_add (norm_add_le (c₁ • (normLp a + normLp b) : Lp ℝ 2 intervalMeasure)
    (c₂ • normLp c)) le_rfl).trans ?_
  rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hc₁, Real.norm_of_nonneg hc₂,
    Real.norm_of_nonneg hc₃, ← norm_normLp a, ← norm_normLp b, ← norm_normLp c, ← norm_normLp d]
  gcongr
  exact norm_add_le _ _

variable {Γ : Ambient n × Ambient n → Ambient n}

/-- Pointwise algebra of the derivative difference. -/
theorem deriv_difference_identity {A A' : Ambient n × Ambient n →L[ℝ] Ambient n}
    {H H' : Ambient n × Ambient n →L[ℝ] (Ambient n × Ambient n →L[ℝ] Ambient n)}
    (X Y Y' D D' : Ambient n) :
    (A' (0, D') + H' (X, Y') (0, D)) - (A (0, D') + H (X, Y) (0, D)) =
      (A' - A) (0, D') + (H' - H) (X, Y') (0, D) + H (0, Y' - Y) (0, D) := by
  have e : ((0 : Ambient n), Y' - Y) = ((X, Y') : Ambient n × Ambient n) - (X, Y) := by
    ext <;> simp
  rw [e, map_sub]
  simp only [sub_apply]
  abel

theorem deriv_difference_pointwise {A A' : Ambient n × Ambient n →L[ℝ] Ambient n}
    {H H' : Ambient n × Ambient n →L[ℝ] (Ambient n × Ambient n →L[ℝ] Ambient n)}
    (X Y Y' D D' : Ambient n) {e L₂ L₃ B₂ : ℝ} (hA : ‖A' - A‖ ≤ L₂ * e) (hH : ‖H' - H‖ ≤ L₃ * e)
    (hB : ‖H‖ ≤ B₂) (hD : ‖D‖ ≤ 2) (he : 0 ≤ e) (hL₂ : 0 ≤ L₂) (hL₃ : 0 ≤ L₃) :
    ‖(A' (0, D') + H' (X, Y') (0, D)) - (A (0, D') + H (X, Y) (0, D))‖ ≤
      (2 * L₃ * e) * (‖X‖ + ‖Y'‖) + (L₂ * e) * ‖D'‖ + (2 * B₂) * ‖Y' - Y‖ := by
  rw [deriv_difference_identity]
  have h1 : ‖(A' - A) (0, D')‖ ≤ (L₂ * e) * ‖D'‖ :=
    ((A' - A).le_opNorm _).trans (mul_le_mul hA (norm_zero_fst_le D') (norm_nonneg _)
      (by positivity))
  have h2 : ‖(H' - H) (X, Y') (0, D)‖ ≤ (2 * L₃ * e) * (‖X‖ + ‖Y'‖) := by
    calc ‖(H' - H) (X, Y') (0, D)‖ ≤ ‖(H' - H) (X, Y')‖ * ‖((0 : Ambient n), D)‖ :=
          ((H' - H) (X, Y')).le_opNorm _
      _ ≤ (‖H' - H‖ * ‖((X, Y') : Ambient n × Ambient n)‖) * 2 :=
          mul_le_mul ((H' - H).le_opNorm _) ((norm_zero_fst_le D).trans hD) (norm_nonneg _)
            (by positivity)
      _ ≤ ((L₃ * e) * (‖X‖ + ‖Y'‖)) * 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul hH (norm_pair_le X Y') (norm_nonneg _)
            (by positivity)) (by norm_num)
      _ = (2 * L₃ * e) * (‖X‖ + ‖Y'‖) := by ring
  have h3 : ‖H (0, Y' - Y) (0, D)‖ ≤ (2 * B₂) * ‖Y' - Y‖ := by
    calc ‖H (0, Y' - Y) (0, D)‖ ≤ ‖H (0, Y' - Y)‖ * ‖((0 : Ambient n), D)‖ :=
          (H (0, Y' - Y)).le_opNorm _
      _ ≤ (‖H‖ * ‖Y' - Y‖) * 2 :=
          mul_le_mul ((H.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_zero_fst_le _)
            (norm_nonneg _))) ((norm_zero_fst_le D).trans hD) (norm_nonneg _) (by positivity)
      _ ≤ (B₂ * ‖Y' - Y‖) * 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (norm_nonneg _)) (by norm_num)
      _ = (2 * B₂) * ‖Y' - Y‖ := by ring
  calc _ ≤ ‖(A' - A) (0, D') + (H' - H) (X, Y') (0, D)‖ + ‖H (0, Y' - Y) (0, D)‖ := norm_add_le _ _
    _ ≤ (‖(A' - A) (0, D')‖ + ‖(H' - H) (X, Y') (0, D)‖) + ‖H (0, Y' - Y) (0, D)‖ := by
        gcongr; exact norm_add_le _ _
    _ ≤ ((L₂ * e) * ‖D'‖ + (2 * L₃ * e) * (‖X‖ + ‖Y'‖)) + (2 * B₂) * ‖Y' - Y‖ := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 3200000 in
/-- Lipschitz dependence of the derivative of the superposition operator on the base point,
uniformly on the unit ball of directions. -/
theorem derivData_sub_le (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h' b : Space n, ‖h' - h‖ ≤ 1 → ‖b‖ ≤ 1 →
      ‖derivData hΓ u h' b - derivData hΓ u h b‖ ≤ K * ‖h' - h‖ := by
  set R : ℝ := 2 * (‖u‖ + ‖h‖ + 1) with hRdef
  have hRpos : 0 ≤ R := by positivity
  have hD1 : ContDiff ℝ 2 (fderiv ℝ Γ) := hΓ.fderiv_right (m := 2) (by norm_num)
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ Γ)) := hD1.fderiv_right (m := 1) (by norm_num)
  obtain ⟨L₂, hL₂⟩ := ((hD1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).contDiffOn
    (s := Metric.closedBall (0 : Ambient n × Ambient n) R)).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  obtain ⟨L₃, hL₃⟩ := (hD2.contDiffOn
    (s := Metric.closedBall (0 : Ambient n × Ambient n) R)).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hD2c : ContinuousOn (fun z => ‖fderiv ℝ (fderiv ℝ Γ) z‖)
      (Metric.closedBall (0 : Ambient n × Ambient n) R) := by
    have hc : Continuous (fun z : Ambient n × Ambient n => ‖fderiv ℝ (fderiv ℝ Γ) z‖) :=
      (continuous_norm (E := Ambient n × Ambient n →L[ℝ] (Ambient n × Ambient n →L[ℝ] Ambient n))).comp
        hD2.continuous
    exact hc.continuousOn
  obtain ⟨B₂, hB₂'⟩ := (isCompact_closedBall (0 : Ambient n × Ambient n) R).exists_bound_of_continuousOn
    hD2c
  have hB₂ : ∀ z ∈ Metric.closedBall (0 : Ambient n × Ambient n) R,
      ‖fderiv ℝ (fderiv ℝ Γ) z‖ ≤ B₂ := fun z hz =>
    (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hB₂' z hz)
  have hB₂0 : 0 ≤ B₂ := (norm_nonneg _).trans (hB₂' 0 (Metric.mem_closedBall_self hRpos))
  refine ⟨4 * L₂ + (4 * L₃ * (‖u‖ + ‖h‖ + 1) + 2 * L₂ + 2 * B₂), by positivity,
    fun h' b hh' hb => ?_⟩
  have he0 := norm_nonneg (h' - h)
  have hh'n : ‖h'‖ ≤ ‖h‖ + 1 := by
    have := norm_le_insert' h' h
    linarith
  have hmem : ∀ k : Space n, ‖k‖ ≤ ‖h‖ + 1 → ∀ t ∈ Icc (0 : ℝ) 1,
      ((continuousRepresentative u t, continuousRepresentative k t) : Ambient n × Ambient n) ∈
        Metric.closedBall (0 : Ambient n × Ambient n) R := by
    intro k hk t ht
    rw [mem_closedBall_zero_iff]
    have hu := continuousRepresentative_norm_le_two u ht
    have hkk := continuousRepresentative_norm_le_two k ht
    have hu0 := norm_nonneg u
    have hh0 := norm_nonneg h
    refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
    · change ‖continuousRepresentative u t‖ ≤ R
      rw [hRdef]
      linarith
    · change ‖continuousRepresentative k t‖ ≤ R
      rw [hRdef]
      linarith
  have hdist : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖((continuousRepresentative u t, continuousRepresentative h' t) : Ambient n × Ambient n) -
        (continuousRepresentative u t, continuousRepresentative h t)‖ ≤ 2 * ‖h' - h‖ := by
    intro t ht
    rw [Prod.mk_sub_mk, sub_self]
    exact (norm_zero_fst_le _).trans (rep_sub_norm_le h' h ht)
  have hA : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h' t) -
        fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)‖ ≤
        (L₂ : ℝ) * (2 * ‖h' - h‖) := by
    intro t ht
    have := hL₂.dist_le_mul _ (hmem h' hh'n t ht) _ (hmem h (by linarith) t ht)
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hdist t ht) L₂.2)
  have hH : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ Γ) (continuousRepresentative u t, continuousRepresentative h' t) -
        fderiv ℝ (fderiv ℝ Γ) (continuousRepresentative u t, continuousRepresentative h t)‖ ≤
        (L₃ : ℝ) * (2 * ‖h' - h‖) := by
    intro t ht
    have := hL₃.dist_le_mul _ (hmem h' hh'n t ht) _ (hmem h (by linarith) t ht)
    rw [dist_eq_norm, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hdist t ht) L₃.2)
  have hbt : ∀ t ∈ Icc (0 : ℝ) 1, ‖continuousRepresentative b t‖ ≤ 2 := fun t ht =>
    (continuousRepresentative_norm_le_two b ht).trans (by linarith)
  -- value part
  have hval : ‖value (derivData hΓ u h' b - derivData hΓ u h b)‖ ≤ 4 * L₂ * ‖h' - h‖ := by
    apply value_sub_norm_le (by positivity) (value_derivData_ae hΓ u h' b)
      (value_derivData_ae hΓ u h b)
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    change ‖fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h' t)
        (0, continuousRepresentative b t) -
      fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)
        (0, continuousRepresentative b t)‖ ≤ _
    rw [← sub_apply]
    calc _ ≤ ‖fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h' t) -
          fderiv ℝ Γ (continuousRepresentative u t, continuousRepresentative h t)‖ *
          ‖((0 : Ambient n), continuousRepresentative b t)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ((L₂ : ℝ) * (2 * ‖h' - h‖)) * 2 :=
          mul_le_mul (hA t htI) ((norm_zero_fst_le _).trans (hbt t htI)) (norm_nonneg _)
            (by positivity)
      _ = 4 * L₂ * ‖h' - h‖ := by ring
  -- velocity part
  have hvel : ‖velocity (derivData hΓ u h' b - derivData hΓ u h b)‖ ≤
      (2 * L₃ * (2 * ‖h' - h‖)) * (‖velocity u‖ + ‖velocity h'‖) +
        (L₂ * (2 * ‖h' - h‖)) * ‖velocity b‖ + (2 * B₂) * ‖velocity h' - velocity h‖ := by
    rw [velocity_sub]
    apply norm_le_of_ae_le_sum3 (by positivity) (by positivity) (by positivity)
    filter_upwards [Lp.coeFn_sub (velocity (derivData hΓ u h' b)) (velocity (derivData hΓ u h b)),
      velocity_derivData_ae hΓ u h' b, velocity_derivData_ae hΓ u h b,
      Lp.coeFn_sub (velocity h') (velocity h), ae_restrict_mem measurableSet_Ioo]
      with t h1 h2 h3 h4 ht
    have htI := Ioo_subset_Icc_self ht
    rw [h1, Pi.sub_apply, h2, h3, h4, Pi.sub_apply, partialMap_fderiv_apply hΓ,
      partialMap_fderiv_apply hΓ]
    exact deriv_difference_pointwise (velocity u t) (velocity h t) (velocity h' t)
      (continuousRepresentative b t) (velocity b t) (hA t htI) (hH t htI)
      (hB₂ _ (hmem h (by linarith) t htI)) (hbt t htI) (by positivity) L₂.2 L₃.2
  have hnorm := norm_le_of_value_velocity (by positivity) (by positivity) hval hvel
  have hvu := velocity_norm_le u
  have hvh' : ‖velocity h'‖ ≤ ‖h‖ + 1 := (velocity_norm_le h').trans hh'n
  have hvb : ‖velocity b‖ ≤ 1 := (velocity_norm_le b).trans hb
  have hvd : ‖velocity h' - velocity h‖ ≤ ‖h' - h‖ := by
    calc ‖velocity h' - velocity h‖ = ‖velocity (h' - h)‖ := by rw [velocity_sub]
      _ ≤ ‖h' - h‖ := velocity_norm_le _
  calc _ ≤ 4 * L₂ * ‖h' - h‖ + ((2 * L₃ * (2 * ‖h' - h‖)) * (‖velocity u‖ + ‖velocity h'‖) +
        (L₂ * (2 * ‖h' - h‖)) * ‖velocity b‖ + (2 * B₂) * ‖velocity h' - velocity h‖) := hnorm
    _ ≤ 4 * L₂ * ‖h' - h‖ + ((2 * L₃ * (2 * ‖h' - h‖)) * (‖u‖ + (‖h‖ + 1)) +
        (L₂ * (2 * ‖h' - h‖)) * 1 + (2 * B₂) * ‖h' - h‖) := by gcongr
    _ = _ := by ring

/-- Operator-norm Lipschitz bound for the derivative near a base point. -/
theorem derivL_sub_opNorm_le (hΓ : ContDiff ℝ 3 Γ) (u h : Space n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h' : Space n, ‖h' - h‖ ≤ 1 →
      ‖derivL hΓ u h' - derivL hΓ u h‖ ≤ 2 * K * ‖h' - h‖ := by
  obtain ⟨K, hK0, hK⟩ := derivData_sub_le hΓ u h
  refine ⟨K, hK0, fun h' hh' => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro b
  have hshell := ((derivL hΓ u h' - derivL hΓ u h : Space n →L[ℝ] Space n) :
      Space n →ₗ[ℝ] Space n).bound_of_shell (ε := 1) (C := 2 * K * ‖h' - h‖) one_pos
    (c := (2 : ℝ)) (by norm_num) (fun x hx1 hx2 => ?_) b
  · exact hshell
  · have hhalf : 1 / 2 ≤ ‖x‖ := by
      have h2 : ‖(2 : ℝ)‖ = 2 := by norm_num
      rw [h2] at hx1
      exact hx1
    have hd := hK h' x hh' hx2.le
    change ‖derivData hΓ u h' x - derivData hΓ u h x‖ ≤ 2 * K * ‖h' - h‖ * ‖x‖
    calc _ ≤ K * ‖h' - h‖ := hd
      _ = 2 * K * ‖h' - h‖ * (1 / 2) := by ring
      _ ≤ 2 * K * ‖h' - h‖ * ‖x‖ := by gcongr

/-- The derivative of the superposition operator depends continuously on the base point. -/
theorem derivL_continuous (hΓ : ContDiff ℝ 3 Γ) (u : Space n) :
    Continuous (fun h => derivL hΓ u h) := by
  refine continuous_of_norm_criterion (E := Space n) (F := Space n →L[ℝ] Space n)
    (f := fun h => derivL hΓ u h) ?_
  intro h ε hε
  obtain ⟨K, hK0, hK⟩ := derivL_sub_opNorm_le hΓ u h
  refine ⟨min 1 (ε / (2 * K + 1)), by positivity, fun h' hh' => ?_⟩
  have h1 : ‖h' - h‖ ≤ 1 := (lt_of_lt_of_le hh' (min_le_left _ _)).le
  have h2 : ‖h' - h‖ < ε / (2 * K + 1) := lt_of_lt_of_le hh' (min_le_right _ _)
  have hpos : 0 < 2 * K + 1 := by positivity
  calc ‖derivL hΓ u h' - derivL hΓ u h‖ ≤ 2 * K * ‖h' - h‖ := hK h' h1
    _ ≤ (2 * K + 1) * ‖h' - h‖ := by gcongr; linarith
    _ < (2 * K + 1) * (ε / (2 * K + 1)) := by gcongr
    _ = ε := by field_simp

/-- Superposition operators of C³ maps are C¹ on the original weak H¹ graph. -/
theorem superposition_contDiff (hΓ : ContDiff ℝ 3 Γ) (u : Space n) :
    ContDiff ℝ 1 (fun h => superposition hΓ u h) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun h => (superposition_hasFDerivAt hΓ u h).differentiableAt, ?_⟩
  have hf : fderiv ℝ (fun h => superposition hΓ u h) = fun h => derivL hΓ u h :=
    funext fun h => (superposition_hasFDerivAt hΓ u h).fderiv
  rw [hf]
  exact derivL_continuous hΓ u

theorem chartData_contDiff (u : SphereLoop n) : ContDiff ℝ 1 (chartData u) :=
  superposition_contDiff (ratMap_contDiff3 1) (u.data : Space n)

theorem chartInvSpace_contDiff (u : SphereLoop n) : ContDiff ℝ 1 (chartInvSpace u) :=
  superposition_contDiff stereoG_contDiff3 (u.data : Space n)

/-- Chart transitions are C¹. -/
theorem transition_contDiff (u u' : SphereLoop n) :
    ContDiff ℝ 1 (fun h => chartInvSpace u' (chartData u h)) :=
  (chartInvSpace_contDiff u').comp (chartData_contDiff u)

/-- Radial normalization is C¹. -/
theorem radialData_contDiff : ContDiff ℝ 1 (radialData (n := n)) :=
  superposition_contDiff radial_contDiff3 (0 : Space n)

end

end Finsler.SobolevDerivContinuity
