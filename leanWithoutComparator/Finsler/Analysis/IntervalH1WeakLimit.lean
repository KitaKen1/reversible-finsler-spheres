module

public import Finsler.Geometry.MilnorContinuity
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Topology.UniformSpace.HeineCantor

/-! Strong H¹ convergence from pointwise convergence of the representatives and convergence of
the velocity norms (a Radon–Riesz argument). Pointwise convergence of the representatives with
bounded velocities gives weak convergence of the velocities: against a continuous function the
pairing is a Riemann sum of increments of the representatives up to the oscillation of the
function times the L¹ norm of the velocity, and bounded continuous functions are dense in L².
Weak convergence and convergence of the norms give convergence of ‖v − v₀‖². -/

@[expose] public section

namespace Finsler.SobolevWeakLimit

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevEnergyDifferential
open Finsler.MilnorContinuity
open MeasureTheory Set Filter Finset
open scoped Topology ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

theorem velocity_intervalIntegrable_of_mem (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) : IntervalIntegrable (velocity u) volume s t := by
  apply (velocity_intervalIntegrable u).mono_set
  rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
  exact uIcc_subset_Icc hs ht

theorem integral_norm_velocity_le (u : Space n) :
    ∫ t in (0 : ℝ)..1, ‖velocity u t‖ ≤ (1 + ‖velocity u‖ ^ 2) / 2 := by
  have hsq : ∫ t in (0 : ℝ)..1, ‖velocity u t‖ ^ 2 = ‖velocity u‖ ^ 2 := by
    rw [lp_two_norm_eq_sqrt_integral_norm_sq, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
      intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    rfl
  have hi1 : IntervalIntegrable (fun t => ‖velocity u t‖) volume 0 1 :=
    (velocity_intervalIntegrable u).norm
  have hi2 : IntervalIntegrable (fun t => ‖velocity u t‖ ^ 2) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mpr
    exact integrable_velocity_sq u
  have hle : ∫ t in (0 : ℝ)..1, ‖velocity u t‖ ≤
      ∫ t in (0 : ℝ)..1, (1 + ‖velocity u t‖ ^ 2) / 2 := by
    apply intervalIntegral.integral_mono_on zero_le_one hi1
      ((intervalIntegrable_const.add hi2).div_const 2)
    intro t _
    nlinarith [sq_nonneg (‖velocity u t‖ - 1)]
  have hR : ∫ t in (0 : ℝ)..1, (1 + ‖velocity u t‖ ^ 2) / 2 = (1 + ‖velocity u‖ ^ 2) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const hi2,
      intervalIntegral.integral_const, hsq]
    simp
  linarith

theorem inner_increment_eq (u : Space n) {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) (c : Ambient n) :
    ⟪continuousRepresentative u t - continuousRepresentative u s, c⟫ =
      ∫ x in s..t, ⟪velocity u x, c⟫ := by
  rw [continuousRepresentative_sub u hs ht, real_inner_comm]
  have h := ((innerSL ℝ c).intervalIntegral_comp_comm
    (velocity_intervalIntegrable_of_mem u hs ht)).symm
  simp only [innerSL_apply_apply] at h
  rw [h]
  apply intervalIntegral.integral_congr
  intro x _
  exact real_inner_comm _ _

/-- The pairing with a continuous function is a Riemann sum of increments up to the
oscillation of the function times the L¹ norm of the velocity. -/
theorem riemann_bound (u : Space n) {g : ℝ → Ambient n} (hg : Continuous g) {N : ℕ}
    (hN : 0 < N) {δ : ℝ}
    (hδ : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| ≤ 1 / N → ‖g s - g t‖ ≤ δ) :
    |(∫ t in (0 : ℝ)..1, ⟪velocity u t, g t⟫) -
        ∑ k ∈ range N, ⟪continuousRepresentative u (((k : ℝ) + 1) / N) -
          continuousRepresentative u ((k : ℝ) / N), g ((k : ℝ) / N)⟫| ≤
      δ * ∫ t in (0 : ℝ)..1, ‖velocity u t‖ := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  set a : ℕ → ℝ := fun k => (k : ℝ) / N with ha
  have ha0 : a 0 = 0 := by simp [ha]
  have haN : a N = 1 := by simp only [ha]; exact div_self hNr.ne'
  have hsucc (k : ℕ) : a (k + 1) = ((k : ℝ) + 1) / N := by simp [ha]
  have hmem : ∀ k ≤ N, a k ∈ Icc (0 : ℝ) 1 := by
    intro k hk
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hNr]
    exact_mod_cast hk
  have hle (k : ℕ) : a k ≤ a (k + 1) := by
    simp only [ha]
    gcongr
    norm_num
  have hstep (k : ℕ) : a (k + 1) - a k = 1 / N := by
    simp only [ha]
    push_cast
    ring
  have hvi (k : ℕ) (hk : k < N) : IntervalIntegrable (velocity u) volume (a k) (a (k + 1)) :=
    velocity_intervalIntegrable_of_mem u (hmem k hk.le) (hmem (k + 1) hk)
  have hpair (k : ℕ) (hk : k < N) (c : ℝ → Ambient n) (hc : ContinuousOn c (Icc 0 1)) :
      IntervalIntegrable (fun t => ⟪velocity u t, c t⟫) volume (a k) (a (k + 1)) := by
    obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    have hsub : uIcc (a k) (a (k + 1)) ⊆ Icc (0 : ℝ) 1 := uIcc_subset_Icc (hmem k hk.le)
      (hmem (k + 1) hk)
    refine (intervalIntegrable_iff.mpr ?_)
    refine Integrable.mono' ((hvi k hk).def'.norm.const_mul D) ?_ ?_
    · exact (Lp.stronglyMeasurable (velocity u)).aestronglyMeasurable.inner
        ((hc.mono (uIoc_subset_uIcc.trans hsub)).aestronglyMeasurable measurableSet_uIoc)
    · rw [ae_restrict_iff' measurableSet_uIoc]
      filter_upwards with t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := hsub (uIoc_subset_uIcc ht)
      calc ‖⟪velocity u t, c t⟫‖ ≤ ‖velocity u t‖ * ‖c t‖ := by
            rw [Real.norm_eq_abs]
            exact abs_real_inner_le_norm _ _
        _ ≤ D * ‖velocity u t‖ := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_right (hD t htI) (norm_nonneg _)
  have hsum1 : ∫ t in (0 : ℝ)..1, ⟪velocity u t, g t⟫ =
      ∑ k ∈ range N, ∫ t in (a k)..(a (k + 1)), ⟪velocity u t, g t⟫ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k hk => hpair k hk g hg.continuousOn), ha0, haN]
  have hsum2 : ∫ t in (0 : ℝ)..1, ‖velocity u t‖ =
      ∑ k ∈ range N, ∫ t in (a k)..(a (k + 1)), ‖velocity u t‖ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k hk => (hvi k hk).norm), ha0, haN]
  have hterm (k : ℕ) (hk : k ∈ range N) :
      ⟪continuousRepresentative u (((k : ℝ) + 1) / N) - continuousRepresentative u ((k : ℝ) / N),
        g ((k : ℝ) / N)⟫ = ∫ t in (a k)..(a (k + 1)), ⟪velocity u t, g (a k)⟫ := by
    have hk' := Finset.mem_range.mp hk
    rw [← hsucc k]
    exact inner_increment_eq u (hmem k hk'.le) (hmem (k + 1) hk') _
  rw [hsum1, hsum2, Finset.sum_congr rfl hterm, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk' := Finset.mem_range.mp hk
  rw [← intervalIntegral.integral_sub (hpair k hk' g hg.continuousOn)
    (hpair k hk' (fun _ => g (a k)) continuousOn_const), ← Real.norm_eq_abs,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.norm_integral_le_of_norm_le (hle k)
  · filter_upwards with t ht
    have hsub : Ioc (a k) (a (k + 1)) ⊆ Icc (0 : ℝ) 1 :=
      Ioc_subset_Icc_self.trans (Icc_subset_Icc (hmem k hk'.le).1 (hmem (k + 1) hk').2)
    have htI := hsub ht
    have hdist : |t - a k| ≤ 1 / N := by
      rw [abs_of_nonneg (by linarith [ht.1]), ← hstep k]
      linarith [ht.2]
    rw [← inner_sub_right, Real.norm_eq_abs]
    calc |⟪velocity u t, g t - g (a k)⟫| ≤ ‖velocity u t‖ * ‖g t - g (a k)‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖velocity u t‖ * δ :=
          mul_le_mul_of_nonneg_left (hδ t htI (a k) (hmem k hk'.le) hdist) (norm_nonneg _)
      _ = δ * ‖velocity u t‖ := mul_comm _ _
  · exact (hvi k hk').norm.const_mul δ

theorem intervalMeasure_weaklyRegular : (intervalMeasure : Measure ℝ).WeaklyRegular := by
  change (volume.restrict (Ioo (0 : ℝ) 1)).WeaklyRegular
  infer_instance

/-- Velocities of graph elements whose representatives tend to zero pointwise and whose
velocities are bounded tend to zero weakly. -/
theorem tendsto_inner_velocity_zero {X : Type*} {l : Filter X} {h : X → Space n} {M : ℝ}
    (hrep : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun x => continuousRepresentative (h x) t) l (𝓝 0))
    (hbd : ∀ᶠ x in l, ‖velocity (h x)‖ ≤ M) (B : ValueLp n) :
    Tendsto (fun x => ⟪velocity (h x), B⟫) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set M' : ℝ := max M 0 with hM'
  have hM'0 : 0 ≤ M' := le_max_right _ _
  set K : ℝ := M' + 1 + (1 + M' ^ 2) / 2 + 1 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := ε / K with hδdef
  have hδ : 0 < δ := div_pos hε hKpos
  have := intervalMeasure_weaklyRegular
  obtain ⟨g, hgB, hgm⟩ := (Lp.memLp B).exists_boundedContinuous_eLpNorm_sub_le
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (ENNReal.ofReal_pos.mpr hδ).ne'
  obtain ⟨G, hG⟩ : ∃ G : ValueLp n, G = hgm.toLp g := ⟨_, rfl⟩
  have hGae : (G : ℝ → Ambient n) =ᵐ[intervalMeasure] g := by
    rw [hG]
    exact hgm.coeFn_toLp
  have hBG : ‖B - G‖ ≤ δ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub B G)]
    have hcongr : (⇑B - ⇑G) =ᵐ[intervalMeasure] (⇑B - (g : ℝ → Ambient n)) := by
      filter_upwards [hGae] with t ht
      simp only [Pi.sub_apply, ht]
    rw [eLpNorm_congr_ae hcongr]
    exact ENNReal.toReal_le_of_le_ofReal hδ.le hgB
  have hpair (x : X) : ⟪velocity (h x), G⟫ = ∫ t in (0 : ℝ)..1, ⟪velocity (h x) t, g t⟫ := by
    rw [MeasureTheory.L2.inner_def, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [hGae] with t ht
    rw [ht]
  obtain ⟨η, hη, hηg⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous g.continuous.continuousOn) δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  have hN1 : 0 < N + 1 := Nat.succ_pos N
  have hδg : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| ≤ 1 / ((N + 1 : ℕ) : ℝ) →
      ‖g s - g t‖ ≤ δ := by
    intro s hs t ht hst
    have hd : dist s t < η := by
      rw [Real.dist_eq]
      refine lt_of_le_of_lt hst ?_
      push_cast
      exact hN
    rw [← dist_eq_norm]
    exact (hηg s hs t ht hd).le
  have hmemk (k : ℕ) (hk : k ≤ N + 1) : ((k : ℝ) / ((N + 1 : ℕ) : ℝ)) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    exact_mod_cast hk
  have hsum : Tendsto (fun x => ∑ k ∈ range (N + 1),
      ⟪continuousRepresentative (h x) (((k : ℝ) + 1) / ((N + 1 : ℕ) : ℝ)) -
        continuousRepresentative (h x) ((k : ℝ) / ((N + 1 : ℕ) : ℝ)),
        g ((k : ℝ) / ((N + 1 : ℕ) : ℝ))⟫) l (𝓝 0) := by
    have h0 : (0 : ℝ) = ∑ k ∈ range (N + 1),
        ⟪(0 : Ambient n) - 0, g ((k : ℝ) / ((N + 1 : ℕ) : ℝ))⟫ := by simp
    rw [h0]
    apply tendsto_finsetSum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hk1 : ((k : ℝ) + 1) / ((N + 1 : ℕ) : ℝ) ∈ Icc (0 : ℝ) 1 := by
      have := hmemk (k + 1) hk'
      push_cast at this ⊢
      exact this
    exact ((hrep _ hk1).sub (hrep _ (hmemk k hk'.le))).inner tendsto_const_nhds
  filter_upwards [hbd, (Metric.tendsto_nhds.mp hsum) δ hδ] with x hx hxs
  rw [Real.dist_eq, sub_zero] at hxs ⊢
  have hvx : ‖velocity (h x)‖ ≤ M' := hx.trans (le_max_left _ _)
  have h1 : |⟪velocity (h x), B - G⟫| ≤ M' * δ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hvx hBG (norm_nonneg _) hM'0)
  have h2 := riemann_bound (h x) g.continuous hN1 hδg
  have h3 := integral_norm_velocity_le (h x)
  have hsq : ‖velocity (h x)‖ ^ 2 ≤ M' ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvx 2
  have hsplit : ⟪velocity (h x), B⟫ = ⟪velocity (h x), B - G⟫ + ⟪velocity (h x), G⟫ := by
    rw [inner_sub_right]
    ring
  rw [hsplit, hpair x]
  set S := ∑ k ∈ range (N + 1),
      ⟪continuousRepresentative (h x) (((k : ℝ) + 1) / ((N + 1 : ℕ) : ℝ)) -
        continuousRepresentative (h x) ((k : ℝ) / ((N + 1 : ℕ) : ℝ)),
        g ((k : ℝ) / ((N + 1 : ℕ) : ℝ))⟫ with hS
  set I := ∫ t in (0 : ℝ)..1, ⟪velocity (h x) t, g t⟫ with hI
  set J := ∫ t in (0 : ℝ)..1, ‖velocity (h x) t‖ with hJ
  have hJb : J ≤ (1 + M' ^ 2) / 2 := by linarith
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _
  have hI : |I| ≤ |S| + δ * J := by
    have := abs_sub_abs_le_abs_sub I S
    linarith
  have hδJ : δ * J ≤ δ * ((1 + M' ^ 2) / 2) := mul_le_mul_of_nonneg_left hJb hδ.le
  calc |⟪velocity (h x), B - G⟫ + I| ≤ |⟪velocity (h x), B - G⟫| + |I| := abs_add_le _ _
    _ < M' * δ + (δ + δ * ((1 + M' ^ 2) / 2)) + δ := by linarith
    _ = δ * K := by rw [hK]; ring
    _ = ε := by rw [hδdef]; field_simp

/-- Weak convergence of the velocities. -/
theorem tendsto_inner_velocity {X : Type*} {l : Filter X} {w : X → Space n} {w₀ : Space n}
    {M : ℝ}
    (hrep : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun x => continuousRepresentative (w x) t) l
      (𝓝 (continuousRepresentative w₀ t)))
    (hbd : ∀ᶠ x in l, ‖velocity (w x)‖ ≤ M) (B : ValueLp n) :
    Tendsto (fun x => ⟪velocity (w x), B⟫) l (𝓝 ⟪velocity w₀, B⟫) := by
  have hrep' : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun x => continuousRepresentative (w x - w₀) t) l (𝓝 0) := by
    intro t ht
    have hsub (x : X) : continuousRepresentative (w x - w₀) t =
        continuousRepresentative (w x) t - continuousRepresentative w₀ t := by
      exact (traceL n ⟨t, ht⟩).map_sub (w x) w₀
    have h := (hrep t ht).sub_const (continuousRepresentative w₀ t)
    simp only [sub_self] at h
    refine h.congr ?_
    intro x
    exact (hsub x).symm
  have hvel (x : X) : velocity (w x - w₀) = velocity (w x) - velocity w₀ :=
    (velocityL n).map_sub _ _
  have hbd' : ∀ᶠ x in l, ‖velocity (w x - w₀)‖ ≤ M + ‖velocity w₀‖ := by
    filter_upwards [hbd] with x hx
    calc ‖velocity (w x - w₀)‖ = ‖velocity (w x) - velocity w₀‖ := congrArg norm (hvel x)
      _ ≤ ‖velocity (w x)‖ + ‖velocity w₀‖ := norm_sub_le _ _
      _ ≤ M + ‖velocity w₀‖ := by linarith
  have h := (tendsto_inner_velocity_zero hrep' hbd' B).add_const ⟪velocity w₀, B⟫
  simp only [zero_add] at h
  refine h.congr fun x => ?_
  calc ⟪velocity (w x - w₀), B⟫ + ⟪velocity w₀, B⟫ =
      ⟪velocity (w x) - velocity w₀, B⟫ + ⟪velocity w₀, B⟫ :=
        congrArg (fun v => ⟪v, B⟫ + ⟪velocity w₀, B⟫) (hvel x)
    _ = (⟪velocity (w x), B⟫ - ⟪velocity w₀, B⟫) + ⟪velocity w₀, B⟫ :=
        congrArg (· + ⟪velocity w₀, B⟫) (inner_sub_left _ _ _)
    _ = ⟪velocity (w x), B⟫ := sub_add_cancel _ _

/-- Radon–Riesz: pointwise convergence of the representatives and convergence of the velocity
norms give convergence of the velocities. -/
theorem tendsto_velocity_of_norm {X : Type*} {l : Filter X} {w : X → Space n} {w₀ : Space n}
    (hrep : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun x => continuousRepresentative (w x) t) l
      (𝓝 (continuousRepresentative w₀ t)))
    (hnorm : Tendsto (fun x => ‖velocity (w x)‖) l (𝓝 ‖velocity w₀‖)) :
    Tendsto (fun x => velocity (w x)) l (𝓝 (velocity w₀)) := by
  have hbd : ∀ᶠ x in l, ‖velocity (w x)‖ ≤ ‖velocity w₀‖ + 1 :=
    hnorm.eventually (ge_mem_nhds (by linarith))
  have hin := tendsto_inner_velocity hrep hbd (velocity w₀)
  rw [real_inner_self_eq_norm_sq] at hin
  have hsq : Tendsto (fun x => ‖velocity (w x) - velocity w₀‖ ^ 2) l (𝓝 0) := by
    have h := ((hnorm.pow 2).sub (hin.const_mul 2)).add_const (‖velocity w₀‖ ^ 2)
    have hlim : ‖velocity w₀‖ ^ 2 - 2 * ‖velocity w₀‖ ^ 2 + ‖velocity w₀‖ ^ 2 = 0 := by ring
    rw [hlim] at h
    refine h.congr fun x => ?_
    rw [norm_sub_sq_real]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hs
  refine hs.congr fun x => ?_
  simp only [Function.comp_apply]
  exact Real.sqrt_sq (norm_nonneg _)

/-- Strong convergence in the graph space. -/
theorem tendsto_of_representative_norm {X : Type*} {l : Filter X} {w : X → Space n}
    {w₀ : Space n}
    (hrep : ∀ t ∈ Icc (0 : ℝ) 1, Tendsto (fun x => continuousRepresentative (w x) t) l
      (𝓝 (continuousRepresentative w₀ t)))
    (hnorm : Tendsto (fun x => ‖velocity (w x)‖) l (𝓝 ‖velocity w₀‖)) :
    Tendsto w l (𝓝 w₀) :=
  tendsto_of_trace_velocity (hrep 0 ⟨le_rfl, zero_le_one⟩) (tendsto_velocity_of_norm hrep hnorm)

end

end Finsler.SobolevWeakLimit
