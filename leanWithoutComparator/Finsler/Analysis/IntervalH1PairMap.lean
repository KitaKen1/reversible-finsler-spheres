module

public import Finsler.Analysis.IntervalH1OfPrimitive
public import Finsler.Analysis.IntervalH1CurveRealization

/-! One-dimensional superposition: a C¹ map Γ of a pair of original weak H¹ graph
elements is a graph element, with value Γ of the continuous representatives and weak
velocity the derivative of Γ applied to the pair of weak velocities, certified by the
one-dimensional chain rule. The superposition operator is continuous in the original H¹
topology: values are controlled through the uniform bound of representatives and a
Lipschitz constant of Γ on a compact ball, velocities through a bound and the uniform
continuity of the derivative of Γ on that ball, with L² Minkowski control. -/

@[expose] public section

namespace Finsler.SobolevPairMap

open Finsler.SphereGeometry Finsler.IntervalSobolev Finsler.SobolevOfPrimitive
open Finsler.SobolevCurveFamily Finsler.SobolevCurveRealization Finsler.IntervalChainRule
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

set_option maxHeartbeats 400000

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

/-- The scalar L² function of pointwise norms. -/
def normLp (g : ValueLp n) : Lp ℝ 2 intervalMeasure := (Lp.memLp g).norm.toLp (fun t => ‖g t‖)

theorem normLp_ae (g : ValueLp n) : normLp g =ᵐ[intervalMeasure] fun t => ‖g t‖ :=
  (Lp.memLp g).norm.coeFn_toLp

theorem norm_normLp (g : ValueLp n) : ‖normLp g‖ = ‖g‖ := by
  rw [normLp, Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable g), Lp.norm_def]

/-- Minkowski control from a two-term pointwise bound by four L² functions. -/
theorem norm_le_of_ae_le_sum {f a b c d : ValueLp n} {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (h : ∀ᵐ t ∂intervalMeasure, ‖f t‖ ≤ c₁ * (‖a t‖ + ‖b t‖) + c₂ * (‖c t‖ + ‖d t‖)) :
    ‖f‖ ≤ c₁ * (‖a‖ + ‖b‖) + c₂ * (‖c‖ + ‖d‖) := by
  have hG : ∀ᵐ t ∂intervalMeasure,
      (c₁ • (normLp a + normLp b) + c₂ • (normLp c + normLp d) : Lp ℝ 2 intervalMeasure) t =
        c₁ * (‖a t‖ + ‖b t‖) + c₂ * (‖c t‖ + ‖d t‖) := by
    filter_upwards [Lp.coeFn_add (c₁ • (normLp a + normLp b)) (c₂ • (normLp c + normLp d)),
      Lp.coeFn_smul c₁ (normLp a + normLp b), Lp.coeFn_smul c₂ (normLp c + normLp d),
      Lp.coeFn_add (normLp a) (normLp b), Lp.coeFn_add (normLp c) (normLp d),
      normLp_ae a, normLp_ae b, normLp_ae c, normLp_ae d] with t h1 h2 h3 h4 h5 ha hb hc hd
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5, Pi.add_apply,
      Pi.add_apply, ha, hb, hc, hd, smul_eq_mul, smul_eq_mul]
  have hle : ‖f‖ ≤ ‖(c₁ • (normLp a + normLp b) + c₂ • (normLp c + normLp d) :
      Lp ℝ 2 intervalMeasure)‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [h, hG] with t ht hGt
    rw [hGt, Real.norm_of_nonneg (by positivity)]
    exact ht
  refine hle.trans ((norm_add_le _ _).trans ?_)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hc₁, Real.norm_of_nonneg hc₂,
    ← norm_normLp a, ← norm_normLp b, ← norm_normLp c, ← norm_normLp d]
  gcongr <;> exact norm_add_le _ _

variable {Γ : Ambient n × Ambient n → Ambient n}

theorem mapValue_continuousOn (hΓ : ContDiff ℝ 1 Γ) (u h : Space n) :
    ContinuousOn (fun t => Γ (pairRep u h t)) (Icc 0 1) :=
  hΓ.continuous.comp_continuousOn (pairRep_continuousOn u h)

theorem mapVelocity_memLp (hΓ : ContDiff ℝ 1 Γ) (u h : Space n) :
    MemLp (fun t => fderiv ℝ Γ (pairRep u h t) (pairVel u h t)) 2 intervalMeasure := by
  have hD : ContinuousOn (fun s => fderiv ℝ Γ (pairRep u h s)) (Icc 0 1) :=
    (hΓ.continuous_fderiv (by norm_num)).comp_continuousOn (pairRep_continuousOn u h)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hmeas : AEStronglyMeasurable (fun t => fderiv ℝ Γ (pairRep u h t) (pairVel u h t))
      intervalMeasure := by
    have he : Continuous (fun p : (Ambient n × Ambient n →L[ℝ] Ambient n) ×
        (Ambient n × Ambient n) => p.1 p.2) := continuous_fst.clm_apply continuous_snd
    have hD' : AEStronglyMeasurable (fun s => fderiv ℝ Γ (pairRep u h s)) intervalMeasure :=
      (hD.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo
    have hV : AEStronglyMeasurable (pairVel u h) intervalMeasure :=
      (Lp.aestronglyMeasurable (velocity u)).prodMk (Lp.aestronglyMeasurable (velocity h))
    exact he.comp_aestronglyMeasurable (hD'.prodMk hV)
  refine (velocitySum_memLp u h).of_le_mul (c := C) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  have h2 := hC s (Ioo_subset_Icc_self hs)
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    ‖fderiv ℝ Γ (pairRep u h s) (pairVel u h s)‖ ≤
        ‖fderiv ℝ Γ (pairRep u h s)‖ * ‖pairVel u h s‖ := (fderiv ℝ Γ (pairRep u h s)).le_opNorm _
    _ ≤ C * (‖velocity u s‖ + ‖velocity h s‖) :=
      mul_le_mul h2 (norm_pairVel_le u h s) (norm_nonneg _) ((norm_nonneg _).trans h2)

theorem mapValue_prim (hΓ : ContDiff ℝ 1 Γ) (u h : Space n) :
    ∀ t ∈ Icc (0 : ℝ) 1, Γ (pairRep u h t) =
      Γ (pairRep u h 0) + ∫ s in (0 : ℝ)..t, fderiv ℝ Γ (pairRep u h s) (pairVel u h s) := by
  intro t ht
  have hc := comp_sub_eq_integral hΓ (pairVel_intervalIntegrable u h)
    (fun t ht => pairRep_eq_add_integral u h ht) (pairRep_hasDerivAt_ae u h) ht
  rw [← hc]
  abel

/-- A C¹ map of a pair of graph elements, as a graph element (H¹ is closed under C¹ maps
in one dimension). -/
def mapData (hΓ : ContDiff ℝ 1 Γ) (u h : Space n) : Space n :=
  ofPrimitive (mapValue_continuousOn hΓ u h) (mapVelocity_memLp hΓ u h) (mapValue_prim hΓ u h)

theorem value_mapData_ae (hΓ : ContDiff ℝ 1 Γ) (u h : Space n) :
    value (mapData hΓ u h) =ᵐ[intervalMeasure] fun t => Γ (pairRep u h t) :=
  value_ofPrimitive_ae _ _ _

theorem velocity_mapData_ae (hΓ : ContDiff ℝ 1 Γ) (u h : Space n) :
    velocity (mapData hΓ u h) =ᵐ[intervalMeasure]
      fun t => fderiv ℝ Γ (pairRep u h t) (pairVel u h t) :=
  velocity_ofPrimitive_ae _ _ _

theorem representative_mapData (hΓ : ContDiff ℝ 1 Γ) (u h : Space n) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative (mapData hΓ u h) t = Γ (pairRep u h t) :=
  representative_ofPrimitive _ _ _ ht

theorem mapData_periodic (hΓ : ContDiff ℝ 1 Γ) {u h : Space n} (hu : u ∈ periodicSubmodule n)
    (hh : h ∈ periodicSubmodule n) : mapData hΓ u h ∈ periodicSubmodule n := by
  apply ofPrimitive_periodic
  rw [mem_periodicSubmodule_iff] at hu hh
  change continuousRepresentative u 1 = continuousRepresentative u 0 at hu
  change continuousRepresentative h 1 = continuousRepresentative h 0 at hh
  simp only [pairRep, hu, hh]

theorem value_sub (a b : Space n) : value (a - b) = value a - value b := by
  change valueL n (a - b) = valueL n a - valueL n b
  exact (valueL n).map_sub a b

theorem velocity_sub (a b : Space n) : velocity (a - b) = velocity a - velocity b := by
  change velocityL n (a - b) = velocityL n a - velocityL n b
  exact (velocityL n).map_sub a b

theorem value_sub_norm_le {X Y : Space n} {x y : ℝ → Ambient n} {C : ℝ} (hC : 0 ≤ C)
    (hx : value X =ᵐ[intervalMeasure] x) (hy : value Y =ᵐ[intervalMeasure] y)
    (h : ∀ t ∈ Ioo (0 : ℝ) 1, ‖x t - y t‖ ≤ C) : ‖value (X - Y)‖ ≤ C := by
  rw [value_sub]
  apply valueLp_norm_le_of_ae_bound hC
  filter_upwards [Lp.coeFn_sub (value X) (value Y), hx, hy, ae_restrict_mem measurableSet_Ioo]
    with t h1 h2 h3 ht
  rw [h1, Pi.sub_apply, h2, h3]
  exact h t ht

theorem velocity_sub_norm_le {X Y : Space n} {x y : ℝ → Ambient n} {a b c d : ValueLp n}
    {c₁ c₂ : ℝ} (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hx : velocity X =ᵐ[intervalMeasure] x) (hy : velocity Y =ᵐ[intervalMeasure] y)
    (h : ∀ᵐ t ∂intervalMeasure,
      ‖x t - y t‖ ≤ c₁ * (‖a t‖ + ‖b t‖) + c₂ * (‖c t‖ + ‖d t‖)) :
    ‖velocity (X - Y)‖ ≤ c₁ * (‖a‖ + ‖b‖) + c₂ * (‖c‖ + ‖d‖) := by
  rw [velocity_sub]
  apply norm_le_of_ae_le_sum hc₁ hc₂
  filter_upwards [Lp.coeFn_sub (velocity X) (velocity Y), hx, hy, h] with t h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, h3]
  exact h4

theorem rep_sub_norm_le (u v : Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖continuousRepresentative u t - continuousRepresentative v t‖ ≤ 2 * ‖u - v‖ := by
  have h1 : continuousRepresentative u t - continuousRepresentative v t =
      continuousRepresentative (u - v) t := by
    have h := (traceL n ⟨t, ht⟩).map_sub u v
    rw [traceL_apply, traceL_apply, traceL_apply] at h
    exact h.symm
  rw [h1]
  exact continuousRepresentative_norm_le_two (u - v) ht

theorem pairRep_norm_le (p : Space n × Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖pairRep p.1 p.2 t‖ ≤ 2 * ‖p‖ := by
  refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
  · exact (continuousRepresentative_norm_le_two p.1 ht).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le p) (by norm_num))
  · exact (continuousRepresentative_norm_le_two p.2 ht).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le p) (by norm_num))

theorem pairRep_sub_norm_le (p q : Space n × Space n) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖pairRep p.1 p.2 t - pairRep q.1 q.2 t‖ ≤ 2 * ‖p - q‖ := by
  have e : pairRep p.1 p.2 t - pairRep q.1 q.2 t =
      (continuousRepresentative p.1 t - continuousRepresentative q.1 t,
        continuousRepresentative p.2 t - continuousRepresentative q.2 t) := Prod.mk_sub_mk _ _ _ _
  rw [e]
  refine norm_prod_le_iff.mpr ⟨?_, ?_⟩
  · exact (rep_sub_norm_le p.1 q.1 ht).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le (p - q)) (by norm_num))
  · exact (rep_sub_norm_le p.2 q.2 ht).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le (p - q)) (by norm_num))

/-- Pointwise control of the velocity difference of two C¹ pair maps. -/
theorem velocity_pointwise {A A₀ : Ambient n × Ambient n →L[ℝ] Ambient n}
    {W W₀ : Ambient n × Ambient n} {a b c d B η : ℝ} (hB : ‖A‖ ≤ B) (hη : ‖A - A₀‖ ≤ η)
    (hW : ‖W - W₀‖ ≤ a + b) (hW₀ : ‖W₀‖ ≤ c + d) (hB0 : 0 ≤ B) (hη0 : 0 ≤ η) :
    ‖A W - A₀ W₀‖ ≤ B * (a + b) + η * (c + d) := by
  have e : A W - A₀ W₀ = A (W - W₀) + (A - A₀) W₀ := by
    rw [map_sub, sub_apply]
    abel
  rw [e]
  calc
    ‖A (W - W₀) + (A - A₀) W₀‖ ≤ ‖A (W - W₀)‖ + ‖(A - A₀) W₀‖ := norm_add_le _ _
    _ ≤ ‖A‖ * ‖W - W₀‖ + ‖A - A₀‖ * ‖W₀‖ :=
      add_le_add (A.le_opNorm _) ((A - A₀).le_opNorm _)
    _ ≤ B * (a + b) + η * (c + d) :=
      add_le_add (mul_le_mul hB hW (norm_nonneg _) hB0) (mul_le_mul hη hW₀ (norm_nonneg _) hη0)

/-- The closed-form H¹ difference estimate for C¹ pair maps. -/
theorem mapData_sub_le (hΓ : ContDiff ℝ 1 Γ) (p p₀ : Space n × Space n) {R LΓ B η : ℝ}
    (hRp : ‖p‖ ≤ R / 2) (hRp₀ : ‖p₀‖ ≤ R / 2)
    (hL : ∀ a ∈ Metric.closedBall (0 : Ambient n × Ambient n) R,
      ∀ b ∈ Metric.closedBall (0 : Ambient n × Ambient n) R, ‖Γ a - Γ b‖ ≤ LΓ * ‖a - b‖)
    (hL0 : 0 ≤ LΓ)
    (hB : ∀ a ∈ Metric.closedBall (0 : Ambient n × Ambient n) R, ‖fderiv ℝ Γ a‖ ≤ B)
    (hB0 : 0 ≤ B)
    (hη : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ Γ (pairRep p.1 p.2 t) - fderiv ℝ Γ (pairRep p₀.1 p₀.2 t)‖ ≤ η)
    (hη0 : 0 ≤ η) :
    ‖mapData hΓ p.1 p.2 - mapData hΓ p₀.1 p₀.2‖ ≤
      LΓ * (2 * ‖p - p₀‖) + (B * (‖p - p₀‖ + ‖p - p₀‖) +
        η * (‖velocity p₀.1‖ + ‖velocity p₀.2‖)) := by
  have hmem : ∀ q : Space n × Space n, ‖q‖ ≤ R / 2 → ∀ t ∈ Icc (0 : ℝ) 1,
      pairRep q.1 q.2 t ∈ Metric.closedBall (0 : Ambient n × Ambient n) R := by
    intro q hq t ht
    rw [mem_closedBall_zero_iff]
    exact (pairRep_norm_le q ht).trans (by linarith)
  have hval : ‖value (mapData hΓ p.1 p.2 - mapData hΓ p₀.1 p₀.2)‖ ≤ LΓ * (2 * ‖p - p₀‖) := by
    apply value_sub_norm_le (by positivity) (value_mapData_ae hΓ p.1 p.2)
      (value_mapData_ae hΓ p₀.1 p₀.2)
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    exact (hL _ (hmem p hRp t htI) _ (hmem p₀ hRp₀ t htI)).trans
      (mul_le_mul_of_nonneg_left (pairRep_sub_norm_le p p₀ htI) hL0)
  have hvel : ‖velocity (mapData hΓ p.1 p.2 - mapData hΓ p₀.1 p₀.2)‖ ≤
      B * (‖velocity p.1 - velocity p₀.1‖ + ‖velocity p.2 - velocity p₀.2‖) +
        η * (‖velocity p₀.1‖ + ‖velocity p₀.2‖) := by
    apply velocity_sub_norm_le hB0 hη0 (velocity_mapData_ae hΓ p.1 p.2)
      (velocity_mapData_ae hΓ p₀.1 p₀.2)
    filter_upwards [Lp.coeFn_sub (velocity p.1) (velocity p₀.1),
      Lp.coeFn_sub (velocity p.2) (velocity p₀.2), ae_restrict_mem measurableSet_Ioo]
      with t h1 h2 ht
    have htI := Ioo_subset_Icc_self ht
    rw [h1, h2, Pi.sub_apply, Pi.sub_apply]
    apply velocity_pointwise (hB _ (hmem p hRp t htI)) (hη t htI) _
      (norm_pairVel_le p₀.1 p₀.2 t) hB0 hη0
    have e2 : pairVel p.1 p.2 t - pairVel p₀.1 p₀.2 t =
        (velocity p.1 t - velocity p₀.1 t, velocity p.2 t - velocity p₀.2 t) :=
      Prod.mk_sub_mk _ _ _ _
    rw [e2]
    exact norm_prod_le_iff.mpr ⟨le_add_of_nonneg_right (norm_nonneg _),
      le_add_of_nonneg_left (norm_nonneg _)⟩
  have hv1 : ‖velocity p.1 - velocity p₀.1‖ ≤ ‖p - p₀‖ := by
    calc ‖velocity p.1 - velocity p₀.1‖ = ‖velocity (p.1 - p₀.1)‖ := by rw [velocity_sub]
      _ ≤ ‖p.1 - p₀.1‖ := velocity_norm_le _
      _ ≤ ‖p - p₀‖ := norm_fst_le (p - p₀)
  have hv2 : ‖velocity p.2 - velocity p₀.2‖ ≤ ‖p - p₀‖ := by
    calc ‖velocity p.2 - velocity p₀.2‖ = ‖velocity (p.2 - p₀.2)‖ := by rw [velocity_sub]
      _ ≤ ‖p.2 - p₀.2‖ := velocity_norm_le _
      _ ≤ ‖p - p₀‖ := norm_snd_le (p - p₀)
  have hvel' : ‖velocity (mapData hΓ p.1 p.2 - mapData hΓ p₀.1 p₀.2)‖ ≤
      B * (‖p - p₀‖ + ‖p - p₀‖) + η * (‖velocity p₀.1‖ + ‖velocity p₀.2‖) :=
    hvel.trans (by gcongr)
  exact norm_le_of_value_velocity (by positivity) (by positivity) hval hvel'

/-- Continuity from a norm ε–δ criterion in normed groups. -/
theorem continuous_of_norm_criterion {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] {f : E → F}
    (h : ∀ x : E, ∀ ε > 0, ∃ δ > 0, ∀ y : E, ‖y - x‖ < δ → ‖f y - f x‖ < ε) : Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  obtain ⟨δ, hδ, hf⟩ := h x ε hε
  refine ⟨δ, hδ, fun y hy => ?_⟩
  rw [dist_eq_norm] at hy ⊢
  exact hf y hy

set_option maxHeartbeats 1600000 in
/-- H¹ continuity of C¹ pair maps (continuity of the superposition operator). -/
theorem mapData_continuous (hΓ : ContDiff ℝ 1 Γ) :
    Continuous (fun p : Space n × Space n => mapData hΓ p.1 p.2) := by
  apply continuous_of_norm_criterion
  intro p₀ ε hε
  have hRpos : 0 < 2 * (‖p₀‖ + 1) := by positivity
  obtain ⟨LΓ, hL⟩ := (hΓ.contDiffOn
    (s := Metric.closedBall (0 : Ambient n × Ambient n) (2 * (‖p₀‖ + 1)))).exists_lipschitzOnWith
    (by norm_num) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hDc : ContinuousOn (fderiv ℝ Γ)
      (Metric.closedBall (0 : Ambient n × Ambient n) (2 * (‖p₀‖ + 1))) :=
    (hΓ.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Ambient n × Ambient n)
    (2 * (‖p₀‖ + 1))).exists_bound_of_continuousOn hDc
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Metric.mem_closedBall_self hRpos.le))
  have hU := (isCompact_closedBall (0 : Ambient n × Ambient n)
    (2 * (‖p₀‖ + 1))).uniformContinuousOn_of_continuous hDc
  have hM0 : 0 ≤ ‖velocity p₀.1‖ + ‖velocity p₀.2‖ := by positivity
  have hη : 0 < ε / (2 * ((‖velocity p₀.1‖ + ‖velocity p₀.2‖) + 1)) := by positivity
  obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.mp hU _ hη
  have hK0 : 0 ≤ (LΓ : ℝ) + B := by positivity
  refine ⟨min 1 (min (δ / 2) (ε / (4 * ((LΓ : ℝ) + B + 1)))), by positivity, fun p hp => ?_⟩
  have hp1 : ‖p - p₀‖ < 1 := lt_of_lt_of_le hp (min_le_left _ _)
  have hpδ : ‖p - p₀‖ < δ / 2 := lt_of_lt_of_le hp ((min_le_right _ _).trans (min_le_left _ _))
  have hpε : ‖p - p₀‖ < ε / (4 * ((LΓ : ℝ) + B + 1)) :=
    lt_of_lt_of_le hp ((min_le_right _ _).trans (min_le_right _ _))
  have hpnorm : ‖p‖ ≤ (2 * (‖p₀‖ + 1)) / 2 := by
    have h1 := norm_le_insert' p p₀
    have h2 := norm_sub_rev p p₀
    linarith
  have hp₀norm : ‖p₀‖ ≤ (2 * (‖p₀‖ + 1)) / 2 := by linarith
  have hLb : ∀ a ∈ Metric.closedBall (0 : Ambient n × Ambient n) (2 * (‖p₀‖ + 1)),
      ∀ b ∈ Metric.closedBall (0 : Ambient n × Ambient n) (2 * (‖p₀‖ + 1)),
        ‖Γ a - Γ b‖ ≤ LΓ * ‖a - b‖ := by
    intro a ha b hb
    have := hL.dist_le_mul a ha b hb
    rwa [dist_eq_norm, dist_eq_norm] at this
  have hηb : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖fderiv ℝ Γ (pairRep p.1 p.2 t) - fderiv ℝ Γ (pairRep p₀.1 p₀.2 t)‖ ≤
        ε / (2 * ((‖velocity p₀.1‖ + ‖velocity p₀.2‖) + 1)) := by
    intro t ht
    have hm : ∀ q : Space n × Space n, ‖q‖ ≤ (2 * (‖p₀‖ + 1)) / 2 →
        pairRep q.1 q.2 t ∈ Metric.closedBall (0 : Ambient n × Ambient n) (2 * (‖p₀‖ + 1)) := by
      intro q hq
      rw [mem_closedBall_zero_iff]
      exact (pairRep_norm_le q ht).trans (by linarith)
    have hd : dist (pairRep p.1 p.2 t) (pairRep p₀.1 p₀.2 t) < δ := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (pairRep_sub_norm_le p p₀ ht) (by linarith)
    have := hδU _ (hm p hpnorm) _ (hm p₀ hp₀norm) hd
    rw [dist_eq_norm] at this
    exact this.le
  have hest := mapData_sub_le hΓ p p₀ hpnorm hp₀norm hLb (by positivity) hB hB0 hηb hη.le
  have hηM : ε / (2 * ((‖velocity p₀.1‖ + ‖velocity p₀.2‖) + 1)) *
      (‖velocity p₀.1‖ + ‖velocity p₀.2‖) < ε / 2 :=
    calc ε / (2 * ((‖velocity p₀.1‖ + ‖velocity p₀.2‖) + 1)) *
          (‖velocity p₀.1‖ + ‖velocity p₀.2‖) <
        ε / (2 * ((‖velocity p₀.1‖ + ‖velocity p₀.2‖) + 1)) *
          ((‖velocity p₀.1‖ + ‖velocity p₀.2‖) + 1) :=
          mul_lt_mul_of_pos_left (lt_add_one _) hη
      _ = ε / 2 := by field_simp
  have hKe : ((LΓ : ℝ) + B) * (2 * ‖p - p₀‖) < ε / 2 := by
    have h4 : 0 < 4 * ((LΓ : ℝ) + B + 1) := by positivity
    have hlt : ‖p - p₀‖ * (4 * ((LΓ : ℝ) + B + 1)) < ε := (lt_div_iff₀ h4).mp hpε
    calc ((LΓ : ℝ) + B) * (2 * ‖p - p₀‖) ≤ ((LΓ : ℝ) + B + 1) * (2 * ‖p - p₀‖) :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
            (mul_nonneg zero_le_two (norm_nonneg _))
      _ = ‖p - p₀‖ * (4 * ((LΓ : ℝ) + B + 1)) / 2 := by ring
      _ < ε / 2 := div_lt_div_of_pos_right hlt two_pos
  calc
    ‖mapData hΓ p.1 p.2 - mapData hΓ p₀.1 p₀.2‖ ≤ _ := hest
    _ = ((LΓ : ℝ) + B) * (2 * ‖p - p₀‖) + ε / (2 * ((‖velocity p₀.1‖ + ‖velocity p₀.2‖) + 1)) *
          (‖velocity p₀.1‖ + ‖velocity p₀.2‖) := by ring
    _ < ε / 2 + ε / 2 := add_lt_add hKe hηM
    _ = ε := by ring

end

end Finsler.SobolevPairMap
