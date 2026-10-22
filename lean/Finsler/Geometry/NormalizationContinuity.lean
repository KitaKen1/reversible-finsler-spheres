module

public import Finsler.Geometry.NormalizationHomotopy
public import Finsler.Analysis.IntervalH1WeakLimit

/-! Strong H¹ continuity of the normalization homotopy on [0,1] × Λ, including the parameter 1
and stationary intervals. At a loop of length zero the energy bound E(Ψ) ≤ E forces the
velocities to zero while the starting points converge. At a loop of positive length the speeds
converge in L¹, so the primitives of the densities converge uniformly; the right inverses then
give pointwise convergence of the representatives, since the limit loop moves by at most a
multiple of the increment of the primitive of its density (or is continuous, at s = 0). The
squared velocity norms ∫ ‖u̇‖²/ρ converge by Vitali along almost everywhere convergent
subsequences, and the Radon–Riesz argument gives strong convergence. -/

@[expose] public section

namespace Finsler.NormalizationContinuity

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevEnergy Finsler.SobolevLength Finsler.SobolevReparam Finsler.MonotoneSubst
open Finsler.NormalizationHomotopy Finsler.SobolevWeakLimit Finsler.QuadraticVitali
open Finsler.MilnorContinuity
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal

noncomputable section

variable {n : ℕ}

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance : IsFiniteMeasure intervalMeasure := by
  change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) 1))
  infer_instance

section Speed

theorem sq_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : (a - b) ^ 2 ≤ |a ^ 2 - b ^ 2| := by
  have h1 : |a - b| ≤ a + b := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have h2 : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
  rw [h2, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  calc (a - b) ^ 2 = |a - b| * |a - b| := by rw [abs_mul_abs_self, sq]
    _ ≤ |a - b| * (a + b) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

theorem abs_le_amgm {x δ : ℝ} (hδ : 0 < δ) : |x| ≤ δ + x ^ 2 / (4 * δ) := by
  rw [← sq_abs x, ← sub_nonneg]
  have e : δ + |x| ^ 2 / (4 * δ) - |x| = (|x| - 2 * δ) ^ 2 / (4 * δ) := by
    field_simp
    ring
  rw [e]
  positivity

theorem integral_abs_density_sub_tendsto (F : ReversibleMetric n) {v : ℕ → SphereLoop n}
    {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun i => ∫ t, |lagrangian F (weakJet (v i) t) - lagrangian F (weakJet u t)|
      ∂intervalMeasure) atTop (𝓝 0) := by
  have h := density_seq_tendsto_L1 F hv
  have h' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  rw [ENNReal.toReal_zero] at h'
  refine h'.congr fun i => ?_
  simp only [Function.comp_apply]
  have hm := (density_aestronglyMeasurable F (v i)).sub (density_aestronglyMeasurable F u)
  rw [eLpNorm_one_eq_lintegral_enorm hm, ← integral_norm_eq_lintegral_enorm hm]
  rfl

/-- Speeds converge in L¹. -/
theorem integral_abs_speed_sub_tendsto (F : ReversibleMetric n) {v : ℕ → SphereLoop n}
    {u : SphereLoop n} (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun i => ∫ t, |speed F (v i) t - speed F u t| ∂intervalMeasure) atTop (𝓝 0) := by
  have hD := integral_abs_density_sub_tendsto F hv
  rw [Metric.tendsto_nhds] at hD ⊢
  intro ε hε
  set δ := ε / 3 with hδ
  have hδpos : 0 < δ := by positivity
  filter_upwards [hD (4 * δ * δ) (by positivity)] with i hi
  rw [Real.dist_eq, sub_zero] at hi ⊢
  have hint1 : Integrable (fun t => |speed F (v i) t - speed F u t|) intervalMeasure :=
    ((speed_integrable F (v i)).sub (speed_integrable F u)).abs
  have hdint : Integrable (fun t => |lagrangian F (weakJet (v i) t) -
      lagrangian F (weakJet u t)|) intervalMeasure :=
    ((density_integrable F (v i)).sub (density_integrable F u)).abs
  have hint2 : Integrable (fun t => δ + |lagrangian F (weakJet (v i) t) -
      lagrangian F (weakJet u t)| / (4 * δ)) intervalMeasure :=
    (integrable_const _).add (hdint.div_const _)
  have hle : ∫ t, |speed F (v i) t - speed F u t| ∂intervalMeasure ≤
      ∫ t, (δ + |lagrangian F (weakJet (v i) t) - lagrangian F (weakJet u t)| / (4 * δ))
        ∂intervalMeasure := by
    apply integral_mono hint1 hint2
    intro t
    refine (abs_le_amgm hδpos).trans ?_
    show δ + _ ≤ δ + |lagrangian F (weakJet (v i) t) - lagrangian F (weakJet u t)| / (4 * δ)
    gcongr
    rw [← speed_sq, ← speed_sq]
    exact sq_sub_le (speed_nonneg F _ t) (speed_nonneg F _ t)
  have hR : ∫ t, (δ + |lagrangian F (weakJet (v i) t) - lagrangian F (weakJet u t)| / (4 * δ))
      ∂intervalMeasure = δ + (∫ t, |lagrangian F (weakJet (v i) t) - lagrangian F (weakJet u t)|
        ∂intervalMeasure) / (4 * δ) := by
    have hU : intervalMeasure.real univ = 1 := by
      rw [measureReal_def, intervalMeasure_univ, ENNReal.toReal_one]
    rw [integral_add (integrable_const _) (hdint.div_const _), integral_const, integral_div, hU,
      one_smul]
  have hnn : 0 ≤ ∫ t, |speed F (v i) t - speed F u t| ∂intervalMeasure :=
    integral_nonneg fun _ => abs_nonneg _
  rw [abs_of_nonneg hnn]
  have hD0 : 0 ≤ ∫ t, |lagrangian F (weakJet (v i) t) - lagrangian F (weakJet u t)|
      ∂intervalMeasure := integral_nonneg fun _ => abs_nonneg _
  rw [abs_of_nonneg hD0] at hi
  have hq : (∫ t, |lagrangian F (weakJet (v i) t) - lagrangian F (weakJet u t)| ∂intervalMeasure)
      / (4 * δ) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    linarith
  linarith

theorem tendsto_length_seq (F : ReversibleMetric n) {v : ℕ → SphereLoop n} {u : SphereLoop n}
    (hv : Tendsto v atTop (𝓝 u)) : Tendsto (fun i => length F (v i)) atTop (𝓝 (length F u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) (integral_abs_speed_sub_tendsto F hv)
  unfold length
  rw [← integral_sub (speed_integrable F (v i)) (speed_integrable F u), Real.norm_eq_abs]
  exact abs_integral_le_integral_abs

end Speed

section Cumul

theorem mspeed_intervalIntegrable (F : ReversibleMetric n) (u : SphereLoop n) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (mspeed F u) volume x y := by
  have h : IntegrableOn (mspeed F u) (Ioc 0 1) := by
    show Integrable (mspeed F u) (volume.restrict (Ioc (0 : ℝ) 1))
    rw [← intervalMeasure_eq]
    exact mspeed_integrable F u
  constructor
  · exact h.mono_set (Ioc_subset_Ioc hx.1 hy.2)
  · exact h.mono_set (Ioc_subset_Ioc hy.1 hx.2)

theorem cumul_normDensity (F : ReversibleMetric n) (s : ℝ) (u : SphereLoop n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    cumul (normDensity F s u) x =
      (1 - s) * x + s / length F u * ∫ y in (0 : ℝ)..x, mspeed F u y := by
  unfold cumul normDensity
  have hi := mspeed_intervalIntegrable F u ⟨le_rfl, zero_le_one⟩ hx
  rw [intervalIntegral.integral_add intervalIntegrable_const ((hi.div_const _).const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_div]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem integral_mspeed_nonneg (F : ReversibleMetric n) (u : SphereLoop n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ ∫ y in (0 : ℝ)..x, mspeed F u y :=
  intervalIntegral.integral_nonneg hx.1 fun y _ => mspeed_nonneg F u y

theorem integral_mspeed_le (F : ReversibleMetric n) (u : SphereLoop n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : ∫ y in (0 : ℝ)..x, mspeed F u y ≤ length F u := by
  rw [← integral_mspeed F u]
  exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
    (Eventually.of_forall fun y => mspeed_nonneg F u y)
    (mspeed_intervalIntegrable F u ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩)

theorem abs_integral_mspeed_sub_le (F : ReversibleMetric n) (v u : SphereLoop n) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    |(∫ y in (0 : ℝ)..x, mspeed F v y) - ∫ y in (0 : ℝ)..x, mspeed F u y| ≤
      ∫ t, |speed F v t - speed F u t| ∂intervalMeasure := by
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rw [← intervalIntegral.integral_sub (mspeed_intervalIntegrable F v h0 hx)
    (mspeed_intervalIntegrable F u h0 hx)]
  refine (intervalIntegral.abs_integral_le_integral_abs hx.1).trans ?_
  have hint : IntervalIntegrable (fun y => |mspeed F v y - mspeed F u y|) volume 0 1 :=
    ((mspeed_intervalIntegrable F v h0 h1).sub (mspeed_intervalIntegrable F u h0 h1)).abs
  refine (intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
    (Eventually.of_forall fun y => abs_nonneg _) hint).trans (le_of_eq ?_)
  rw [intervalIntegral.integral_of_le zero_le_one, ← intervalMeasure_eq]
  apply integral_congr_ae
  filter_upwards [mspeed_ae F v, mspeed_ae F u] with t h1 h2
  rw [h1, h2]

/-- The primitives of the densities are uniformly close. -/
theorem abs_cumul_sub_le (F : ReversibleMetric n) {s s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) {v u : SphereLoop n} (hLu : 0 < length F u)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |cumul (normDensity F s v) x - cumul (normDensity F s₀ u) x| ≤
      |s - s₀| + |s / length F v - s₀ / length F u| * length F v +
        s₀ / length F u * ∫ t, |speed F v t - speed F u t| ∂intervalMeasure := by
  rw [cumul_normDensity F s v hx, cumul_normDensity F s₀ u hx]
  set Mv := ∫ y in (0 : ℝ)..x, mspeed F v y
  set Mu := ∫ y in (0 : ℝ)..x, mspeed F u y
  have hMv0 : 0 ≤ Mv := integral_mspeed_nonneg F v hx
  have hMvL : Mv ≤ length F v := integral_mspeed_le F v hx
  have hdiff := abs_integral_mspeed_sub_le F v u hx
  have hc : 0 ≤ s₀ / length F u := div_nonneg hs₀.1 hLu.le
  have he : (1 - s) * x + s / length F v * Mv - ((1 - s₀) * x + s₀ / length F u * Mu) =
      (s₀ - s) * x + (s / length F v - s₀ / length F u) * Mv + s₀ / length F u * (Mv - Mu) := by
    ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  refine add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_
  · rw [abs_mul, abs_sub_comm, abs_of_nonneg hx.1]
    exact mul_le_of_le_one_right (abs_nonneg _) hx.2
  · rw [abs_mul, abs_of_nonneg hMv0]
    exact mul_le_mul_of_nonneg_left hMvL (abs_nonneg _)
  · rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left hdiff hc

/-- The limit loop moves by at most a multiple of the increment of the primitive. -/
theorem rep_increment_le (F : ReversibleMetric n) {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1)
    {u : SphereLoop n} (hL : 0 < length F u) {k : ℝ} (hk : 0 < k)
    (hkb : ∀ᵐ t ∂intervalMeasure, k * ‖velocity (u.data : Space n) t‖ ≤ mspeed F u t)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    ‖continuousRepresentative (u.data : Space n) y -
        continuousRepresentative (u.data : Space n) x‖ ≤
      length F u / (s * k) * (cumul (normDensity F s u) y - cumul (normDensity F s u) x) := by
  have hadm := normDensity_admissible F ⟨hs0.le, hs1⟩ hL
  rw [continuousRepresentative_sub (u.data : Space n) hx hy,
    (primitive_sub_eq (admissible_isPrimitive hadm)) hx hy]
  have hvi : IntervalIntegrable (velocity (u.data : Space n)) volume x y := by
    apply (velocity_intervalIntegrable (u.data : Space n)).mono_set
    rw [uIcc_of_le zero_le_one]
    exact uIcc_subset_Icc hx hy
  have hmi := mspeed_intervalIntegrable F u hx hy
  have hρi : IntervalIntegrable (normDensity F s u) volume x y :=
    (primitive_intervalIntegrable (admissible_isPrimitive hadm)) hx hy
  have h1 : ‖∫ t in x..y, velocity (u.data : Space n) t‖ ≤ ∫ t in x..y, mspeed F u t / k := by
    refine (intervalIntegral.norm_integral_le_integral_norm hxy).trans ?_
    apply intervalIntegral.integral_mono_ae_restrict hxy hvi.norm (hmi.div_const k)
    have hkb' : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) 1 →
        k * ‖velocity (u.data : Space n) t‖ ≤ mspeed F u t :=
      (ae_restrict_iff' measurableSet_Ioo).mp hkb
    rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    have hne : ∀ᵐ t ∂volume, t ≠ x := by
      rw [ae_iff]
      simp
    have hne1 : ∀ᵐ t ∂volume, t ≠ (1 : ℝ) := by
      rw [ae_iff]
      simp
    filter_upwards [hkb', hne, hne1] with t ht htx ht1 htI
    have htI' : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt hx.1 (lt_of_le_of_ne htI.1 (Ne.symm htx)),
      lt_of_le_of_ne (htI.2.trans hy.2) ht1⟩
    rw [le_div_iff₀ hk, mul_comm]
    exact ht htI'
  have h2 : ∫ t in x..y, s / length F u * mspeed F u t ≤ ∫ t in x..y, normDensity F s u t := by
    apply intervalIntegral.integral_mono_on hxy (hmi.const_mul _) hρi
    intro t _
    unfold normDensity
    have : s / length F u * mspeed F u t = s * (mspeed F u t / length F u) := by ring
    rw [this]
    linarith [hs1]
  rw [intervalIntegral.integral_const_mul] at h2
  rw [intervalIntegral.integral_div] at h1
  have hm0 : 0 ≤ ∫ t in x..y, mspeed F u t :=
    intervalIntegral.integral_nonneg hxy fun t _ => mspeed_nonneg F u t
  have h3 : ∫ t in x..y, mspeed F u t ≤
      length F u / s * ∫ t in x..y, normDensity F s u t := by
    have := mul_le_mul_of_nonneg_left h2 (div_nonneg hL.le hs0.le)
    rw [← mul_assoc, div_mul_div_comm, mul_comm (length F u) s, div_self (by positivity),
      one_mul] at this
    exact this
  calc ‖∫ t in x..y, velocity (u.data : Space n) t‖
      ≤ (∫ t in x..y, mspeed F u t) / k := h1
    _ ≤ (length F u / s * ∫ t in x..y, normDensity F s u t) / k := by gcongr
    _ = length F u / (s * k) * ∫ t in x..y, normDensity F s u t := by
        field_simp

end Cumul

section Representative

variable (F : ReversibleMetric n)

/-- The uniform distance bound between the primitives of the densities. -/
def theta (p : ℕ → ℝ × SphereLoop n) (p₀ : ℝ × SphereLoop n) (i : ℕ) : ℝ :=
  |(p i).1 - p₀.1| + |(p i).1 / length F (p i).2 - p₀.1 / length F p₀.2| * length F (p i).2 +
    p₀.1 / length F p₀.2 * ∫ t, |speed F (p i).2 t - speed F p₀.2 t| ∂intervalMeasure

theorem tendsto_theta {p : ℕ → ℝ × SphereLoop n} {p₀ : ℝ × SphereLoop n}
    (hp : Tendsto p atTop (𝓝 p₀)) (hL₀ : 0 < length F p₀.2) :
    Tendsto (theta F p p₀) atTop (𝓝 0) := by
  have hu : Tendsto (fun i => (p i).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  have hsT : Tendsto (fun i => (p i).1) atTop (𝓝 p₀.1) := (continuous_fst.tendsto _).comp hp
  have hLT := tendsto_length_seq F hu
  have hη := integral_abs_speed_sub_tendsto F hu
  have h1 : Tendsto (fun i => |(p i).1 - p₀.1|) atTop (𝓝 0) := by
    have := (hsT.sub_const p₀.1).abs
    rwa [sub_self, abs_zero] at this
  have h2 : Tendsto (fun i => |(p i).1 / length F (p i).2 - p₀.1 / length F p₀.2| *
      length F (p i).2) atTop (𝓝 0) := by
    have := ((hsT.div hLT hL₀.ne').sub_const (p₀.1 / length F p₀.2)).abs.mul hLT
    rwa [sub_self, abs_zero, zero_mul] at this
  have h3 := hη.const_mul (p₀.1 / length F p₀.2)
  rw [mul_zero] at h3
  have := (h1.add h2).add h3
  rwa [add_zero, add_zero] at this

theorem abs_cumul_sub_le_theta {p : ℕ → ℝ × SphereLoop n} {p₀ : ℝ × SphereLoop n}
    (hs₀ : p₀.1 ∈ Icc (0 : ℝ) 1) (hL₀ : 0 < length F p₀.2) (i : ℕ) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    |cumul (normDensity F (p i).1 (p i).2) x - cumul (normDensity F p₀.1 p₀.2) x| ≤
      theta F p p₀ i :=
  abs_cumul_sub_le F hs₀ hL₀ hx

theorem representative_normLoop_of_pos {q : ℝ × SphereLoop n} (hs : q.1 ∈ Icc (0 : ℝ) 1)
    (hL : 0 < length F q.2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    continuousRepresentative ((normLoop F q).data : Space n) t =
      continuousRepresentative (q.2.data : Space n) (time (normDensity F q.1 q.2) t) := by
  rw [normLoop_of_mem F (p := q) ⟨hs, hL⟩]
  exact representative_reparam (normDensity_admissible F hs hL) ht

theorem norm_representative_sub_le (v u : SphereLoop n) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ‖continuousRepresentative (v.data : Space n) x - continuousRepresentative (u.data : Space n) x‖
      ≤ 2 * ‖(v.data : Space n) - (u.data : Space n)‖ := by
  have h := (traceL n ⟨x, hx⟩).le_opNorm ((v.data : Space n) - (u.data : Space n))
  rw [map_sub] at h
  exact h.trans (mul_le_mul_of_nonneg_right (traceL_norm_le n _) (norm_nonneg _))

/-- The limit loop along the new times converges. -/
theorem tendsto_limit_along_times {p : ℕ → ℝ × SphereLoop n} {p₀ : ℝ × SphereLoop n}
    (hp : Tendsto p atTop (𝓝 p₀)) (hs : ∀ i, (p i).1 ∈ Icc (0 : ℝ) 1)
    (hL : ∀ i, 0 < length F (p i).2) (hs₀ : p₀.1 ∈ Icc (0 : ℝ) 1) (hL₀ : 0 < length F p₀.2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun i => continuousRepresentative (p₀.2.data : Space n)
        (time (normDensity F (p i).1 (p i).2) t)) atTop
      (𝓝 (continuousRepresentative (p₀.2.data : Space n) (time (normDensity F p₀.1 p₀.2) t))) := by
  have hθ := tendsto_theta F hp hL₀
  have hadm₀ := normDensity_admissible F hs₀ hL₀
  have hxm (i : ℕ) : time (normDensity F (p i).1 (p i).2) t ∈ Icc (0 : ℝ) 1 := time_mem t
  have hx₀m : time (normDensity F p₀.1 p₀.2) t ∈ Icc (0 : ℝ) 1 := time_mem t
  have hcx (i : ℕ) : |cumul (normDensity F p₀.1 p₀.2) (time (normDensity F (p i).1 (p i).2) t)
      - t| ≤ theta F p p₀ i := by
    have h := abs_cumul_sub_le_theta F (p := p) hs₀ hL₀ i (hxm i)
    have hc : cumul (normDensity F (p i).1 (p i).2) (time (normDensity F (p i).1 (p i).2) t) = t :=
      (cumul_time (normDensity_admissible F (hs i) (hL i))) ht
    calc |cumul (normDensity F p₀.1 p₀.2) (time (normDensity F (p i).1 (p i).2) t) - t|
        = |t - cumul (normDensity F p₀.1 p₀.2) (time (normDensity F (p i).1 (p i).2) t)| :=
          abs_sub_comm _ _
      _ = |cumul (normDensity F (p i).1 (p i).2) (time (normDensity F (p i).1 (p i).2) t) -
            cumul (normDensity F p₀.1 p₀.2) (time (normDensity F (p i).1 (p i).2) t)| :=
          congrArg (fun z => |z - cumul (normDensity F p₀.1 p₀.2)
            (time (normDensity F (p i).1 (p i).2) t)|) hc.symm
      _ ≤ theta F p p₀ i := h
  rcases eq_or_lt_of_le hs₀.1 with h0 | hpos
  · -- s₀ = 0: the limit primitive is the identity
    have hid (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) : cumul (normDensity F p₀.1 p₀.2) y = y := by
      rw [cumul_normDensity F _ _ hy, ← h0]
      ring
    have hx₀t : time (normDensity F p₀.1 p₀.2) t = t := by
      have h := (cumul_time hadm₀) ht
      rwa [hid _ hx₀m] at h
    have hxt : Tendsto (fun i => time (normDensity F (p i).1 (p i).2) t) atTop (𝓝 t) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hθ
      have h := hcx i
      rw [hid _ (hxm i)] at h
      rw [Real.norm_eq_abs]
      exact h
    have hcont := (continuousRepresentative_continuousOn (p₀.2.data : Space n)) t ht
    have hlim := hcont.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hxt, Eventually.of_forall hxm⟩)
    exact hlim.mono_right (le_of_eq (congrArg
      (fun z => 𝓝 (continuousRepresentative (p₀.2.data : Space n) z)) hx₀t.symm))
  · -- s₀ > 0: the limit loop moves by a multiple of the primitive increment
    obtain ⟨k, hk, hkb⟩ := exists_speed_lower F
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hθ' := (hθ.const_mul (length F p₀.2 / (p₀.1 * k))).mono_right
      (le_of_eq (congrArg 𝓝 (mul_zero (length F p₀.2 / (p₀.1 * k)))))
    refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hθ'
    have hc₀ : cumul (normDensity F p₀.1 p₀.2) (time (normDensity F p₀.1 p₀.2) t) = t :=
      (cumul_time hadm₀) ht
    have hcoef : 0 ≤ length F p₀.2 / (p₀.1 * k) := by positivity
    have hci := abs_le.mp (hcx i)
    rcases le_total (time (normDensity F (p i).1 (p i).2) t) (time (normDensity F p₀.1 p₀.2) t)
      with hle | hle
    · have h := rep_increment_le F hpos hs₀.2 hL₀ hk (hkb p₀.2) (hxm i) hx₀m hle
      rw [norm_sub_rev]
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hcoef)
      linarith [hc₀, hci.1, hci.2]
    · have h := rep_increment_le F hpos hs₀.2 hL₀ hk (hkb p₀.2) hx₀m (hxm i) hle
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hcoef)
      linarith [hc₀, hci.1, hci.2]

/-- Pointwise convergence of the representatives at positive limit length. -/
theorem tendsto_representative_normLoop {p : ℕ → ℝ × SphereLoop n} {p₀ : ℝ × SphereLoop n}
    (hp : Tendsto p atTop (𝓝 p₀)) (hs : ∀ i, (p i).1 ∈ Icc (0 : ℝ) 1)
    (hL : ∀ i, 0 < length F (p i).2) (hs₀ : p₀.1 ∈ Icc (0 : ℝ) 1) (hL₀ : 0 < length F p₀.2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun i => continuousRepresentative ((normLoop F (p i)).data : Space n) t) atTop
      (𝓝 (continuousRepresentative ((normLoop F p₀).data : Space n) t)) := by
  have hu : Tendsto (fun i => (p i).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  have hunif : Tendsto (fun i => ‖((p i).2.data : Space n) - (p₀.2.data : Space n)‖) atTop
      (𝓝 0) := by
    have := sphereLoop_tendsto_iff.mp hu
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  have hB := tendsto_limit_along_times F hp hs hL hs₀ hL₀ ht
  rw [tendsto_iff_norm_sub_tendsto_zero] at hB
  have hsum := ((hunif.const_mul 2).add hB).mono_right
    (le_of_eq (congrArg 𝓝 (show (2 : ℝ) * 0 + 0 = 0 by ring)))
  have H : Tendsto (fun i => continuousRepresentative ((p i).2.data : Space n)
      (time (normDensity F (p i).1 (p i).2) t)) atTop
      (𝓝 (continuousRepresentative (p₀.2.data : Space n) (time (normDensity F p₀.1 p₀.2) t))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hsum
    exact (norm_sub_le_norm_sub_add_norm_sub _
      (continuousRepresentative (p₀.2.data : Space n) (time (normDensity F (p i).1 (p i).2) t))
        _).trans (add_le_add (norm_representative_sub_le (p i).2 p₀.2 (time_mem t)) le_rfl)
  have key := H.congr fun i => (representative_normLoop_of_pos F (hs i) (hL i) ht).symm
  exact key.mono_right (le_of_eq (congrArg 𝓝 (representative_normLoop_of_pos F hs₀ hL₀ ht).symm))

end Representative

section VelocityNorm

variable (F : ReversibleMetric n)

/-- The kinetic integrand of the normalized loop. -/
def kin (p : ℝ × SphereLoop n) (t : ℝ) : ℝ :=
  (normDensity F p.1 p.2 t)⁻¹ * ‖velocity (p.2.data : Space n) t‖ ^ 2

theorem kin_nonneg {p : ℝ × SphereLoop n} (hs : p.1 ∈ Icc (0 : ℝ) 1)
    (hL : 0 < length F p.2) (t : ℝ) : 0 ≤ kin F p t :=
  mul_nonneg (inv_nonneg.mpr ((normDensity_admissible F hs hL).nonneg t)) (sq_nonneg _)

theorem kin_aestronglyMeasurable {p : ℝ × SphereLoop n} (hs : p.1 ∈ Icc (0 : ℝ) 1)
    (hL : 0 < length F p.2) : AEStronglyMeasurable (kin F p) intervalMeasure :=
  (normDensity_admissible F hs hL).measurable.inv.aemeasurable.aestronglyMeasurable.mul
    ((Lp.aestronglyMeasurable _).norm.pow 2)

theorem kin_integrable {p : ℝ × SphereLoop n} (hs : p.1 ∈ Icc (0 : ℝ) 1)
    (hL : 0 < length F p.2) : Integrable (kin F p) intervalMeasure :=
  (normDensity_admissible F hs hL).finite

theorem velocity_norm_sq_normLoop {p : ℝ × SphereLoop n} (hs : p.1 ∈ Icc (0 : ℝ) 1)
    (hL : 0 < length F p.2) :
    ‖velocity ((normLoop F p).data : Space n)‖ ^ 2 = ∫ t, kin F p t ∂intervalMeasure := by
  rw [normLoop_of_mem F ⟨hs, hL⟩]
  exact (reparam_velocity_norm_sq (normDensity_admissible F hs hL))

theorem ae_tendsto_kin {p : ℕ → ℝ × SphereLoop n} {p₀ : ℝ × SphereLoop n}
    (hp : Tendsto p atTop (𝓝 p₀)) (hs : ∀ i, (p i).1 ∈ Icc (0 : ℝ) 1)
    (hL : ∀ i, 0 < length F (p i).2) (hs₀ : p₀.1 ∈ Icc (0 : ℝ) 1) (hL₀ : 0 < length F p₀.2)
    (hvel : ∀ᵐ t ∂intervalMeasure, Tendsto (fun i => velocity ((p i).2.data : Space n) t) atTop
      (𝓝 (velocity (p₀.2.data : Space n) t))) :
    ∀ᵐ t ∂intervalMeasure, Tendsto (fun i => kin F (p i) t) atTop (𝓝 (kin F p₀ t)) := by
  obtain ⟨k, hk, hkb⟩ := exists_speed_lower F
  have hu : Tendsto (fun i => (p i).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  have hsT : Tendsto (fun i => (p i).1) atTop (𝓝 p₀.1) := (continuous_fst.tendsto _).comp hp
  have hLT := tendsto_length_seq F hu
  have hdens := density_ae_tendsto_of_velocity_ae_tendsto F hu hvel
  have hms : ∀ᵐ t ∂intervalMeasure, ∀ i, mspeed F (p i).2 t = speed F (p i).2 t :=
    ae_all_iff.mpr fun i => mspeed_ae F (p i).2
  have hkall : ∀ᵐ t ∂intervalMeasure, ∀ i,
      k * ‖velocity ((p i).2.data : Space n) t‖ ≤ mspeed F (p i).2 t :=
    ae_all_iff.mpr fun i => hkb (p i).2
  filter_upwards [hvel, hdens, hms, mspeed_ae F p₀.2, hkall, hkb p₀.2] with t hv hd hmi hm0 hki hk0
  have hsp : Tendsto (fun i => mspeed F (p i).2 t) atTop (𝓝 (mspeed F p₀.2 t)) := by
    simp_rw [hmi]
    rw [hm0]
    exact (Real.continuous_sqrt.tendsto _).comp hd
  have hρ : Tendsto (fun i => normDensity F (p i).1 (p i).2 t) atTop
      (𝓝 (normDensity F p₀.1 p₀.2 t)) := by
    unfold normDensity
    exact (tendsto_const_nhds.sub hsT).add (hsT.mul (hsp.div hLT hL₀.ne'))
  unfold kin
  by_cases h0 : normDensity F p₀.1 p₀.2 t = 0
  · have hm00 : mspeed F p₀.2 t = 0 := by
      unfold normDensity at h0
      have h1 : 0 ≤ 1 - p₀.1 := sub_nonneg.mpr hs₀.2
      have h2 : 0 ≤ p₀.1 * (mspeed F p₀.2 t / length F p₀.2) :=
        mul_nonneg hs₀.1 (div_nonneg (mspeed_nonneg F p₀.2 t) hL₀.le)
      have hs1 : p₀.1 = 1 := by linarith
      rw [hs1] at h0
      have h3 : mspeed F p₀.2 t / length F p₀.2 = 0 := by linarith
      rcases div_eq_zero_iff.mp h3 with h | h
      · exact h
      · exact absurd h hL₀.ne'
    have hv0 : ‖velocity (p₀.2.data : Space n) t‖ = 0 := by
      rw [hm00] at hk0
      exact le_antisymm (by nlinarith [norm_nonneg (velocity (p₀.2.data : Space n) t)])
        (norm_nonneg _)
    have hlim0 : (normDensity F p₀.1 p₀.2 t)⁻¹ * ‖velocity (p₀.2.data : Space n) t‖ ^ 2 = 0 := by
      rw [h0, inv_zero, zero_mul]
    have hvn : Tendsto (fun i => ‖velocity ((p i).2.data : Space n) t‖) atTop (𝓝 0) :=
      hv.norm.mono_right (le_of_eq (congrArg 𝓝 hv0))
    have hup : Tendsto (fun i => 2 * ‖velocity ((p i).2.data : Space n) t‖ ^ 2 +
        2 * length F (p i).2 / k * ‖velocity ((p i).2.data : Space n) t‖) atTop (𝓝 0) :=
      (((hvn.pow 2).const_mul 2).add (((hLT.const_mul 2).div_const k).mul hvn)).mono_right
        (le_of_eq (congrArg 𝓝 (by ring)))
    refine (squeeze_zero (fun i => ?_) (fun i => ?_) hup).mono_right
      (le_of_eq (congrArg 𝓝 hlim0.symm))
    · exact mul_nonneg (inv_nonneg.mpr ((normDensity_admissible F (hs i) (hL i)).nonneg t))
        (sq_nonneg _)
    · exact inv_density_le (hs i) (hL i) hk (norm_nonneg _) (hki i)
  · exact (hρ.inv₀ h0).mul (hv.norm.pow 2)

theorem kin_unifIntegrable {p : ℕ → ℝ × SphereLoop n} {p₀ : ℝ × SphereLoop n}
    (hp : Tendsto p atTop (𝓝 p₀)) (hs : ∀ i, (p i).1 ∈ Icc (0 : ℝ) 1)
    (hL : ∀ i, 0 < length F (p i).2) :
    UnifIntegrable (fun i => kin F (p i)) 1 intervalMeasure := by
  obtain ⟨k, hk, hkb⟩ := exists_speed_lower F
  have hu : Tendsto (fun i => (p i).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  have hvT := sphereLoop_velocity_tendsto hu
  obtain ⟨B, hB⟩ : ∃ B, ∀ i, length F (p i).2 ≤ B := by
    obtain ⟨B, hB⟩ := (tendsto_length_seq F hu).bddAbove_range
    exact ⟨B, fun i => hB ⟨i, rfl⟩⟩
  have hUI1 : UnifIntegrable (fun i t => 3 * ‖velocity ((p i).2.data : Space n) t‖ ^ 2) 1
      intervalMeasure :=
    lp_convergent_quadratic_unifIntegrable hvT
      (fun i => ((Lp.aestronglyMeasurable _).norm.pow 2).const_mul 3) (by norm_num)
      (fun i => Eventually.of_forall fun t => le_of_eq (Real.norm_of_nonneg (by positivity)))
  have hUI2 : UnifIntegrable (fun (_ : ℕ) (_ : ℝ) => (B / k) ^ 2) 1 intervalMeasure :=
    unifIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const _)
  refine (hUI1.add hUI2 le_rfl).ae_mono (fun i => kin_aestronglyMeasurable F (hs i) (hL i))
    fun i => ?_
  filter_upwards [hkb (p i).2] with t ht
  have hnn := kin_nonneg F (hs i) (hL i) t
  have hle : kin F (p i) t ≤ 3 * ‖velocity ((p i).2.data : Space n) t‖ ^ 2 + (B / k) ^ 2 := by
    have h1 : (normDensity F (p i).1 (p i).2 t)⁻¹ * ‖velocity ((p i).2.data : Space n) t‖ ^ 2 ≤
        2 * ‖velocity ((p i).2.data : Space n) t‖ ^ 2 +
          2 * length F (p i).2 / k * ‖velocity ((p i).2.data : Space n) t‖ :=
      inv_density_le (hs i) (hL i) hk (norm_nonneg _) ht
    have hL0 := length_nonneg F (p i).2
    have h2 : length F (p i).2 / k ≤ B / k := div_le_div_of_nonneg_right (hB i) hk.le
    have h3 : 0 ≤ length F (p i).2 / k := div_nonneg hL0 hk.le
    have h4 : 2 * length F (p i).2 / k * ‖velocity ((p i).2.data : Space n) t‖ ≤
        ‖velocity ((p i).2.data : Space n) t‖ ^ 2 + (B / k) ^ 2 := by
      have e : 2 * length F (p i).2 / k * ‖velocity ((p i).2.data : Space n) t‖ =
          2 * (length F (p i).2 / k) * ‖velocity ((p i).2.data : Space n) t‖ := by ring
      rw [e]
      nlinarith [sq_nonneg (‖velocity ((p i).2.data : Space n) t‖ - length F (p i).2 / k),
        mul_le_mul h2 h2 h3 (h3.trans h2)]
    unfold kin
    linarith
  have hR : 0 ≤ 3 * ‖velocity ((p i).2.data : Space n) t‖ ^ 2 + (B / k) ^ 2 := by positivity
  simp only [Pi.add_apply]
  rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg hnn, abs_of_nonneg hR]
  exact ENNReal.ofReal_le_ofReal hle

/-- Convergence of the squared velocity norms. -/
theorem tendsto_integral_kin {p : ℕ → ℝ × SphereLoop n} {p₀ : ℝ × SphereLoop n}
    (hp : Tendsto p atTop (𝓝 p₀)) (hs : ∀ i, (p i).1 ∈ Icc (0 : ℝ) 1)
    (hL : ∀ i, 0 < length F (p i).2) (hs₀ : p₀.1 ∈ Icc (0 : ℝ) 1) (hL₀ : 0 < length F p₀.2) :
    Tendsto (fun i => ∫ t, kin F (p i) t ∂intervalMeasure) atTop
      (𝓝 (∫ t, kin F p₀ t ∂intervalMeasure)) := by
  have hu : Tendsto (fun i => (p i).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hvns := sphereLoop_velocity_tendsto (hu.comp hns)
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvns).exists_seq_tendsto_ae
  have hq : Tendsto (fun i => p (ns (ms i))) atTop (𝓝 p₀) :=
    hp.comp (hns.comp hms.tendsto_atTop)
  refine ⟨ms, tendsto_integral_of_L1' _ (Eventually.of_forall fun i => kin_integrable F
    (hs (ns (ms i))) (hL (ns (ms i)))) ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
    (fun i => kin_aestronglyMeasurable F (hs (ns (ms i))) (hL (ns (ms i))))
    (memLp_one_iff_integrable.mpr (kin_integrable F hs₀ hL₀))
    (kin_unifIntegrable F hq (fun i => hs (ns (ms i))) (fun i => hL (ns (ms i))))
    (ae_tendsto_kin F hq (fun i => hs (ns (ms i))) (fun i => hL (ns (ms i))) hs₀ hL₀ hae)

end VelocityNorm

section Continuity

variable (F : ReversibleMetric n)

theorem tendsto_normLoop_of_pos {p : ℕ → ℝ × SphereLoop n} {p₀ : ℝ × SphereLoop n}
    (hp : Tendsto p atTop (𝓝 p₀)) (hs : ∀ i, (p i).1 ∈ Icc (0 : ℝ) 1)
    (hL : ∀ i, 0 < length F (p i).2) (hs₀ : p₀.1 ∈ Icc (0 : ℝ) 1) (hL₀ : 0 < length F p₀.2) :
    Tendsto (fun i => normLoop F (p i)) atTop (𝓝 (normLoop F p₀)) := by
  rw [sphereLoop_tendsto_iff]
  apply tendsto_of_representative_norm
  · intro t ht
    exact tendsto_representative_normLoop F hp hs hL hs₀ hL₀ ht
  · have hsq : Tendsto (fun i => ‖velocity ((normLoop F (p i)).data : Space n)‖ ^ 2) atTop
        (𝓝 (‖velocity ((normLoop F p₀).data : Space n)‖ ^ 2)) := by
      rw [velocity_norm_sq_normLoop F hs₀ hL₀]
      refine (tendsto_integral_kin F hp hs hL hs₀ hL₀).congr fun i => ?_
      rw [velocity_norm_sq_normLoop F (hs i) (hL i)]
    have h := (Real.continuous_sqrt.tendsto _).comp hsq
    simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] at h
    exact h

theorem tendsto_normLoop_of_length_zero {X : Type*} {l : Filter X} {p : X → ℝ × SphereLoop n}
    {p₀ : ℝ × SphereLoop n} (hp : Tendsto p l (𝓝 p₀))
    (hs : ∀ᶠ x in l, (p x).1 ∈ Icc (0 : ℝ) 1) (hL₀ : length F p₀.2 = 0) :
    Tendsto (fun x => normLoop F (p x)) l (𝓝 (normLoop F p₀)) := by
  have hu : Tendsto (fun x => (p x).2) l (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  rw [normLoop_of_length_eq_zero F hL₀, sphereLoop_tendsto_iff]
  apply tendsto_of_trace_velocity
  · simp_rw [representative_normLoop_zero]
    exact sphereLoop_representative_tendsto hu ⟨le_rfl, zero_le_one⟩
  · have hv0 : velocity (p₀.2.data : Space n) = 0 :=
      velocity_eq_zero_of_energy_eq_zero F _ (energy_eq_zero_of_length F hL₀)
    rw [hv0, tendsto_zero_iff_norm_tendsto_zero]
    obtain ⟨c, hc, hcb⟩ := Finsler.PolygonSampling.exists_velocity_sq_le F
    have hE : Tendsto (fun x => SobolevEnergy.energy F (p x).2) l (𝓝 0) := by
      rw [← energy_eq_zero_of_length F hL₀]
      exact ((SobolevEnergy.energy_continuous F).tendsto _).comp hu
    have hlim : Tendsto (fun x => Real.sqrt (SobolevEnergy.energy F (p x).2 / c)) l (𝓝 0) :=
      ((Real.continuous_sqrt.tendsto _).comp (hE.div_const c)).mono_right
        (le_of_eq (congrArg 𝓝 (by rw [zero_div, Real.sqrt_zero])))
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
    filter_upwards [hs] with x hx
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc, mul_comm]
    exact (hcb _).trans (energy_normLoop_le_energy F hx (p x).2)

/-- The normalization homotopy is continuous on [0, 1] × Λ. -/
theorem normLoop_continuousOn :
    ContinuousOn (normLoop F) (Icc (0 : ℝ) 1 ×ˢ (univ : Set (SphereLoop n))) := by
  intro p₀ hp₀
  have hs₀ : p₀.1 ∈ Icc (0 : ℝ) 1 := hp₀.1
  by_cases hL₀ : length F p₀.2 = 0
  · exact tendsto_normLoop_of_length_zero F (tendsto_id.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => hx.1) hL₀
  · have hL₀' : 0 < length F p₀.2 := lt_of_le_of_ne (length_nonneg F _) (Ne.symm hL₀)
    rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
    intro x hx
    rw [tendsto_nhdsWithin_iff] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hLx : Tendsto (fun i => length F (x i).2) atTop (𝓝 (length F p₀.2)) :=
      tendsto_length_seq F ((continuous_snd.tendsto _).comp hx1)
    have hev : ∀ᶠ i in atTop, x i ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set (SphereLoop n)) ∧
        0 < length F (x i).2 := hx2.and (hLx.eventually (lt_mem_nhds hL₀'))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have hshift := tendsto_normLoop_of_pos F (p := fun i => x (i + N))
      ((tendsto_add_atTop_iff_nat N).mpr hx1) (fun i => (hN (i + N) (by omega)).1.1)
      (fun i => (hN (i + N) (by omega)).2) hs₀ hL₀'
    exact (tendsto_add_atTop_iff_nat N).mp hshift

end Continuity

end

end Finsler.NormalizationContinuity
