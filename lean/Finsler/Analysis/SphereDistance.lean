module

public import Finsler.Analysis.IntervalH1Concat
public import Finsler.Analysis.IntervalH1Reverse
public import Finsler.Analysis.IntervalH1SphereChart
public import Mathlib.Analysis.Normed.Module.Connected

/-! The Finsler distance on the sphere from minimal path energy. The minimal energy e(p,q) is the
infimum of the energies of actual H¹ sphere paths from p to q on the unit interval, and the
distance is d = √e. Reversal gives symmetry, concatenation with an optimized split parameter
gives the triangle inequality, the round comparison gives c‖p − q‖² ≤ e(p,q), and restriction
gives the sampling estimate e(u(s),u(t)) ≤ (t − s)E(u). The inverse stereographic image of a
segment joins nearby points with e(p,q) ≤ C‖p − q‖², and connectedness of the sphere joins any
two points when n ≥ 1. -/

@[expose] public section

namespace Finsler.SphereDistance

open Finsler.SphereGeometry Finsler.Geometry Finsler.IntervalSobolev Finsler.AmbientLagrangian
open Finsler.SobolevSpherePath Finsler.SobolevAffine Finsler.SobolevConcat Finsler.SobolevReverse
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal RealInnerProductSpace

noncomputable section

variable {n : ℕ}

/-- Actual H¹ sphere paths from p to q. -/
def pathsBetween (n : ℕ) (p q : Ambient n) : Set (Space n) :=
  {w | w ∈ SpherePath n ∧ continuousRepresentative w 0 = p ∧ continuousRepresentative w 1 = q}

/-- The minimal energy of sphere paths from p to q. -/
def minEnergy (F : ReversibleMetric n) (p q : Ambient n) : ℝ :=
  sInf (pathEnergy F '' pathsBetween n p q)

/-- The Finsler distance. -/
def dist (F : ReversibleMetric n) (p q : Ambient n) : ℝ := Real.sqrt (minEnergy F p q)

theorem minEnergy_nonneg (F : ReversibleMetric n) (p q : Ambient n) : 0 ≤ minEnergy F p q := by
  apply Real.sInf_nonneg
  rintro _ ⟨w, _, rfl⟩
  exact pathEnergy_nonneg F w

theorem dist_nonneg (F : ReversibleMetric n) (p q : Ambient n) : 0 ≤ dist F p q :=
  Real.sqrt_nonneg _

theorem dist_sq (F : ReversibleMetric n) (p q : Ambient n) : dist F p q ^ 2 = minEnergy F p q :=
  Real.sq_sqrt (minEnergy_nonneg F p q)

theorem bddBelow_energies (F : ReversibleMetric n) (p q : Ambient n) :
    BddBelow (pathEnergy F '' pathsBetween n p q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨w, _, rfl⟩
  exact pathEnergy_nonneg F w

theorem minEnergy_le (F : ReversibleMetric n) {p q : Ambient n} {w : Space n}
    (hw : w ∈ pathsBetween n p q) : minEnergy F p q ≤ pathEnergy F w :=
  csInf_le (bddBelow_energies F p q) ⟨w, hw, rfl⟩

theorem exists_lt_of_lt (F : ReversibleMetric n) {p q : Ambient n}
    (hne : (pathsBetween n p q).Nonempty) {b : ℝ} (hb : minEnergy F p q < b) :
    ∃ w ∈ pathsBetween n p q, pathEnergy F w < b := by
  obtain ⟨_, ⟨w, hw, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (hne.image _) hb
  exact ⟨w, hw, hlt⟩

/-- Sampling estimate in distance form. -/
theorem minEnergy_sample_le (F : ReversibleMetric n) {w : Space n} (hw : w ∈ SpherePath n)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    minEnergy F (continuousRepresentative w s) (continuousRepresentative w t) ≤
      (t - s) * pathEnergy F w := by
  have hmem : restrict w hs ht hst ∈ pathsBetween n (continuousRepresentative w s)
      (continuousRepresentative w t) :=
    ⟨restrict_mem hw hs ht hst, representative_restrict_zero w hs ht hst,
      representative_restrict_one w hs ht hst⟩
  exact (minEnergy_le F hmem).trans (pathEnergy_restrict_le F hw hs ht hst)

/-- Sampling estimate for actual sphere loops. -/
theorem minEnergy_sample_loop_le (F : ReversibleMetric n) (u : SphereLoop n) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    minEnergy F (continuousRepresentative (u.data : Space n) s)
        (continuousRepresentative (u.data : Space n) t) ≤
      (t - s) * Finsler.SobolevEnergy.energy F u :=
  minEnergy_sample_le F (sphereLoop_mem u) hs ht hst

section Reverse

theorem pathEnergy_reverseData (F : ReversibleMetric n) (w : Space n) :
    pathEnergy F (reverseData w) = pathEnergy F w := by
  have hae : (fun t => lagrangian F (continuousRepresentative (reverseData w) t,
      velocity (reverseData w) t)) =ᵐ[intervalMeasure]
      fun t => lagrangian F (continuousRepresentative w (reflection t),
        velocity w (reflection t)) := by
    filter_upwards [velocity_reverseData_ae w, ae_restrict_mem measurableSet_Ioo] with t hv ht
    rw [representative_reverseData w (Ioo_subset_Icc_self ht), hv]
    have h := Finsler.EnergyConservation.lagrangian_velocity_smul F
      (continuousRepresentative w (reflection t)) (velocity w (reflection t)) (-1)
    simpa only [neg_one_smul, neg_one_sq, one_mul, reverseVelocityFun] using h
  change (∫ t, lagrangian F (continuousRepresentative (reverseData w) t,
    velocity (reverseData w) t) ∂intervalMeasure) = _
  rw [integral_congr_ae hae]
  exact reflection_measurePreserving.integral_comp (measurableEmbedding_subLeft (1 : ℝ))
    (fun t : ℝ => lagrangian F (continuousRepresentative w t, velocity w t))

theorem reverseData_mem_pathsBetween {p q : Ambient n} {w : Space n}
    (hw : w ∈ pathsBetween n p q) : reverseData w ∈ pathsBetween n q p := by
  obtain ⟨hs, h0, h1⟩ := hw
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [representative_reverseData w ht]
    exact hs _ (reflection_mem_Icc ht)
  · rw [representative_reverseData w (left_mem_Icc.mpr zero_le_one)]
    change continuousRepresentative w (1 - 0) = q
    rw [sub_zero, h1]
  · rw [representative_reverseData w (right_mem_Icc.mpr zero_le_one)]
    change continuousRepresentative w (1 - 1) = p
    rw [sub_self, h0]

theorem image_subset_swap (F : ReversibleMetric n) (p q : Ambient n) :
    pathEnergy F '' pathsBetween n p q ⊆ pathEnergy F '' pathsBetween n q p := by
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨reverseData w, reverseData_mem_pathsBetween hw, pathEnergy_reverseData F w⟩

theorem minEnergy_comm (F : ReversibleMetric n) (p q : Ambient n) :
    minEnergy F p q = minEnergy F q p := by
  unfold minEnergy
  rw [Set.Subset.antisymm (image_subset_swap F p q) (image_subset_swap F q p)]

theorem dist_comm (F : ReversibleMetric n) (p q : Ambient n) : dist F p q = dist F q p := by
  unfold dist
  rw [minEnergy_comm]

end Reverse

section Triangle

/-- The optimized split of A/a + B/(1 − a). -/
theorem split_bound {A B δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 < δ) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      A / a + B / (1 - a) ≤ (Real.sqrt A + Real.sqrt B + 2 * δ) ^ 2 := by
  set x := Real.sqrt A with hx
  set y := Real.sqrt B with hy
  have hx0 : 0 ≤ x := Real.sqrt_nonneg A
  have hy0 : 0 ≤ y := Real.sqrt_nonneg B
  have hAx : A = x ^ 2 := (Real.sq_sqrt hA).symm
  have hBy : B = y ^ 2 := (Real.sq_sqrt hB).symm
  set S := x + y + 2 * δ with hS
  have hSpos : 0 < S := by positivity
  refine ⟨(x + δ) / S, div_pos (by positivity) hSpos, ?_, ?_⟩
  · rw [div_lt_one hSpos]
    linarith
  · have h1a : 1 - (x + δ) / S = (y + δ) / S := by
      field_simp
      ring
    rw [h1a, div_div_eq_mul_div, div_div_eq_mul_div, hAx, hBy]
    have hxd : 0 < x + δ := by positivity
    have hyd : 0 < y + δ := by positivity
    have e1 : x ^ 2 * S / (x + δ) ≤ x * S := by
      rw [div_le_iff₀ hxd]
      nlinarith [mul_nonneg hx0 hSpos.le, mul_nonneg (mul_nonneg hx0 hSpos.le) hδ.le]
    have e2 : y ^ 2 * S / (y + δ) ≤ y * S := by
      rw [div_le_iff₀ hyd]
      nlinarith [mul_nonneg hy0 hSpos.le, mul_nonneg (mul_nonneg hy0 hSpos.le) hδ.le]
    have e3 : x * S + y * S ≤ S ^ 2 := by nlinarith
    linarith

theorem minEnergy_triangle_aux (F : ReversibleMetric n) {p q r : Ambient n} {w₁ w₂ : Space n}
    (h₁ : w₁ ∈ pathsBetween n p q) (h₂ : w₂ ∈ pathsBetween n q r) {δ : ℝ} (hδ : 0 < δ) :
    minEnergy F p r ≤
      (Real.sqrt (pathEnergy F w₁) + Real.sqrt (pathEnergy F w₂) + 2 * δ) ^ 2 := by
  obtain ⟨a, ha0, ha1, hbound⟩ := split_bound (pathEnergy_nonneg F w₁) (pathEnergy_nonneg F w₂) hδ
  have hmatch : continuousRepresentative w₁ 1 = continuousRepresentative w₂ 0 := by
    rw [h₁.2.2, h₂.2.1]
  have hmem : concat w₁ w₂ ha0 ha1 ∈ pathsBetween n p r :=
    ⟨concat_mem w₁ w₂ ha0 ha1 h₁.1 h₂.1 hmatch,
      (representative_concat_zero w₁ w₂ ha0 ha1).trans h₁.2.1,
      (representative_concat_one w₁ w₂ ha0 ha1 hmatch).trans h₂.2.2⟩
  calc minEnergy F p r ≤ pathEnergy F (concat w₁ w₂ ha0 ha1) := minEnergy_le F hmem
    _ = pathEnergy F w₁ / a + pathEnergy F w₂ / (1 - a) :=
      pathEnergy_concat w₁ w₂ ha0 ha1 F h₁.1 h₂.1 hmatch
    _ ≤ _ := hbound

/-- Triangle inequality for the Finsler distance. -/
theorem dist_triangle (F : ReversibleMetric n) {p q r : Ambient n}
    (hpq : (pathsBetween n p q).Nonempty) (hqr : (pathsBetween n q r).Nonempty) :
    dist F p r ≤ dist F p q + dist F q r := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  set η := ε / 4 with hη
  have hη0 : 0 < η := by positivity
  -- near-optimal paths
  have hsq : ∀ {x y : Ambient n}, (pathsBetween n x y).Nonempty →
      ∃ w ∈ pathsBetween n x y, Real.sqrt (pathEnergy F w) < dist F x y + η := by
    intro x y hne
    have hlt : minEnergy F x y < (dist F x y + η) ^ 2 := by
      rw [← dist_sq F x y]
      have := dist_nonneg F x y
      nlinarith
    obtain ⟨w, hw, hE⟩ := exists_lt_of_lt F hne hlt
    refine ⟨w, hw, ?_⟩
    rw [Real.sqrt_lt' (add_pos_of_nonneg_of_pos (dist_nonneg F x y) hη0)]
    exact hE
  obtain ⟨w₁, h₁, hE₁⟩ := hsq hpq
  obtain ⟨w₂, h₂, hE₂⟩ := hsq hqr
  have hT := minEnergy_triangle_aux F h₁ h₂ hη0
  have hpos : 0 ≤ Real.sqrt (pathEnergy F w₁) + Real.sqrt (pathEnergy F w₂) + 2 * η := by
    positivity
  have hd : dist F p r ≤ Real.sqrt (pathEnergy F w₁) + Real.sqrt (pathEnergy F w₂) + 2 * η := by
    unfold dist
    calc Real.sqrt (minEnergy F p r)
        ≤ Real.sqrt ((Real.sqrt (pathEnergy F w₁) + Real.sqrt (pathEnergy F w₂) + 2 * η) ^ 2) :=
          Real.sqrt_le_sqrt hT
      _ = _ := Real.sqrt_sq hpos
  linarith

end Triangle

section Lower

/-- On the unit interval, the squared mean of a square-integrable function is at most its mean
square. -/
theorem sq_integral_le_integral_sq {g : ℝ → ℝ} (hg : MemLp g 2 intervalMeasure) :
    (∫ t, g t ∂intervalMeasure) ^ 2 ≤ ∫ t, g t ^ 2 ∂intervalMeasure := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  set m := ∫ t, g t ∂intervalMeasure with hm
  have hi : Integrable g intervalMeasure := hg.integrable (by norm_num)
  have hi2 : Integrable (fun t => g t ^ 2) intervalMeasure := hg.integrable_sq
  have hnonneg : 0 ≤ ∫ t, (g t - m) ^ 2 ∂intervalMeasure :=
    integral_nonneg fun t => sq_nonneg _
  have hexp : (fun t => (g t - m) ^ 2) = fun t => g t ^ 2 - (2 * m) * g t + m ^ 2 := by
    funext t
    ring
  have hint : ∫ t, (g t - m) ^ 2 ∂intervalMeasure = (∫ t, g t ^ 2 ∂intervalMeasure) - m ^ 2 := by
    have hA : Integrable (fun t => g t ^ 2 - 2 * m * g t) intervalMeasure :=
      hi2.sub (hi.const_mul (2 * m))
    have hB : Integrable (fun _ : ℝ => m ^ 2) intervalMeasure := integrable_const _
    have hC : Integrable (fun t => 2 * m * g t) intervalMeasure := hi.const_mul (2 * m)
    rw [hexp, integral_add hA hB, integral_sub hi2 hC, integral_const_mul, integral_const,
      probReal_univ, one_smul, ← hm]
    ring
  linarith

theorem norm_sub_sq_le (w : Space n) :
    ‖continuousRepresentative w 1 - continuousRepresentative w 0‖ ^ 2 ≤
      ∫ t, ‖velocity w t‖ ^ 2 ∂intervalMeasure := by
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hdiff := trace_difference w
  change continuousRepresentative w 1 - continuousRepresentative w 0 = _ at hdiff
  have hint : ∫ x in (0 : ℝ)..1, velocity w x = ∫ t, velocity w t ∂intervalMeasure := by
    change _ = ∫ t in Ioo (0 : ℝ) 1, velocity w t
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [hdiff, hint]
  have hnorm : ‖∫ t, velocity w t ∂intervalMeasure‖ ≤ ∫ t, ‖velocity w t‖ ∂intervalMeasure :=
    norm_integral_le_integral_norm _
  have hmem : MemLp (fun t => ‖velocity w t‖) 2 intervalMeasure := (Lp.memLp (velocity w)).norm
  have hj := sq_integral_le_integral_sq hmem
  have h0 : 0 ≤ ‖∫ t, velocity w t ∂intervalMeasure‖ := norm_nonneg _
  calc ‖∫ t, velocity w t ∂intervalMeasure‖ ^ 2 ≤ (∫ t, ‖velocity w t‖ ∂intervalMeasure) ^ 2 :=
        pow_le_pow_left₀ h0 hnorm 2
    _ ≤ _ := hj

/-- The round comparison: some c > 0 with c‖p − q‖² ≤ e(p,q) whenever paths exist. -/
theorem exists_minEnergy_lower (F : ReversibleMetric n) :
    ∃ c : ℝ, 0 < c ∧ ∀ p q : Ambient n, (pathsBetween n p q).Nonempty →
      c * ‖q - p‖ ^ 2 ≤ minEnergy F p q := by
  obtain ⟨c, C, hc, _hC, hb⟩ := exists_pathEnergy_bounds F
  refine ⟨c, hc, ?_⟩
  intro p q hne
  apply le_csInf (hne.image _)
  rintro _ ⟨w, hw, rfl⟩
  have h1 := (hb w hw.1).1
  have h2 := norm_sub_sq_le w
  rw [hw.2.1, hw.2.2] at h2
  calc c * ‖q - p‖ ^ 2 ≤ c * ∫ t, ‖velocity w t‖ ^ 2 ∂intervalMeasure :=
        mul_le_mul_of_nonneg_left h2 hc.le
    _ ≤ _ := h1

theorem eq_of_dist_eq_zero (F : ReversibleMetric n) {p q : Ambient n}
    (hne : (pathsBetween n p q).Nonempty) (h : dist F p q = 0) : p = q := by
  obtain ⟨c, hc, hlow⟩ := exists_minEnergy_lower F
  have h1 := hlow p q hne
  rw [← dist_sq, h] at h1
  have h2 : ‖q - p‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < c * ‖q - p‖ ^ 2 := mul_pos hc hcon
    linarith
  have h3 : ‖q - p‖ = 0 := by
    have := sq_nonneg ‖q - p‖
    nlinarith [norm_nonneg (q - p)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp h3)).symm

end Lower


section Upper

open Finsler.RationalSphereCurve Finsler.SobolevSphereChart Finsler.SobolevOfPrimitive

/-- The inverse stereographic image of the segment from 0 to the stereographic image of q. -/
def segCurve (p q : Ambient n) (τ : ℝ) : Ambient n := ratMap 1 (p, τ • stereo p q)

/-- Its velocity. -/
def segVel (p q : Ambient n) (τ : ℝ) : Ambient n :=
  ratDeriv 1 (p, τ • stereo p q) (0, stereo p q)

theorem segCurve_hasDerivAt (p q : Ambient n) (τ : ℝ) :
    HasDerivAt (segCurve p q) (segVel p q τ) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => (p, τ • stereo p q)) ((0 : Ambient n), (1 : ℝ) • stereo p q)
      τ := (hasDerivAt_const τ p).prodMk ((hasDerivAt_id' τ).smul_const (stereo p q))
  have h2 := (ratMap_hasFDerivAt (n := n) 1 (p, τ • stereo p q)).comp_hasDerivAt τ h1
  rw [one_smul] at h2
  exact h2

theorem segCurve_continuous (p q : Ambient n) : Continuous (segCurve p q) :=
  continuous_iff_continuousAt.mpr fun τ => (segCurve_hasDerivAt p q τ).continuousAt

theorem segVel_continuous (p q : Ambient n) : Continuous (segVel p q) := by
  have hf : fderiv ℝ (ratMap (n := n) 1) = fun z => ratDeriv 1 z := funext (ratMap_fderiv 1)
  have hc : Continuous (fun z : Ambient n × Ambient n => ratDeriv (n := n) 1 z) := by
    have h := (ratMap_contDiff (n := n) 1).continuous_fderiv (by norm_num)
    rw [hf] at h
    exact h
  exact (hc.comp (continuous_const.prodMk (continuous_id.smul continuous_const))).clm_apply
    continuous_const

theorem segCurve_zero (p q : Ambient n) : segCurve p q 0 = p := by
  simp [segCurve, ratMap, aFun]

theorem segCurve_one {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hs : -1 < ⟪q, p⟫) :
    segCurve p q 1 = q := by
  rw [segCurve, one_smul]
  exact ratMap_stereo hp hq hs

theorem inner_segment {p q : Ambient n} (hp : ‖p‖ = 1) (τ : ℝ) :
    ⟪p, τ • stereo p q⟫ = 0 := by
  have h0 : ⟪stereo p q, p⟫ = 0 := inner_stereo hp
  rw [real_inner_smul_right, real_inner_comm, h0, mul_zero]

theorem norm_segCurve {p q : Ambient n} (hp : ‖p‖ = 1) (τ : ℝ) : ‖segCurve p q τ‖ = 1 :=
  norm_ratMap hp (inner_segment hp τ)

theorem norm_segVel_le {p q : Ambient n} (hp : ‖p‖ = 1) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ‖segVel p q τ‖ ≤ (1 + ‖stereo p q‖ + ‖stereo p q‖ ^ 2 / 4) * ‖stereo p q‖ := by
  have hM : ‖τ • stereo p q‖ ≤ ‖stereo p q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hτ.2
  have hb := ratDeriv_sub_bound (r := 1) (by norm_num) hp (inner_segment hp τ)
    (norm_nonneg (stereo p q)) hM (0 : Ambient n) (stereo p q)
  simp only [sub_zero, one_smul, norm_zero, mul_zero, zero_add, one_pow, one_mul] at hb
  unfold segVel
  calc ‖ratDeriv 1 (p, τ • stereo p q) (0, stereo p q)‖
      = ‖(ratDeriv 1 (p, τ • stereo p q) (0, stereo p q) - stereo p q) + stereo p q‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖ratDeriv 1 (p, τ • stereo p q) (0, stereo p q) - stereo p q‖ + ‖stereo p q‖ :=
        norm_add_le _ _
    _ ≤ (‖stereo p q‖ ^ 2 / 4 + ‖stereo p q‖) * ‖stereo p q‖ + ‖stereo p q‖ := by linarith
    _ = _ := by ring

theorem norm_stereo_sq_le {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hpq : ‖q - p‖ ≤ 1) : ‖stereo p q‖ ^ 2 ≤ 2 * ‖q - p‖ ^ 2 := by
  have hdist : ‖q - p‖ ^ 2 = 2 - 2 * ⟪q, p⟫ := by
    rw [norm_sub_sq_real, hp, hq]
    ring
  have hs : 0 ≤ ⟪q, p⟫ := by
    have h1 : ‖q - p‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (q - p)]
    linarith
  rw [norm_sq_stereo hp hq (by linarith), hdist]
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem segVel_sq_le {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ‖q - p‖ ≤ 1)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) : ‖segVel p q τ‖ ^ 2 ≤ 32 * ‖q - p‖ ^ 2 := by
  have hy := norm_stereo_sq_le hp hq hpq
  have hy0 : 0 ≤ ‖stereo p q‖ := norm_nonneg _
  have hy2 : ‖stereo p q‖ ≤ 2 := by nlinarith [norm_nonneg (q - p)]
  have hv := norm_segVel_le (q := q) hp hτ
  have hcoef : 1 + ‖stereo p q‖ + ‖stereo p q‖ ^ 2 / 4 ≤ 4 := by nlinarith
  have hv' : ‖segVel p q τ‖ ≤ 4 * ‖stereo p q‖ :=
    hv.trans (mul_le_mul_of_nonneg_right hcoef hy0)
  have h0 : 0 ≤ ‖segVel p q τ‖ := norm_nonneg _
  nlinarith

theorem segCurve_eq_add_integral (p q : Ambient n) (t : ℝ) :
    segCurve p q t = segCurve p q 0 + ∫ s in (0 : ℝ)..t, segVel p q s := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => segCurve_hasDerivAt p q x)
    ((segVel_continuous p q).intervalIntegrable 0 t)]
  abel

/-- The stereographic segment as an actual graph element. -/
def segPath (p q : Ambient n) : Space n :=
  ofPrimitive (segCurve_continuous p q).continuousOn
    (memLp_of_continuousOn (segVel_continuous p q).continuousOn)
    (fun t _ => segCurve_eq_add_integral p q t)

theorem segPath_mem {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : ‖q - p‖ ≤ 1) :
    segPath p q ∈ pathsBetween n p q := by
  have hs : -1 < ⟪q, p⟫ := by
    have hdist : ‖q - p‖ ^ 2 = 2 - 2 * ⟪q, p⟫ := by
      rw [norm_sub_sq_real, hp, hq]
      ring
    nlinarith [norm_nonneg (q - p)]
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    rw [segPath, representative_ofPrimitive _ _ _ ht]
    exact norm_segCurve hp t
  · rw [segPath, representative_ofPrimitive _ _ _ (left_mem_Icc.mpr zero_le_one)]
    exact segCurve_zero p q
  · rw [segPath, representative_ofPrimitive _ _ _ (right_mem_Icc.mpr zero_le_one)]
    exact segCurve_one hp hq hs

/-- Nearby points are joined by sphere paths with energy O(‖q − p‖²). -/
theorem exists_minEnergy_upper (F : ReversibleMetric n) :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : Ambient n, ‖p‖ = 1 → ‖q‖ = 1 → ‖q - p‖ ≤ 1 →
      (pathsBetween n p q).Nonempty ∧ minEnergy F p q ≤ C * ‖q - p‖ ^ 2 := by
  obtain ⟨c, C, _hc, hC, hb⟩ := exists_pathEnergy_bounds F
  refine ⟨32 * C, by positivity, ?_⟩
  intro p q hp hq hpq
  have hmem := segPath_mem hp hq hpq
  refine ⟨⟨_, hmem⟩, (minEnergy_le F hmem).trans ?_⟩
  let : IsProbabilityMeasure intervalMeasure := intervalMeasure_probability
  have hvel : ∫ t, ‖velocity (segPath p q) t‖ ^ 2 ∂intervalMeasure ≤ 32 * ‖q - p‖ ^ 2 := by
    have hae : ∀ᵐ t ∂intervalMeasure, ‖velocity (segPath p q) t‖ ^ 2 ≤ 32 * ‖q - p‖ ^ 2 := by
      filter_upwards [velocity_ofPrimitive_ae (segCurve_continuous p q).continuousOn
        (memLp_of_continuousOn (segVel_continuous p q).continuousOn)
        (fun t _ => segCurve_eq_add_integral p q t),
        ae_restrict_mem measurableSet_Ioo] with t hv ht
      rw [show velocity (segPath p q) t = segVel p q t from hv]
      exact segVel_sq_le hp hq hpq (Ioo_subset_Icc_self ht)
    calc ∫ t, ‖velocity (segPath p q) t‖ ^ 2 ∂intervalMeasure
        ≤ ∫ _t, 32 * ‖q - p‖ ^ 2 ∂intervalMeasure :=
          integral_mono_ae (integrable_velocity_sq _) (integrable_const _) hae
      _ = 32 * ‖q - p‖ ^ 2 := by rw [integral_const, probReal_univ, one_smul]
  calc pathEnergy F (segPath p q) ≤ C * ∫ t, ‖velocity (segPath p q) t‖ ^ 2 ∂intervalMeasure :=
        (hb _ hmem.1).2
    _ ≤ C * (32 * ‖q - p‖ ^ 2) := mul_le_mul_of_nonneg_left hvel hC.le
    _ = 32 * C * ‖q - p‖ ^ 2 := by ring

theorem exists_dist_upper (F : ReversibleMetric n) :
    ∃ K : ℝ, 0 < K ∧ ∀ p q : Ambient n, ‖p‖ = 1 → ‖q‖ = 1 → ‖q - p‖ ≤ 1 →
      dist F p q ≤ K * ‖q - p‖ := by
  obtain ⟨C, hC, hup⟩ := exists_minEnergy_upper F
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  intro p q hp hq hpq
  have h := (hup p q hp hq hpq).2
  unfold dist
  calc Real.sqrt (minEnergy F p q) ≤ Real.sqrt (C * ‖q - p‖ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt C * ‖q - p‖ := by
      rw [Real.sqrt_mul hC.le, Real.sqrt_sq (norm_nonneg _)]

end Upper

section Connected

theorem one_lt_rank (hn : 1 ≤ n) : 1 < Module.rank ℝ (Ambient n) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast (by omega : 1 < n + 1)

theorem pathsBetween_trans {p q r : Ambient n} (hpq : (pathsBetween n p q).Nonempty)
    (hqr : (pathsBetween n q r).Nonempty) : (pathsBetween n p r).Nonempty := by
  obtain ⟨w₁, h₁⟩ := hpq
  obtain ⟨w₂, h₂⟩ := hqr
  have hmatch : continuousRepresentative w₁ 1 = continuousRepresentative w₂ 0 := by
    rw [h₁.2.2, h₂.2.1]
  have ha0 : (0 : ℝ) < 1 / 2 := by norm_num
  have ha1 : (1 / 2 : ℝ) < 1 := by norm_num
  exact ⟨concat w₁ w₂ ha0 ha1, concat_mem w₁ w₂ ha0 ha1 h₁.1 h₂.1 hmatch,
    (representative_concat_zero w₁ w₂ ha0 ha1).trans h₁.2.1,
    (representative_concat_one w₁ w₂ ha0 ha1 hmatch).trans h₂.2.2⟩

/-- Any two points of the sphere are joined by an actual H¹ sphere path when n ≥ 1. -/
theorem pathsBetween_nonempty (hn : 1 ≤ n) {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    (pathsBetween n p q).Nonempty := by
  have hS := isPreconnected_sphere (one_lt_rank hn) (0 : Ambient n) 1
  have hpS : p ∈ Metric.sphere (0 : Ambient n) 1 := by simpa using hp
  have hqS : q ∈ Metric.sphere (0 : Ambient n) 1 := by simpa using hq
  refine hS.induction₂ (fun x y => (pathsBetween n x y).Nonempty) ?_ ?_ ?_ hpS hqS
  · intro x hx
    have hx1 : ‖x‖ = 1 := by simpa using hx
    have hball : Metric.ball x 1 ∈ 𝓝[Metric.sphere (0 : Ambient n) 1] x :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos)
    filter_upwards [hball, self_mem_nhdsWithin] with y hy hyS
    have hy1 : ‖y‖ = 1 := by simpa using hyS
    have hxy : ‖y - x‖ ≤ 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact hy.le
    exact ⟨segPath x y, segPath_mem hx1 hy1 hxy⟩
  · intro x y z _ _ _ hxy hyz
    exact pathsBetween_trans hxy hyz
  · intro x y _ _ hxy
    obtain ⟨w, hw⟩ := hxy
    exact ⟨reverseData w, reverseData_mem_pathsBetween hw⟩

end Connected


section Metric

theorem minEnergy_self (F : ReversibleMetric n) {p : Ambient n} (hp : ‖p‖ = 1) :
    minEnergy F p p = 0 := by
  obtain ⟨C, _hC, hup⟩ := exists_minEnergy_upper F
  have h := (hup p p hp hp (by simp)).2
  rw [sub_self, norm_zero] at h
  have h0 := minEnergy_nonneg F p p
  have hz : C * (0 : ℝ) ^ 2 = 0 := by ring
  linarith

theorem dist_self (F : ReversibleMetric n) {p : Ambient n} (hp : ‖p‖ = 1) : dist F p p = 0 := by
  unfold dist
  rw [minEnergy_self F hp, Real.sqrt_zero]

/-- The triangle inequality on the sphere, n ≥ 1. -/
theorem dist_triangle_sphere (F : ReversibleMetric n) (hn : 1 ≤ n) {p q r : Ambient n}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1) : dist F p r ≤ dist F p q + dist F q r :=
  dist_triangle F (pathsBetween_nonempty hn hp hq) (pathsBetween_nonempty hn hq hr)

/-- Points of the sphere at Finsler distance zero coincide, n ≥ 1. -/
theorem eq_of_dist_eq_zero_sphere (F : ReversibleMetric n) (hn : 1 ≤ n) {p q : Ambient n}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (h : dist F p q = 0) : p = q :=
  eq_of_dist_eq_zero F (pathsBetween_nonempty hn hp hq) h

/-- The round lower bound for the Finsler distance on the sphere, n ≥ 1. -/
theorem exists_dist_lower (F : ReversibleMetric n) (hn : 1 ≤ n) :
    ∃ k : ℝ, 0 < k ∧ ∀ p q : Ambient n, ‖p‖ = 1 → ‖q‖ = 1 → k * ‖q - p‖ ≤ dist F p q := by
  obtain ⟨c, hc, hlow⟩ := exists_minEnergy_lower F
  refine ⟨Real.sqrt c, Real.sqrt_pos.mpr hc, ?_⟩
  intro p q hp hq
  have h := hlow p q (pathsBetween_nonempty hn hp hq)
  unfold dist
  calc Real.sqrt c * ‖q - p‖ = Real.sqrt (c * ‖q - p‖ ^ 2) := by
        rw [Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ Real.sqrt (minEnergy F p q) := Real.sqrt_le_sqrt h

/-- Sampling estimate in distance form for actual sphere loops. -/
theorem dist_sample_le (F : ReversibleMetric n) (u : SphereLoop n) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    dist F (continuousRepresentative (u.data : Space n) s)
        (continuousRepresentative (u.data : Space n) t) ≤
      Real.sqrt ((t - s) * Finsler.SobolevEnergy.energy F u) :=
  Real.sqrt_le_sqrt (minEnergy_sample_loop_le F u hs ht hst)

end Metric

end

end Finsler.SphereDistance
