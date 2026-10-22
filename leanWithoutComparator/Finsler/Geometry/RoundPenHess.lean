module

public import Finsler.Geometry.RoundNondeg

/-! The penalized round polygon energy at the regular m-gons: smoothness, criticality and the
second derivative in all directions.

* Near a polygon with nonzero vertices whose normalized consecutive vertices are neither equal
  nor antipodal, the round minimal energy of each edge is arccos² of the normalized inner
  product, so the penalized energy pen = E + log-penalty is C^∞ there.
* The penalty Σ log² ‖Q_i‖ has vanishing derivative at polygons of unit vectors and second
  derivative 2 Σ ⟪Q_i, v_i⟫² there (only the radial parts are seen).
* The normalized polygon energy E is invariant under positive rescalings of the vertices. At a
  regular m-gon every rescaled polygon is critical as well, so the derivative of E vanishes
  along every radial line through the polygon, and the second derivative of E vanishes on radial
  directions.
* Hence, for an increment B = (ρ_i Q_i + β_i t_i) + w with t_i the unit tangents of the
  regular polygon and w normal to its plane,

    D²pen(B, B) = 2N Σ (β_{i+1} − β_i)² + 2 Σ ρ_i² + D²E(w, w). -/

@[expose] public section

namespace Finsler.RoundPenHess

open Finsler.SphereGeometry Finsler.Geometry Finsler.RoundEnergy Finsler.RoundPolygon
open Finsler.RoundHessian Finsler.RoundModes Finsler.RoundNondeg Finsler.PolygonSmooth
open Finsler.SphereRetraction Finsler.IndexComparison Finsler.AmbientPenalty
open Finsler.EnergySphereSmooth
open Finsler.SphereDistance (minEnergy)
open Finset Filter Set
open scoped RealInnerProductSpace Real Topology ContDiff

noncomputable section

variable {n : ℕ} {N : ℕ} [NeZero N]

/-! ### Smoothness -/

/-- The normalized inner product of two ambient vectors. -/
def nip (x : Ambient n × Ambient n) : ℝ := ⟪‖x.1‖⁻¹ • x.1, ‖x.2‖⁻¹ • x.2⟫

theorem nip_contDiffAt {x : Ambient n × Ambient n} (h1 : x.1 ≠ 0) (h2 : x.2 ≠ 0) :
    ContDiffAt ℝ ∞ nip x := by
  have hf : ContDiffAt ℝ ∞ (fun y : Ambient n × Ambient n => ‖y.1‖⁻¹ • y.1) x :=
    ((contDiffAt_fst.norm ℝ h1).inv (norm_ne_zero_iff.mpr h1)).smul contDiffAt_fst
  have hg : ContDiffAt ℝ ∞ (fun y : Ambient n × Ambient n => ‖y.2‖⁻¹ • y.2) x :=
    ((contDiffAt_snd.norm ℝ h2).inv (norm_ne_zero_iff.mpr h2)).smul contDiffAt_snd
  exact hf.inner ℝ hg

theorem nip_continuousAt {x : Ambient n × Ambient n} (h1 : x.1 ≠ 0) (h2 : x.2 ≠ 0) :
    ContinuousAt nip x :=
  (nip_contDiffAt h1 h2).continuousAt

theorem coe_normalize_eq {v : Ambient n} (hv : v ≠ 0) :
    ((normalize v : Sphere n) : Ambient n) = ‖v‖⁻¹ • v := coe_normalize hv

theorem norm_inv_smul_self {v : Ambient n} (hv : v ≠ 0) : ‖‖v‖⁻¹ • v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- Near a pair of nonzero vectors with non-antipodal directions the round extended minimal
energy is arccos² of the normalized inner product. -/
theorem ambientMinEnergy_eventuallyEq {x : Ambient n × Ambient n} (h1 : x.1 ≠ 0) (h2 : x.2 ≠ 0)
    (h3 : nip x ≠ -1) :
    ambientMinEnergy (roundMetric n) =ᶠ[𝓝 x] fun y => Real.arccos (nip y) ^ 2 := by
  have e1 : ∀ᶠ y in 𝓝 x, y.1 ≠ 0 :=
    continuous_fst.continuousAt.eventually (isOpen_ne.mem_nhds h1)
  have e2 : ∀ᶠ y in 𝓝 x, y.2 ≠ 0 :=
    continuous_snd.continuousAt.eventually (isOpen_ne.mem_nhds h2)
  have e3 : ∀ᶠ y in 𝓝 x, nip y ≠ -1 :=
    (nip_continuousAt h1 h2).eventually (isOpen_ne.mem_nhds h3)
  filter_upwards [e1, e2, e3] with y hy1 hy2 hy3
  unfold ambientMinEnergy
  rw [coe_normalize_eq hy1, coe_normalize_eq hy2]
  exact minEnergy_round (norm_inv_smul_self hy1) (norm_inv_smul_self hy2) hy3

/-- The round extended minimal energy is smooth at pairs of nonzero vectors with neither equal
nor antipodal directions. -/
theorem ambientMinEnergy_contDiffAt {x : Ambient n × Ambient n} (h1 : x.1 ≠ 0) (h2 : x.2 ≠ 0)
    (h3 : nip x ≠ -1) (h4 : nip x ≠ 1) : ContDiffAt ℝ ∞ (ambientMinEnergy (roundMetric n)) x := by
  have h : ContDiffAt ℝ ∞ (fun y => Real.arccos (nip y) ^ 2) x :=
    ((Real.contDiffAt_arccos h3 h4).comp x (nip_contDiffAt h1 h2)).pow 2
  exact h.congr_of_eventuallyEq (ambientMinEnergy_eventuallyEq h1 h2 h3)

/-- The polygons with nonzero vertices whose normalized edges are nondegenerate. -/
def good (N : ℕ) : Set (ZMod N → Ambient n) :=
  {Q | (∀ i, Q i ≠ 0) ∧ ∀ i, nip (Q i, Q (i + 1)) ≠ -1 ∧ nip (Q i, Q (i + 1)) ≠ 1}

theorem good_isOpen : IsOpen (good (n := n) N) := by
  rw [isOpen_iff_mem_nhds]
  rintro Q ⟨h0, h1⟩
  have e0 : ∀ᶠ P in 𝓝 Q, ∀ i, P i ≠ 0 := by
    rw [eventually_all]
    intro i
    exact (continuous_apply i).continuousAt.eventually (isOpen_ne.mem_nhds (h0 i))
  have e1 : ∀ᶠ P in 𝓝 Q, ∀ i, nip (P i, P (i + 1)) ≠ -1 ∧ nip (P i, P (i + 1)) ≠ 1 := by
    rw [eventually_all]
    intro i
    have hc : ContinuousAt (fun P : ZMod N → Ambient n => nip (P i, P (i + 1))) Q :=
      ContinuousAt.comp (g := nip) (f := fun P : ZMod N → Ambient n => (P i, P (i + 1)))
        (nip_continuousAt (h0 i) (h0 (i + 1)))
        ((continuous_apply i).prodMk (continuous_apply (i + 1))).continuousAt
    exact hc.eventually ((isOpen_ne.inter isOpen_ne).mem_nhds (h1 i))
  filter_upwards [e0, e1] with P hP0 hP1
  exact ⟨hP0, hP1⟩

/-- The normalized polygon energy is smooth on the good polygons. -/
theorem polyEnergyN_contDiffAt {Q : ZMod N → Ambient n} (hQ : Q ∈ good N) :
    ContDiffAt ℝ ∞ (polyEnergyN (roundMetric n) N) Q := by
  unfold polyEnergyN
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro k _
  have hproj : ContDiffAt ℝ ∞ (fun P : ZMod N → Ambient n => (P k, P ((k : ZMod N) + 1))) Q :=
    ((contDiff_apply ℝ (Ambient n) (k : ZMod N)).prodMk
      (contDiff_apply ℝ (Ambient n) ((k : ZMod N) + 1))).contDiffAt
  exact ContDiffAt.comp (g := ambientMinEnergy (roundMetric n))
    (f := fun P : ZMod N → Ambient n => (P k, P ((k : ZMod N) + 1))) (x := Q)
    (ambientMinEnergy_contDiffAt (hQ.1 _) (hQ.1 _) (hQ.2 _).1 (hQ.2 _).2) hproj

/-- The log-penalty is smooth at polygons with nonzero vertices. -/
theorem logPen_contDiffAt {Q : ZMod N → Ambient n} (hQ : ∀ i, Q i ≠ 0) :
    ContDiffAt ℝ ∞ (logPen (n := n) (N := N)) Q := by
  unfold logPen
  apply ContDiffAt.sum
  intro j _
  have h1 : ContDiffAt ℝ ∞ (fun P : ZMod N → Ambient n => ‖P j‖) Q :=
    (contDiff_apply ℝ (Ambient n) j).contDiffAt.norm ℝ (hQ j)
  have h2 : ContDiffAt ℝ ∞ (fun P : ZMod N → Ambient n => Real.log ‖P j‖) Q :=
    ContDiffAt.comp (g := Real.log) (f := fun P : ZMod N → Ambient n => ‖P j‖) Q
      (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr (hQ j))) h1
  exact h2.pow 2

/-- **The penalized round energy is smooth on the good polygons.** -/
theorem pen_contDiffAt {Q : ZMod N → Ambient n} (hQ : Q ∈ good N) (lam : ℝ) :
    ContDiffAt ℝ ∞ (pen (roundMetric n) N lam) Q :=
  (polyEnergyN_contDiffAt hQ).add (contDiffAt_const.mul (logPen_contDiffAt hQ.1))

/-- Unit vectors with inner product strictly between −1 and 1 give a good edge. -/
theorem nip_of_unit {p q : Ambient n} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : nip (p, q) = ⟪p, q⟫ := by
  unfold nip
  simp [hp, hq]

/-- The regular m-gons with 0 < 2m < N are good. -/
theorem regular_mem_good {m : ℕ} (hm : 0 < m) (hmN : 2 * m < N) {x u : Ambient n} (hx : ‖x‖ = 1)
    (hu : ‖u‖ = 1) (hxu : ⟪x, u⟫ = 0) : regular N m x u ∈ good N := by
  have hQ := norm_regular (N := N) (m := m) hx hu hxu
  have hb := cos_ang_bounds (N := N) hm hmN
  refine ⟨fun i h => by have := hQ i; rw [h, norm_zero] at this; exact zero_ne_one this, fun i => ?_⟩
  rw [nip_of_unit (hQ i) (hQ (i + 1)), inner_regular hx hu hxu]
  exact ⟨ne_of_gt hb.1, ne_of_lt hb.2⟩

/-! ### The log-penalty at unit polygons -/

theorem hasDerivAt_log_norm_line {P V : Ambient n} (hP : ‖P‖ = 1) :
    HasDerivAt (fun t : ℝ => Real.log ‖P + t • V‖) ⟪P, V⟫ 0 := by
  have hq : HasDerivAt (fun t : ℝ => ‖P + t • V‖ ^ 2) (2 * ⟪P, V⟫) 0 := by
    have hl : HasDerivAt (fun t : ℝ => P + t • V) V 0 := hasDerivAt_line P V
    have h := hl.norm_sq
    simp only [zero_smul, add_zero] at h
    convert h using 1 <;> try simp [real_inner_comm]
  have h0 : ‖P + (0 : ℝ) • V‖ ^ 2 = 1 := by simp [hP]
  have hlog : HasDerivAt (fun t : ℝ => Real.log (‖P + t • V‖ ^ 2)) (2 * ⟪P, V⟫ / 1) 0 := by
    have := hq.log (by rw [h0]; norm_num)
    rwa [h0] at this
  have heq : (fun t : ℝ => Real.log ‖P + t • V‖) = fun t => (1 / 2 : ℝ) * Real.log (‖P + t • V‖ ^ 2) := by
    funext t
    rw [Real.log_pow]
    push_cast
    ring
  rw [heq]
  convert hlog.const_mul (1 / 2 : ℝ) using 1
  ring

/-- The derivative of the log-penalty vanishes at polygons of unit vectors. -/
theorem fderiv_logPen_unit {Q : ZMod N → Ambient n} (hQ : ∀ i, ‖Q i‖ = 1) :
    fderiv ℝ (logPen (n := n) (N := N)) Q = 0 := by
  have h0 : ∀ i, Q i ≠ 0 := fun i h => by have := hQ i; rw [h, norm_zero] at this; exact zero_ne_one this
  have hd : HasFDerivAt (logPen (n := n) (N := N)) (0 : (ZMod N → Ambient n) →L[ℝ] ℝ) Q := by
    unfold logPen
    have : (0 : (ZMod N → Ambient n) →L[ℝ] ℝ) = ∑ j : ZMod N, (0 : (ZMod N → Ambient n) →L[ℝ] ℝ) := by
      simp
    rw [this]
    apply HasFDerivAt.fun_sum
    intro j _
    have h1 : DifferentiableAt ℝ (fun P : ZMod N → Ambient n => Real.log ‖P j‖) Q :=
      (ContDiffAt.comp (g := Real.log) (f := fun P : ZMod N → Ambient n => ‖P j‖) (n := 1) Q
        (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr (h0 j)))
        ((contDiff_apply ℝ (Ambient n) j).contDiffAt.norm ℝ (h0 j))).differentiableAt
        (by simp)
    have h2 := h1.hasFDerivAt.pow 2
    have hz : Real.log ‖Q j‖ = 0 := by rw [hQ j, Real.log_one]
    simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      zero_smul] at h2
    convert h2 using 1
    simp
  exact hd.fderiv

/-- The second derivative of the log-penalty at a polygon of unit vectors. -/
theorem logPen_hessian {Q : ZMod N → Ambient n} (hQ : ∀ i, ‖Q i‖ = 1) (v : ZMod N → Ambient n) :
    fderiv ℝ (fderiv ℝ (logPen (n := n) (N := N))) Q v v = 2 * ∑ i, ⟪Q i, v i⟫ ^ 2 := by
  have h0 : ∀ i, Q i ≠ 0 := fun i h => by have := hQ i; rw [h, norm_zero] at this; exact zero_ne_one this
  have hC2 : ContDiffAt ℝ 2 (logPen (n := n) (N := N)) Q := (logPen_contDiffAt h0).of_le (by simp)
  have hT := tendsto_div_sq hC2 (fderiv_logPen_unit hQ) (hasDerivAt_line Q v) (by simp)
  -- the direct limit
  have hval : logPen Q = 0 := by
    unfold logPen
    simp [hQ]
  have hlim : Tendsto (fun t : ℝ => (logPen (Q + t • v) - logPen Q) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (∑ i, ⟪Q i, v i⟫ ^ 2)) := by
    have hi : ∀ i, Tendsto (fun t : ℝ => (Real.log ‖Q i + t • v i‖ / t) ^ 2) (𝓝[≠] 0)
        (𝓝 (⟪Q i, v i⟫ ^ 2)) := by
      intro i
      have hs := (hasDerivAt_log_norm_line (V := v i) (hQ i)).tendsto_slope_zero
      simp only [zero_add, zero_smul, add_zero, hQ i, Real.log_one, sub_zero] at hs
      have hs' : Tendsto (fun t : ℝ => Real.log ‖Q i + t • v i‖ / t) (𝓝[≠] 0) (𝓝 ⟪Q i, v i⟫) := by
        refine hs.congr fun t => ?_
        rw [smul_eq_mul, div_eq_inv_mul]
      exact hs'.pow 2
    have hsum := tendsto_finset_sum (Finset.univ : Finset (ZMod N)) fun i _ => hi i
    refine hsum.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hval, sub_zero]
    unfold logPen
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [div_pow]
  have huniq := tendsto_nhds_unique hT hlim
  linarith

/-! ### Radial invariance -/

theorem normalize_smul_pos {c : ℝ} (hc : 0 < c) (v : Ambient n) : normalize (c • v) = normalize v := by
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have hcv : c • v ≠ 0 := smul_ne_zero hc.ne' hv
    apply Subtype.ext
    rw [coe_normalize hcv, coe_normalize hv, norm_smul, Real.norm_of_nonneg hc.le, mul_inv,
      smul_smul, mul_comm, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

/-- The normalized polygon energy is invariant under positive rescalings of the vertices. -/
theorem polyEnergyN_scaleVert (F : ReversibleMetric n) (c : ZMod N → ℝ) (hc : ∀ i, 0 < c i)
    (Q : ZMod N → Ambient n) : polyEnergyN F N (fun i => c i • Q i) = polyEnergyN F N Q := by
  unfold polyEnergyN ambientMinEnergy
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [normalize_smul_pos (hc _)]

/-- The vertexwise scaling as a linear map. -/
def scaleL (c : ZMod N → ℝ) : (ZMod N → Ambient n) →L[ℝ] (ZMod N → Ambient n) :=
  ContinuousLinearMap.pi fun i => c i • ContinuousLinearMap.proj i

theorem scaleL_apply (c : ZMod N → ℝ) (Q : ZMod N → Ambient n) (i : ZMod N) :
    scaleL c Q i = c i • Q i := rfl

/-- The second derivative of E at a critical point vanishes on radial directions, if E is
invariant under positive vertex scalings. -/
theorem hessian_radial_zero {Q : ZMod N → Ambient n} {E : (ZMod N → Ambient n) → ℝ}
    (hinv : ∀ c : ZMod N → ℝ, (∀ i, 0 < c i) → ∀ P, E (scaleL c P) = E P)
    (hC2 : ContDiffAt ℝ 2 E Q) (hcrit : fderiv ℝ E Q = 0) (ρ : ZMod N → ℝ) :
    fderiv ℝ (fderiv ℝ E) Q (scaleL ρ Q) = 0 := by
  -- the derivative of E vanishes along the radial line
  have hdiff : ∀ᶠ P in 𝓝 Q, DifferentiableAt ℝ E P :=
    (hC2.eventually (by simp)).mono fun P hP => hP.differentiableAt (by simp)
  have hline : Tendsto (fun s : ℝ => Q + s • scaleL ρ Q) (𝓝 0) (𝓝 Q) := by
    have h : Continuous (fun s : ℝ => Q + s • scaleL ρ Q) := by fun_prop
    simpa using h.tendsto 0
  have hpos : ∀ᶠ s : ℝ in 𝓝 0, ∀ i, 0 < 1 + s * ρ i := by
    rw [eventually_all]
    intro i
    have h : Continuous (fun s : ℝ => 1 + s * ρ i) := by fun_prop
    exact h.continuousAt.eventually (lt_mem_nhds (by simp))
  have hzero : ∀ᶠ s : ℝ in 𝓝 0, fderiv ℝ E (Q + s • scaleL ρ Q) = 0 := by
    filter_upwards [hpos, hline.eventually hdiff] with s hs hd
    set c : ZMod N → ℝ := fun i => 1 + s * ρ i with hc
    have hQs : Q + s • scaleL ρ Q = scaleL c Q := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, scaleL_apply, hc, add_smul, one_smul, smul_smul]
    rw [hQs] at hd ⊢
    have hEc : E ∘ scaleL c = E := funext fun P => hinv c hs P
    have h1 : fderiv ℝ (E ∘ scaleL c) Q = (fderiv ℝ E (scaleL c Q)).comp (scaleL c) :=
      fderiv_comp Q hd (scaleL c).differentiableAt |>.trans (by rw [ContinuousLinearMap.fderiv])
    rw [hEc, hcrit] at h1
    ext v
    have hv : v = scaleL c (scaleL (fun i => (c i)⁻¹) v) := by
      funext i
      simp only [scaleL_apply, smul_smul]
      rw [mul_inv_cancel₀ (show c i ≠ 0 from (hs i).ne'), one_smul]
    rw [hv]
    have := congrArg (fun φ : (ZMod N → Ambient n) →L[ℝ] ℝ => φ (scaleL (fun i => (c i)⁻¹) v)) h1
    simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply] at this
    rw [← this]
    rfl
  -- its derivative at s = 0 is the second derivative on the radial direction
  have hF : HasFDerivAt (fderiv ℝ E) (fderiv ℝ (fderiv ℝ E) Q) Q :=
    ((hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => Q + s • scaleL ρ Q) (scaleL ρ Q) 0 := hasDerivAt_line _ _
  have hcomp : HasDerivAt (fun s : ℝ => fderiv ℝ E (Q + s • scaleL ρ Q))
      (fderiv ℝ (fderiv ℝ E) Q (scaleL ρ Q)) 0 := by
    exact HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hF hl (by simp)
  have hc0 : HasDerivAt (fun s : ℝ => fderiv ℝ E (Q + s • scaleL ρ Q)) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (0 : (ZMod N → Ambient n) →L[ℝ] ℝ)).congr_of_eventuallyEq hzero
  exact hcomp.unique hc0

end

end Finsler.RoundPenHess
