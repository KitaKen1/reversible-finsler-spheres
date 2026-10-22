module

public import TauCeti.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Averages along segments. For continuous linear maps `P`, `Q` of a normed space and a map `L`
into a normed space, `avg L P Q w` is the integral over `t ∈ [0, 1]` of `t • L (P w + t • Q w)`.
A property that holds near `0` holds on all these segments for `w` near `0`. If `L` is `C^n` at
`0`, the average is `C^n` at `0` (Tau Ceti's parametric integral over a compact parameter space,
which needs the integrand only near the segments); its value at `0` is `L 0 / 2`. If `P + Q = 1`
and a function `φ` is differentiable along the segment from `P w` to `w`, then `φ w - φ (P w)`
is the integral of the derivative along the segment (fundamental theorem of calculus). -/

@[expose] public section

namespace Finsler.SegmentAverage

open MeasureTheory Set Filter
open scoped Topology ContDiff

noncomputable section

/-- Lebesgue measure on the unit interval as a type. -/
def unitMeasure : Measure (Icc (0 : ℝ) 1) := Measure.comap Subtype.val volume

/-- The integral over the unit interval as a type is the interval integral. -/
theorem integral_unit {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (h : ℝ → G) :
    ∫ t : Icc (0 : ℝ) 1, h t ∂unitMeasure = ∫ t in (0 : ℝ)..1, h t := by
  rw [unitMeasure, integral_subtype_comap measurableSet_Icc h, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one]

theorem integrable_unit {G : Type*} [NormedAddCommGroup G] {h : ℝ → G}
    (hh : IntegrableOn h (Icc 0 1)) : Integrable (fun t : Icc (0 : ℝ) 1 => h t) unitMeasure := by
  have h1 : Integrable h (Measure.map Subtype.val unitMeasure) := by
    rw [unitMeasure, map_comap_subtype_coe measurableSet_Icc]
    exact hh
  exact ((MeasurableEmbedding.subtype_coe measurableSet_Icc).integrable_map_iff).mp h1

theorem integrable_coe : Integrable (fun t : Icc (0 : ℝ) 1 => (t : ℝ)) unitMeasure :=
  integrable_unit (h := fun t => t) continuous_id.integrableOn_Icc

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A property that holds near `0` holds along the segments `P w + t • Q w`, `t ∈ [0, 1]`, for
all `w` near `0`. -/
theorem eventually_segment {q : E → Prop} (h : ∀ᶠ x in 𝓝 (0 : E), q x) (P Q : E →L[ℝ] E) :
    ∀ᶠ w in 𝓝 (0 : E), ∀ t ∈ Icc (0 : ℝ) 1, q (P w + t • Q w) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h
  have hK : 0 < ‖P‖ + ‖Q‖ + 1 := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : E) (div_pos hε hK)] with w hw t ht
  apply hball
  rw [mem_ball_zero_iff] at hw ⊢
  have h2 : |t| ≤ 1 := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have h3 := P.le_opNorm w
  have h4 := Q.le_opNorm w
  have h5 : |t| * ‖Q w‖ ≤ 1 * (‖Q‖ * ‖w‖) := mul_le_mul h2 h4 (norm_nonneg _) zero_le_one
  have h1 : ‖P w + t • Q w‖ ≤ (‖P‖ + ‖Q‖ + 1) * ‖w‖ := by
    calc ‖P w + t • Q w‖ ≤ ‖P w‖ + ‖t • Q w‖ := norm_add_le _ _
      _ = ‖P w‖ + |t| * ‖Q w‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (‖P‖ + ‖Q‖ + 1) * ‖w‖ := by nlinarith [norm_nonneg w]
  calc ‖P w + t • Q w‖ ≤ (‖P‖ + ‖Q‖ + 1) * ‖w‖ := h1
    _ < (‖P‖ + ‖Q‖ + 1) * (ε / (‖P‖ + ‖Q‖ + 1)) := mul_lt_mul_of_pos_left hw hK
    _ = ε := mul_div_cancel₀ ε hK.ne'

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The average of `L` with weight `t` along the segments `P w + t • Q w`, `t ∈ [0, 1]`. -/
def avg (L : E → F) (P Q : E →L[ℝ] E) (w : E) : F :=
  ∫ t : Icc (0 : ℝ) 1, (t : ℝ) • L (P w + (t : ℝ) • Q w) ∂unitMeasure

/-- The average at `0` is half the value at `0`. -/
theorem avg_zero [CompleteSpace F] (L : E → F) (P Q : E →L[ℝ] E) :
    avg L P Q 0 = (1 / 2 : ℝ) • L 0 := by
  have h : ∫ t : Icc (0 : ℝ) 1, (t : ℝ) ∂unitMeasure = ∫ t in (0 : ℝ)..1, t :=
    integral_unit fun t => t
  have h' : avg L P Q 0 = ∫ t : Icc (0 : ℝ) 1, (t : ℝ) • L 0 ∂unitMeasure := by
    unfold avg
    simp only [map_zero, smul_zero, add_zero]
  rw [h', integral_smul_const, h, integral_id]
  norm_num

/-- The average of a map that is `C^n` at `0` is `C^n` at `0`. -/
theorem avg_contDiffAt {n : ℕ} {L : E → F} (hL : ContDiffAt ℝ n L 0) (P Q : E →L[ℝ] E) :
    ContDiffAt ℝ n (avg L P Q) 0 := by
  have hUopen : IsOpen {x : E | ContDiffAt ℝ n L x} :=
    isOpen_iff_mem_nhds.mpr fun x (hx : ContDiffAt ℝ n L x) => hx.eventually (by simp)
  have hcd : ContDiff ℝ n (fun z : E × ℝ => P z.1 + z.2 • Q z.1) := by fun_prop
  have hWopen : IsOpen ((fun z : E × ℝ => P z.1 + z.2 • Q z.1) ⁻¹' {x : E | ContDiffAt ℝ n L x}) :=
    hUopen.preimage hcd.continuous
  have hF : ContDiffOn ℝ ((n : ℕ∞) : WithTop ℕ∞)
      (fun z : E × ℝ => L (P z.1 + z.2 • Q z.1))
      ((fun z : E × ℝ => P z.1 + z.2 • Q z.1) ⁻¹' {x : E | ContDiffAt ℝ n L x}) := by
    intro z hz
    have h1 : ContDiffAt ℝ n L (P z.1 + z.2 • Q z.1) := hz
    have h2 : ContDiffAt ℝ n (fun z : E × ℝ => L (P z.1 + z.2 • Q z.1)) z :=
      h1.comp z hcd.contDiffAt
    exact_mod_cast h2.contDiffWithinAt
  obtain ⟨V, hV, hVopen, h0V⟩ :=
    eventually_nhds_iff.mp (eventually_segment (hL.eventually (by simp)) P Q)
  have h := TauCeti.contDiffOn_integral_smul_of_contDiffOn (μ := unitMeasure)
    (g := fun t : Icc (0 : ℝ) 1 => (t : ℝ)) (ι := fun t : Icc (0 : ℝ) 1 => (t : ℝ))
    (n := (n : ℕ∞)) integrable_coe continuous_subtype_val hWopen hF hVopen
    (fun w hw t => hV w hw t t.2)
  have h' : ContDiffAt ℝ ((n : ℕ∞) : WithTop ℕ∞) (avg L P Q) 0 :=
    h.contDiffAt (hVopen.mem_nhds h0V)
  exact_mod_cast h'

/-- The integrand of the average is integrable when `L` is continuous near the segment. -/
theorem integrable_avg {L : E → F} {P Q : E →L[ℝ] E} {w : E}
    (hL : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt L (P w + t • Q w)) :
    Integrable (fun t : Icc (0 : ℝ) 1 => (t : ℝ) • L (P w + (t : ℝ) • Q w)) unitMeasure := by
  refine integrable_unit (h := fun t : ℝ => t • L (P w + t • Q w)) ?_
  refine ContinuousOn.integrableOn_Icc fun t ht => ContinuousAt.continuousWithinAt ?_
  have hline : ContinuousAt (fun s : ℝ => P w + s • Q w) t := by fun_prop
  exact continuousAt_id.smul
    (ContinuousAt.comp (f := fun s : ℝ => P w + s • Q w) (x := t) (hL t ht) hline)

/-- The derivative along the segment of a function that is differentiable at one of its points. -/
theorem hasDerivAt_segment {φ : E → ℝ} {φ' : E →L[ℝ] ℝ} {P Q : E →L[ℝ] E} {w : E} {t : ℝ}
    (h : HasFDerivAt φ φ' (P w + t • Q w)) :
    HasDerivAt (fun s : ℝ => φ (P w + s • Q w)) (φ' (Q w)) t := by
  have hline : HasDerivAt (fun s : ℝ => P w + s • Q w) (Q w) t := by
    simpa using ((hasDerivAt_id t).smul_const (Q w)).const_add (P w)
  exact h.comp_hasDerivAt t hline

/-- The fundamental theorem of calculus along the segment from `P w` to `w`. -/
theorem sub_eq_integral {φ : E → ℝ} {P Q : E →L[ℝ] E} (hPQ : ∀ v, P v + Q v = v) {w : E}
    {g : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => φ (P w + s • Q w)) (g t) t)
    (hg : ContinuousOn g (Icc 0 1)) :
    φ w - φ (P w) = ∫ t in (0 : ℝ)..1, g t := by
  have hg' : ContinuousOn g (uIcc 0 1) := by rwa [uIcc_of_le zero_le_one]
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => φ (P w + t • Q w)) (f' := g)
    (fun t ht => by
      rw [uIcc_of_le zero_le_one] at ht
      exact hφ t ht) hg'.intervalIntegrable
  rw [h]
  simp only [one_smul, zero_smul, add_zero]
  rw [hPQ]

end

end Finsler.SegmentAverage
